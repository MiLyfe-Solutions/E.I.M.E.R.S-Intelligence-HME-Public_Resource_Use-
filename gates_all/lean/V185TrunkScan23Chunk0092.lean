import V185TrunkScan23Chunk0091

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_545717 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 3, 6]
def baseStart_545717 : Nat := 118140960795 + 545717 * 2 ^ 59
def prefixEnd_545717 : Nat := 4983230072969 + 3 ^ 40 * 545717 * 2
def baseEnd_545717 : Nat := 93405040776582204475933

theorem tailTrace_545717 : CollatzResearch.WordTrace tailWord_545717 prefixEnd_545717 93405040776582204475933 := by
  unfold tailWord_545717
  simp only [CollatzResearch.WordTrace]
  refine ⟨19903934163967984888595405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13269289442645323259063603 19903934163967984888595405)
  ·
    refine ⟨7463975311487994333223277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19903934163967984888595405 7463975311487994333223277)
    ·
      refine ⟨2798990741807997874958729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7463975311487994333223277 2798990741807997874958729)
      ·
        refine ⟨2099243056355998406219047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2798990741807997874958729 2099243056355998406219047)
        ·
          refine ⟨3148864584533997609328571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2099243056355998406219047 3148864584533997609328571)
          ·
            refine ⟨4723296876800996413992857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3148864584533997609328571 4723296876800996413992857)
            ·
              refine ⟨3542472657600747310494643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4723296876800996413992857 3542472657600747310494643)
              ·
                refine ⟨5313708986401120965741965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3542472657600747310494643 5313708986401120965741965)
                ·
                  refine ⟨1992640869900420362153237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5313708986401120965741965 1992640869900420362153237)
                  ·
                    refine ⟨93405040776582204475933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1992640869900420362153237 93405040776582204475933)
                    ·
                      rfl

theorem cell23_545717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_545717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545717 prefixEnd_545717 := by exact prefixLift 545717
  have htrace : WordTrace (prefixWord ++ tailWord_545717) baseStart_545717 baseEnd_545717 := by
    simpa [prefixWord, tailWord_545717, baseEnd_545717] using wordTrace_append hprefix tailTrace_545717
  have hstable : (prefixWord ++ tailWord_545717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545717).length < 2 ^ (prefixWord ++ tailWord_545717).sum := by decide
  have hdescent : baseEnd_545717 < baseStart_545717 := by decide
  rcases family_descends (prefixWord ++ tailWord_545717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545778 : List Nat := [3, 2, 1, 5, 1, 2, 1, 1, 1, 1, 5]
def baseStart_545778 : Nat := 118140960795 + 545778 * 2 ^ 59
def prefixEnd_545778 : Nat := 4983230072969 + 3 ^ 40 * 545778 * 2
def baseEnd_545778 : Nat := 280246444649670874765019

theorem tailTrace_545778 : CollatzResearch.WordTrace tailWord_545778 prefixEnd_545778 280246444649670874765019 := by
  unfold tailWord_545778
  simp only [CollatzResearch.WordTrace]
  refine ⟨4976539754186748076641497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13270772677831328204377325 4976539754186748076641497)
  ·
    refine ⟨3732404815640061057481123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4976539754186748076641497 3732404815640061057481123)
    ·
      refine ⟨5598607223460091586221685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3732404815640061057481123 5598607223460091586221685)
      ·
        refine ⟨524869427199383586208283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5598607223460091586221685 524869427199383586208283)
        ·
          refine ⟨787304140799075379312425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 524869427199383586208283 787304140799075379312425)
          ·
            refine ⟨590478105599306534484319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 787304140799075379312425 590478105599306534484319)
            ·
              refine ⟨885717158398959801726479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 590478105599306534484319 885717158398959801726479)
              ·
                refine ⟨1328575737598439702589719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 885717158398959801726479 1328575737598439702589719)
                ·
                  refine ⟨1992863606397659553884579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1328575737598439702589719 1992863606397659553884579)
                  ·
                    refine ⟨2989295409596489330826869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1992863606397659553884579 2989295409596489330826869)
                    ·
                      refine ⟨280246444649670874765019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2989295409596489330826869 280246444649670874765019)
                      ·
                        rfl

theorem cell23_545778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_545778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545778 prefixEnd_545778 := by exact prefixLift 545778
  have htrace : WordTrace (prefixWord ++ tailWord_545778) baseStart_545778 baseEnd_545778 := by
    simpa [prefixWord, tailWord_545778, baseEnd_545778] using wordTrace_append hprefix tailTrace_545778
  have hstable : (prefixWord ++ tailWord_545778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545778).length < 2 ^ (prefixWord ++ tailWord_545778).sum := by decide
  have hdescent : baseEnd_545778 < baseStart_545778 := by decide
  rcases family_descends (prefixWord ++ tailWord_545778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545781 : List Nat := [1, 3, 5, 2, 2, 10]
def baseStart_545781 : Nat := 118140960795 + 545781 * 2 ^ 59
def prefixEnd_545781 : Nat := 4983230072969 + 3 ^ 40 * 545781 * 2
def baseEnd_545781 : Nat := 1153283889265985033035

theorem tailTrace_545781 : CollatzResearch.WordTrace tailWord_545781 prefixEnd_545781 1153283889265985033035 := by
  unfold tailWord_545781
  simp only [CollatzResearch.WordTrace]
  refine ⟨19906268435736123818925197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13270845623824082545950131 19906268435736123818925197)
  ·
    refine ⟨7464850663401046432096949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19906268435736123818925197 7464850663401046432096949)
    ·
      refine ⟨699829749693848103009089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7464850663401046432096949 699829749693848103009089)
      ·
        refine ⟨524872312270386077256817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 699829749693848103009089 524872312270386077256817)
        ·
          refine ⟨393654234202789557942613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 524872312270386077256817 393654234202789557942613)
          ·
            refine ⟨1153283889265985033035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 393654234202789557942613 1153283889265985033035)
            ·
              rfl

theorem cell23_545781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 10].length) (baseStart_545781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545781 prefixEnd_545781 := by exact prefixLift 545781
  have htrace : WordTrace (prefixWord ++ tailWord_545781) baseStart_545781 baseEnd_545781 := by
    simpa [prefixWord, tailWord_545781, baseEnd_545781] using wordTrace_append hprefix tailTrace_545781
  have hstable : (prefixWord ++ tailWord_545781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545781).length < 2 ^ (prefixWord ++ tailWord_545781).sum := by decide
  have hdescent : baseEnd_545781 < baseStart_545781 := by decide
  rcases family_descends (prefixWord ++ tailWord_545781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545797 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 1, 5, 4]
def baseStart_545797 : Nat := 118140960795 + 545797 * 2 ^ 59
def prefixEnd_545797 : Nat := 4983230072969 + 3 ^ 40 * 545797 * 2
def baseEnd_545797 : Nat := 280256200782106300427431

theorem tailTrace_545797 : CollatzResearch.WordTrace tailWord_545797 prefixEnd_545797 280256200782106300427431 := by
  unfold tailWord_545797
  simp only [CollatzResearch.WordTrace]
  refine ⟨19906852003678158551507645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13271234669118772367671763 19906852003678158551507645)
  ·
    refine ⟨7465069501379309456815367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19906852003678158551507645 7465069501379309456815367)
    ·
      refine ⟨11197604252068964185223051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7465069501379309456815367 11197604252068964185223051)
      ·
        refine ⟨16796406378103446277834577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11197604252068964185223051 16796406378103446277834577)
        ·
          refine ⟨12597304783577584708375933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16796406378103446277834577 12597304783577584708375933)
          ·
            refine ⟨4723989293841594265640975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12597304783577584708375933 4723989293841594265640975)
            ·
              refine ⟨7085983940762391398461463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4723989293841594265640975 7085983940762391398461463)
              ·
                refine ⟨10628975911143587097692195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7085983940762391398461463 10628975911143587097692195)
                ·
                  refine ⟨15943463866715380646538293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10628975911143587097692195 15943463866715380646538293)
                  ·
                    refine ⟨1494699737504566935612965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15943463866715380646538293 1494699737504566935612965)
                    ·
                      refine ⟨280256200782106300427431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1494699737504566935612965 280256200782106300427431)
                      ·
                        rfl

theorem cell23_545797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_545797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545797 prefixEnd_545797 := by exact prefixLift 545797
  have htrace : WordTrace (prefixWord ++ tailWord_545797) baseStart_545797 baseEnd_545797 := by
    simpa [prefixWord, tailWord_545797, baseEnd_545797] using wordTrace_append hprefix tailTrace_545797
  have hstable : (prefixWord ++ tailWord_545797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545797).length < 2 ^ (prefixWord ++ tailWord_545797).sum := by decide
  have hdescent : baseEnd_545797 < baseStart_545797 := by decide
  rcases family_descends (prefixWord ++ tailWord_545797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545817 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 4, 1, 5]
def baseStart_545817 : Nat := 118140960795 + 545817 * 2 ^ 59
def prefixEnd_545817 : Nat := 4983230072969 + 3 ^ 40 * 545817 * 2
def baseEnd_545817 : Nat := 280266470395196222177339

theorem tailTrace_545817 : CollatzResearch.WordTrace tailWord_545817 prefixEnd_545817 280266470395196222177339 := by
  unfold tailWord_545817
  simp only [CollatzResearch.WordTrace]
  refine ⟨19907581463605701967235705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13271720975737134644823803 19907581463605701967235705)
  ·
    refine ⟨14930686097704276475426779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19907581463605701967235705 14930686097704276475426779)
    ·
      refine ⟨22396029146556414713140169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14930686097704276475426779 22396029146556414713140169)
      ·
        refine ⟨16797021859917311034855127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22396029146556414713140169 16797021859917311034855127)
        ·
          refine ⟨25195532789875966552282691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16797021859917311034855127 25195532789875966552282691)
          ·
            refine ⟨37793299184813949828424037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25195532789875966552282691 37793299184813949828424037)
            ·
              refine ⟨7086243597152615592829507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37793299184813949828424037 7086243597152615592829507)
              ·
                refine ⟨10629365395728923389244261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7086243597152615592829507 10629365395728923389244261)
                ·
                  refine ⟨1993006011699173135483299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10629365395728923389244261 1993006011699173135483299)
                  ·
                    refine ⟨2989509017548759703224949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1993006011699173135483299 2989509017548759703224949)
                    ·
                      refine ⟨280266470395196222177339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2989509017548759703224949 280266470395196222177339)
                      ·
                        rfl

theorem cell23_545817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_545817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545817 prefixEnd_545817 := by exact prefixLift 545817
  have htrace : WordTrace (prefixWord ++ tailWord_545817) baseStart_545817 baseEnd_545817 := by
    simpa [prefixWord, tailWord_545817, baseEnd_545817] using wordTrace_append hprefix tailTrace_545817
  have hstable : (prefixWord ++ tailWord_545817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545817).length < 2 ^ (prefixWord ++ tailWord_545817).sum := by decide
  have hdescent : baseEnd_545817 < baseStart_545817 := by decide
  rcases family_descends (prefixWord ++ tailWord_545817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545848 : List Nat := [2, 1, 2, 1, 5, 2, 1, 1, 4, 2, 2]
def baseStart_545848 : Nat := 118140960795 + 545848 * 2 ^ 59
def prefixEnd_545848 : Nat := 4983230072969 + 3 ^ 40 * 545848 * 2
def baseEnd_545848 : Nat := 280282388295485600889697

theorem tailTrace_545848 : CollatzResearch.WordTrace tailWord_545848 prefixEnd_545848 280282388295485600889697 := by
  unfold tailWord_545848
  simp only [CollatzResearch.WordTrace]
  refine ⟨9954356063246697130807099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13272474750995596174409465 9954356063246697130807099)
  ·
    refine ⟨14931534094870045696210649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9954356063246697130807099 14931534094870045696210649)
    ·
      refine ⟨11198650571152534272157987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14931534094870045696210649 11198650571152534272157987)
      ·
        refine ⟨16797975856728801408236981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11198650571152534272157987 16797975856728801408236981)
        ·
          refine ⟨1574810236568325132022217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16797975856728801408236981 1574810236568325132022217)
          ·
            refine ⟨1181107677426243849016663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1574810236568325132022217 1181107677426243849016663)
            ·
              refine ⟨1771661516139365773524995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1181107677426243849016663 1771661516139365773524995)
              ·
                refine ⟨2657492274209048660287493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1771661516139365773524995 2657492274209048660287493)
                ·
                  refine ⟨498279801414196623803905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2657492274209048660287493 498279801414196623803905)
                  ·
                    refine ⟨373709851060647467852929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 498279801414196623803905 373709851060647467852929)
                    ·
                      refine ⟨280282388295485600889697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 373709851060647467852929 280282388295485600889697)
                      ·
                        rfl

theorem cell23_545848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 4, 2, 2].length) (baseStart_545848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545848 prefixEnd_545848 := by exact prefixLift 545848
  have htrace : WordTrace (prefixWord ++ tailWord_545848) baseStart_545848 baseEnd_545848 := by
    simpa [prefixWord, tailWord_545848, baseEnd_545848] using wordTrace_append hprefix tailTrace_545848
  have hstable : (prefixWord ++ tailWord_545848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545848).length < 2 ^ (prefixWord ++ tailWord_545848).sum := by decide
  have hdescent : baseEnd_545848 < baseStart_545848 := by decide
  rcases family_descends (prefixWord ++ tailWord_545848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545864 : List Nat := [2, 1, 3, 1, 1, 1, 3, 3, 2, 3, 3]
def baseStart_545864 : Nat := 118140960795 + 545864 * 2 ^ 59
def prefixEnd_545864 : Nat := 4983230072969 + 3 ^ 40 * 545864 * 2
def baseEnd_545864 : Nat := 280290603985957538289623

theorem tailTrace_545864 : CollatzResearch.WordTrace tailWord_545864 prefixEnd_545864 280290603985957538289623 := by
  unfold tailWord_545864
  simp only [CollatzResearch.WordTrace]
  refine ⟨9954647847217714497098323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13272863796290285996131097 9954647847217714497098323)
  ·
    refine ⟨14931971770826571745647485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9954647847217714497098323 14931971770826571745647485)
    ·
      refine ⟨5599489414059964404617807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14931971770826571745647485 5599489414059964404617807)
      ·
        refine ⟨8399234121089946606926711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5599489414059964404617807 8399234121089946606926711)
        ·
          refine ⟨12598851181634919910390067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8399234121089946606926711 12598851181634919910390067)
          ·
            refine ⟨18898276772452379865585101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12598851181634919910390067 18898276772452379865585101)
            ·
              refine ⟨7086853789669642449594413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18898276772452379865585101 7086853789669642449594413)
              ·
                refine ⟨2657570171126115918597905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7086853789669642449594413 2657570171126115918597905)
                ·
                  refine ⟨1993177628344586938948429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2657570171126115918597905 1993177628344586938948429)
                  ·
                    refine ⟨747441610629220102105661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1993177628344586938948429 747441610629220102105661)
                    ·
                      refine ⟨280290603985957538289623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 747441610629220102105661 280290603985957538289623)
                      ·
                        rfl

theorem cell23_545864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_545864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545864 prefixEnd_545864 := by exact prefixLift 545864
  have htrace : WordTrace (prefixWord ++ tailWord_545864) baseStart_545864 baseEnd_545864 := by
    simpa [prefixWord, tailWord_545864, baseEnd_545864] using wordTrace_append hprefix tailTrace_545864
  have hstable : (prefixWord ++ tailWord_545864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545864).length < 2 ^ (prefixWord ++ tailWord_545864).sum := by decide
  have hdescent : baseEnd_545864 < baseStart_545864 := by decide
  rcases family_descends (prefixWord ++ tailWord_545864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545884 : List Nat := [2, 2, 4, 1, 1, 1, 1, 3, 1, 7]
def baseStart_545884 : Nat := 118140960795 + 545884 * 2 ^ 59
def prefixEnd_545884 : Nat := 4983230072969 + 3 ^ 40 * 545884 * 2
def baseEnd_545884 : Nat := 93433624533015820013177

theorem tailTrace_545884 : CollatzResearch.WordTrace tailWord_545884 prefixEnd_545884 93433624533015820013177 := by
  unfold tailWord_545884
  simp only [CollatzResearch.WordTrace]
  refine ⟨9955012577181486204962353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13273350102908648273283137 9955012577181486204962353)
  ·
    refine ⟨7466259432886114653721765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9955012577181486204962353 7466259432886114653721765)
    ·
      refine ⟨1399923643666146497572831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7466259432886114653721765 1399923643666146497572831)
      ·
        refine ⟨2099885465499219746359247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1399923643666146497572831 2099885465499219746359247)
        ·
          refine ⟨3149828198248829619538871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2099885465499219746359247 3149828198248829619538871)
          ·
            refine ⟨4724742297373244429308307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3149828198248829619538871 4724742297373244429308307)
            ·
              refine ⟨7087113446059866643962461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4724742297373244429308307 7087113446059866643962461)
              ·
                refine ⟨2657667542272449991485923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7087113446059866643962461 2657667542272449991485923)
                ·
                  refine ⟨3986501313408674987228885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2657667542272449991485923 3986501313408674987228885)
                  ·
                    refine ⟨93433624533015820013177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3986501313408674987228885 93433624533015820013177)
                    ·
                      rfl

theorem cell23_545884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_545884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545884 prefixEnd_545884 := by exact prefixLift 545884
  have htrace : WordTrace (prefixWord ++ tailWord_545884) baseStart_545884 baseEnd_545884 := by
    simpa [prefixWord, tailWord_545884, baseEnd_545884] using wordTrace_append hprefix tailTrace_545884
  have hstable : (prefixWord ++ tailWord_545884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545884).length < 2 ^ (prefixWord ++ tailWord_545884).sum := by decide
  have hdescent : baseEnd_545884 < baseStart_545884 := by decide
  rcases family_descends (prefixWord ++ tailWord_545884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545901 : List Nat := [1, 5, 1, 1, 2, 3, 1, 2, 2, 5]
def baseStart_545901 : Nat := 118140960795 + 545901 * 2 ^ 59
def prefixEnd_545901 : Nat := 4983230072969 + 3 ^ 40 * 545901 * 2
def baseEnd_545901 : Nat := 93436534256724631175651

theorem tailTrace_545901 : CollatzResearch.WordTrace tailWord_545901 prefixEnd_545901 93436534256724631175651 := by
  unfold tailWord_545901
  simp only [CollatzResearch.WordTrace]
  refine ⟨19910645195301384313293557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13273763463534256208862371 19910645195301384313293557)
  ·
    refine ⟨1866622987059504779371271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19910645195301384313293557 1866622987059504779371271)
    ·
      refine ⟨2799934480589257169056907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1866622987059504779371271 2799934480589257169056907)
      ·
        refine ⟨4199901720883885753585361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2799934480589257169056907 4199901720883885753585361)
        ·
          refine ⟨3149926290662914315189021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4199901720883885753585361 3149926290662914315189021)
          ·
            refine ⟨1181222358998592868195883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3149926290662914315189021 1181222358998592868195883)
            ·
              refine ⟨1771833538497889302293825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1181222358998592868195883 1771833538497889302293825)
              ·
                refine ⟨1328875153873416976720369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1771833538497889302293825 1328875153873416976720369)
                ·
                  refine ⟨996656365405062732540277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1328875153873416976720369 996656365405062732540277)
                  ·
                    refine ⟨93436534256724631175651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 996656365405062732540277 93436534256724631175651)
                    ·
                      rfl

theorem cell23_545901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_545901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545901 prefixEnd_545901 := by exact prefixLift 545901
  have htrace : WordTrace (prefixWord ++ tailWord_545901) baseStart_545901 baseEnd_545901 := by
    simpa [prefixWord, tailWord_545901, baseEnd_545901] using wordTrace_append hprefix tailTrace_545901
  have hstable : (prefixWord ++ tailWord_545901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545901).length < 2 ^ (prefixWord ++ tailWord_545901).sum := by decide
  have hdescent : baseEnd_545901 < baseStart_545901 := by decide
  rcases family_descends (prefixWord ++ tailWord_545901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545938 : List Nat := [3, 2, 3, 1, 1, 3, 2, 1, 2, 1, 4]
def baseStart_545938 : Nat := 118140960795 + 545938 * 2 ^ 59
def prefixEnd_545938 : Nat := 4983230072969 + 3 ^ 40 * 545938 * 2
def baseEnd_545938 : Nat := 280328601554390248764283

theorem tailTrace_545938 : CollatzResearch.WordTrace tailWord_545938 prefixEnd_545938 280328601554390248764283 := by
  unfold tailWord_545938
  simp only [CollatzResearch.WordTrace]
  refine ⟨4977998674041834908097617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13274663130778226421593645 4977998674041834908097617)
  ·
    refine ⟨3733499005531376181073213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4977998674041834908097617 3733499005531376181073213)
    ·
      refine ⟨1400062127074266067902455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3733499005531376181073213 1400062127074266067902455)
      ·
        refine ⟨2100093190611399101853683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1400062127074266067902455 2100093190611399101853683)
        ·
          refine ⟨3150139785917098652780525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2100093190611399101853683 3150139785917098652780525)
          ·
            refine ⟨1181302419718911994792697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3150139785917098652780525 1181302419718911994792697)
            ·
              refine ⟨885976814789183996094523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1181302419718911994792697 885976814789183996094523)
              ·
                refine ⟨1328965222183775994141785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 885976814789183996094523 1328965222183775994141785)
                ·
                  refine ⟨996723916637831995606339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1328965222183775994141785 996723916637831995606339)
                  ·
                    refine ⟨1495085874956747993409509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 996723916637831995606339 1495085874956747993409509)
                    ·
                      refine ⟨280328601554390248764283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1495085874956747993409509 280328601554390248764283)
                      ·
                        rfl

theorem cell23_545938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_545938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_545938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_545938 prefixEnd_545938 := by exact prefixLift 545938
  have htrace : WordTrace (prefixWord ++ tailWord_545938) baseStart_545938 baseEnd_545938 := by
    simpa [prefixWord, tailWord_545938, baseEnd_545938] using wordTrace_append hprefix tailTrace_545938
  have hstable : (prefixWord ++ tailWord_545938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545938).length < 2 ^ (prefixWord ++ tailWord_545938).sum := by decide
  have hdescent : baseEnd_545938 < baseStart_545938 := by decide
  rcases family_descends (prefixWord ++ tailWord_545938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546008 : List Nat := [2, 1, 2, 2, 5, 1, 1, 3, 1, 5]
def baseStart_546008 : Nat := 118140960795 + 546008 * 2 ^ 59
def prefixEnd_546008 : Nat := 4983230072969 + 3 ^ 40 * 546008 * 2
def baseEnd_546008 : Nat := 93454848400068324962987

theorem tailTrace_546008 : CollatzResearch.WordTrace tailWord_546008 prefixEnd_546008 93454848400068324962987 := by
  unfold tailWord_546008
  simp only [CollatzResearch.WordTrace]
  refine ⟨9957273902956870793719339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13276365203942494391625785 9957273902956870793719339)
  ·
    refine ⟨14935910854435306190579009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9957273902956870793719339 14935910854435306190579009)
    ·
      refine ⟨11201933140826479642934257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14935910854435306190579009 11201933140826479642934257)
      ·
        refine ⟨8401449855619859732200693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11201933140826479642934257 8401449855619859732200693)
        ·
          refine ⟨787635923964361849893815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8401449855619859732200693 787635923964361849893815)
          ·
            refine ⟨1181453885946542774840723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 787635923964361849893815 1181453885946542774840723)
            ·
              refine ⟨1772180828919814162261085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1181453885946542774840723 1772180828919814162261085)
              ·
                refine ⟨664567810844930310847907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1772180828919814162261085 664567810844930310847907)
                ·
                  refine ⟨996851716267395466271861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 664567810844930310847907 996851716267395466271861)
                  ·
                    refine ⟨93454848400068324962987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 996851716267395466271861 93454848400068324962987)
                    ·
                      rfl

theorem cell23_546008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 1, 5].length) (baseStart_546008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546008 prefixEnd_546008 := by exact prefixLift 546008
  have htrace : WordTrace (prefixWord ++ tailWord_546008) baseStart_546008 baseEnd_546008 := by
    simpa [prefixWord, tailWord_546008, baseEnd_546008] using wordTrace_append hprefix tailTrace_546008
  have hstable : (prefixWord ++ tailWord_546008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546008).length < 2 ^ (prefixWord ++ tailWord_546008).sum := by decide
  have hdescent : baseEnd_546008 < baseStart_546008 := by decide
  rcases family_descends (prefixWord ++ tailWord_546008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546051 : List Nat := [1, 1, 1, 3, 2, 4, 4, 7]
def baseStart_546051 : Nat := 118140960795 + 546051 * 2 ^ 59
def prefixEnd_546051 : Nat := 4983230072969 + 3 ^ 40 * 546051 * 2
def baseEnd_546051 : Nat := 10384689809938826172269

theorem tailTrace_546051 : CollatzResearch.WordTrace tailWord_546051 prefixEnd_546051 10384689809938826172269 := by
  unfold tailWord_546051
  simp only [CollatzResearch.WordTrace]
  refine ⟨19916116144757959931254007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13277410763171973287502671 19916116144757959931254007)
  ·
    refine ⟨29874174217136939896881011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19916116144757959931254007 29874174217136939896881011)
    ·
      refine ⟨44811261325705409845321517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29874174217136939896881011 44811261325705409845321517)
      ·
        refine ⟨16804222997139528691995569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44811261325705409845321517 16804222997139528691995569)
        ·
          refine ⟨12603167247854646518996677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16804222997139528691995569 12603167247854646518996677)
          ·
            refine ⟨2363093858972746222311877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12603167247854646518996677 2363093858972746222311877)
            ·
              refine ⟨443080098557389916683477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2363093858972746222311877 443080098557389916683477)
              ·
                refine ⟨10384689809938826172269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 443080098557389916683477 10384689809938826172269)
                ·
                  rfl

theorem cell23_546051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 7].length) (baseStart_546051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546051 prefixEnd_546051 := by exact prefixLift 546051
  have htrace : WordTrace (prefixWord ++ tailWord_546051) baseStart_546051 baseEnd_546051 := by
    simpa [prefixWord, tailWord_546051, baseEnd_546051] using wordTrace_append hprefix tailTrace_546051
  have hstable : (prefixWord ++ tailWord_546051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546051).length < 2 ^ (prefixWord ++ tailWord_546051).sum := by decide
  have hdescent : baseEnd_546051 < baseStart_546051 := by decide
  rcases family_descends (prefixWord ++ tailWord_546051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546079 : List Nat := [1, 1, 2, 4, 5, 1, 1, 1, 3, 2, 2]
def baseStart_546079 : Nat := 118140960795 + 546079 * 2 ^ 59
def prefixEnd_546079 : Nat := 4983230072969 + 3 ^ 40 * 546079 * 2
def baseEnd_546079 : Nat := 280401002326674197101135

theorem tailTrace_546079 : CollatzResearch.WordTrace tailWord_546079 prefixEnd_546079 280401002326674197101135 := by
  unfold tailWord_546079
  simp only [CollatzResearch.WordTrace]
  refine ⟨19917137388656520713273291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13278091592437680475515527 19917137388656520713273291)
  ·
    refine ⟨29875706082984781069909937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19917137388656520713273291 29875706082984781069909937)
    ·
      refine ⟨22406779562238585802432453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29875706082984781069909937 22406779562238585802432453)
      ·
        refine ⟨4201271167919734837956085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22406779562238585802432453 4201271167919734837956085)
        ·
          refine ⟨393869171992475141058383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4201271167919734837956085 393869171992475141058383)
          ·
            refine ⟨590803757988712711587575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 393869171992475141058383 590803757988712711587575)
            ·
              refine ⟨886205636983069067381363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 590803757988712711587575 886205636983069067381363)
              ·
                refine ⟨1329308455474603601072045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 886205636983069067381363 1329308455474603601072045)
                ·
                  refine ⟨498490670802976350402017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1329308455474603601072045 498490670802976350402017)
                  ·
                    refine ⟨373868003102232262801513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 498490670802976350402017 373868003102232262801513)
                    ·
                      refine ⟨280401002326674197101135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 373868003102232262801513 280401002326674197101135)
                      ·
                        rfl

theorem cell23_546079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_546079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546079 prefixEnd_546079 := by exact prefixLift 546079
  have htrace : WordTrace (prefixWord ++ tailWord_546079) baseStart_546079 baseEnd_546079 := by
    simpa [prefixWord, tailWord_546079, baseEnd_546079] using wordTrace_append hprefix tailTrace_546079
  have hstable : (prefixWord ++ tailWord_546079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546079).length < 2 ^ (prefixWord ++ tailWord_546079).sum := by decide
  have hdescent : baseEnd_546079 < baseStart_546079 := by decide
  rcases family_descends (prefixWord ++ tailWord_546079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546121 : List Nat := [1, 2, 1, 1, 2, 3, 4, 1, 2, 1, 5]
def baseStart_546121 : Nat := 118140960795 + 546121 * 2 ^ 59
def prefixEnd_546121 : Nat := 4983230072969 + 3 ^ 40 * 546121 * 2
def baseEnd_546121 : Nat := 280422568514163032775941

theorem tailTrace_546121 : CollatzResearch.WordTrace tailWord_546121 prefixEnd_546121 280422568514163032775941 := by
  unfold tailWord_546121
  simp only [CollatzResearch.WordTrace]
  refine ⟨19918669254504361886302217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13279112836336241257534811 19918669254504361886302217)
  ·
    refine ⟨14939001940878271414726663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19918669254504361886302217 14939001940878271414726663)
    ·
      refine ⟨22408502911317407122089995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14939001940878271414726663 22408502911317407122089995)
      ·
        refine ⟨33612754366976110683134993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22408502911317407122089995 33612754366976110683134993)
        ·
          refine ⟨25209565775232083012351245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33612754366976110683134993 25209565775232083012351245)
          ·
            refine ⟨9453587165712031129631717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25209565775232083012351245 9453587165712031129631717)
            ·
              refine ⟨1772547593571005836805947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9453587165712031129631717 1772547593571005836805947)
              ·
                refine ⟨2658821390356508755208921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1772547593571005836805947 2658821390356508755208921)
                ·
                  refine ⟨1994116042767381566406691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2658821390356508755208921 1994116042767381566406691)
                  ·
                    refine ⟨2991174064151072349610037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1994116042767381566406691 2991174064151072349610037)
                    ·
                      refine ⟨280422568514163032775941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2991174064151072349610037 280422568514163032775941)
                      ·
                        rfl

theorem cell23_546121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 1, 5].length) (baseStart_546121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546121 prefixEnd_546121 := by exact prefixLift 546121
  have htrace : WordTrace (prefixWord ++ tailWord_546121) baseStart_546121 baseEnd_546121 := by
    simpa [prefixWord, tailWord_546121, baseEnd_546121] using wordTrace_append hprefix tailTrace_546121
  have hstable : (prefixWord ++ tailWord_546121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546121).length < 2 ^ (prefixWord ++ tailWord_546121).sum := by decide
  have hdescent : baseEnd_546121 < baseStart_546121 := by decide
  rcases family_descends (prefixWord ++ tailWord_546121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546131 : List Nat := [1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 4]
def baseStart_546131 : Nat := 118140960795 + 546131 * 2 ^ 59
def prefixEnd_546131 : Nat := 4983230072969 + 3 ^ 40 * 546131 * 2
def baseEnd_546131 : Nat := 280427703320707993650895

theorem tailTrace_546131 : CollatzResearch.WordTrace tailWord_546131 prefixEnd_546131 280427703320707993650895 := by
  unfold tailWord_546131
  simp only [CollatzResearch.WordTrace]
  refine ⟨19919033984468133594166247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13279355989645422396110831 19919033984468133594166247)
  ·
    refine ⟨29878550976702200391249371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19919033984468133594166247 29878550976702200391249371)
    ·
      refine ⟨44817826465053300586874057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29878550976702200391249371 44817826465053300586874057)
      ·
        refine ⟨33613369848789975440155543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44817826465053300586874057 33613369848789975440155543)
        ·
          refine ⟨50420054773184963160233315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33613369848789975440155543 50420054773184963160233315)
          ·
            refine ⟨75630082159777444740349973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50420054773184963160233315 75630082159777444740349973)
            ·
              refine ⟨3545160101239567722203905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75630082159777444740349973 3545160101239567722203905)
              ·
                refine ⟨2658870075929675791652929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3545160101239567722203905 2658870075929675791652929)
                ·
                  refine ⟨1994152556947256843739697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2658870075929675791652929 1994152556947256843739697)
                  ·
                    refine ⟨1495614417710442632804773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1994152556947256843739697 1495614417710442632804773)
                    ·
                      refine ⟨280427703320707993650895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1495614417710442632804773 280427703320707993650895)
                      ·
                        rfl

theorem cell23_546131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 4].length) (baseStart_546131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546131 prefixEnd_546131 := by exact prefixLift 546131
  have htrace : WordTrace (prefixWord ++ tailWord_546131) baseStart_546131 baseEnd_546131 := by
    simpa [prefixWord, tailWord_546131, baseEnd_546131] using wordTrace_append hprefix tailTrace_546131
  have hstable : (prefixWord ++ tailWord_546131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546131).length < 2 ^ (prefixWord ++ tailWord_546131).sum := by decide
  have hdescent : baseEnd_546131 < baseStart_546131 := by decide
  rcases family_descends (prefixWord ++ tailWord_546131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546148 : List Nat := [2, 3, 1, 1, 3, 3, 1, 1, 2, 2, 4]
def baseStart_546148 : Nat := 118140960795 + 546148 * 2 ^ 59
def prefixEnd_546148 : Nat := 4983230072969 + 3 ^ 40 * 546148 * 2
def baseEnd_546148 : Nat := 280436432491834427138317

theorem tailTrace_546148 : CollatzResearch.WordTrace tailWord_546148 prefixEnd_546148 280436432491834427138317 := by
  unfold tailWord_546148
  simp only [CollatzResearch.WordTrace]
  refine ⟨9959827012703272748767549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13279769350271030331690065 9959827012703272748767549)
  ·
    refine ⟨3734935129763727280787831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9959827012703272748767549 3734935129763727280787831)
    ·
      refine ⟨5602402694645590921181747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3734935129763727280787831 5602402694645590921181747)
      ·
        refine ⟨8403604041968386381772621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5602402694645590921181747 8403604041968386381772621)
        ·
          refine ⟨3151351515738144893164733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8403604041968386381772621 3151351515738144893164733)
          ·
            refine ⟨1181756818401804334936775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3151351515738144893164733 1181756818401804334936775)
            ·
              refine ⟨1772635227602706502405163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1181756818401804334936775 1772635227602706502405163)
              ·
                refine ⟨2658952841404059753607745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1772635227602706502405163 2658952841404059753607745)
                ·
                  refine ⟨1994214631053044815205809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2658952841404059753607745 1994214631053044815205809)
                  ·
                    refine ⟨1495660973289783611404357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1994214631053044815205809 1495660973289783611404357)
                    ·
                      refine ⟨280436432491834427138317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1495660973289783611404357 280436432491834427138317)
                      ·
                        rfl

theorem cell23_546148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_546148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546148 prefixEnd_546148 := by exact prefixLift 546148
  have htrace : WordTrace (prefixWord ++ tailWord_546148) baseStart_546148 baseEnd_546148 := by
    simpa [prefixWord, tailWord_546148, baseEnd_546148] using wordTrace_append hprefix tailTrace_546148
  have hstable : (prefixWord ++ tailWord_546148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546148).length < 2 ^ (prefixWord ++ tailWord_546148).sum := by decide
  have hdescent : baseEnd_546148 < baseStart_546148 := by decide
  rcases family_descends (prefixWord ++ tailWord_546148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546152 : List Nat := [2, 1, 4, 2, 3, 1, 2, 1, 1, 4, 2]
def baseStart_546152 : Nat := 118140960795 + 546152 * 2 ^ 59
def prefixEnd_546152 : Nat := 4983230072969 + 3 ^ 40 * 546152 * 2
def baseEnd_546152 : Nat := 280438486414452411488299

theorem tailTrace_546152 : CollatzResearch.WordTrace tailWord_546152 prefixEnd_546152 280438486414452411488299 := by
  unfold tailWord_546152
  simp only [CollatzResearch.WordTrace]
  refine ⟨9959899958696027090340355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13279866611594702787120473 9959899958696027090340355)
  ·
    refine ⟨14939849938044040635510533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9959899958696027090340355 14939849938044040635510533)
    ·
      refine ⟨2801221863383257619158225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14939849938044040635510533 2801221863383257619158225)
      ·
        refine ⟨2100916397537443214368669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2801221863383257619158225 2100916397537443214368669)
        ·
          refine ⟨787843649076541205388251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2100916397537443214368669 787843649076541205388251)
          ·
            refine ⟨1181765473614811808082377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 787843649076541205388251 1181765473614811808082377)
            ·
              refine ⟨886324105211108856061783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1181765473614811808082377 886324105211108856061783)
              ·
                refine ⟨1329486157816663284092675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 886324105211108856061783 1329486157816663284092675)
                ·
                  refine ⟨1994229236724994926139013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1329486157816663284092675 1994229236724994926139013)
                  ·
                    refine ⟨373917981885936548651065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1994229236724994926139013 373917981885936548651065)
                    ·
                      refine ⟨280438486414452411488299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 373917981885936548651065 280438486414452411488299)
                      ·
                        rfl

theorem cell23_546152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_546152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546152 prefixEnd_546152 := by exact prefixLift 546152
  have htrace : WordTrace (prefixWord ++ tailWord_546152) baseStart_546152 baseEnd_546152 := by
    simpa [prefixWord, tailWord_546152, baseEnd_546152] using wordTrace_append hprefix tailTrace_546152
  have hstable : (prefixWord ++ tailWord_546152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546152).length < 2 ^ (prefixWord ++ tailWord_546152).sum := by decide
  have hdescent : baseEnd_546152 < baseStart_546152 := by decide
  rcases family_descends (prefixWord ++ tailWord_546152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546171 : List Nat := [1, 1, 1, 1, 1, 6, 3, 1, 1, 7]
def baseStart_546171 : Nat := 118140960795 + 546171 * 2 ^ 59
def prefixEnd_546171 : Nat := 4983230072969 + 3 ^ 40 * 546171 * 2
def baseEnd_546171 : Nat := 93482747515629279050237

theorem tailTrace_546171 : CollatzResearch.WordTrace tailWord_546171 prefixEnd_546171 93482747515629279050237 := by
  unfold tailWord_546171
  simp only [CollatzResearch.WordTrace]
  refine ⟨19920492904323220425622367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13280328602882146950414911 19920492904323220425622367)
  ·
    refine ⟨29880739356484830638433551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19920492904323220425622367 29880739356484830638433551)
    ·
      refine ⟨44821109034727245957650327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29880739356484830638433551 44821109034727245957650327)
      ·
        refine ⟨67231663552090868936475491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44821109034727245957650327 67231663552090868936475491)
        ·
          refine ⟨100847495328136303404713237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67231663552090868936475491 100847495328136303404713237)
          ·
            refine ⟨4727226343506389222095933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 100847495328136303404713237 4727226343506389222095933)
            ·
              refine ⟨1772709878814895958285975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4727226343506389222095933 1772709878814895958285975)
              ·
                refine ⟨2659064818222343937428963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1772709878814895958285975 2659064818222343937428963)
                ·
                  refine ⟨3988597227333515906143445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2659064818222343937428963 3988597227333515906143445)
                  ·
                    refine ⟨93482747515629279050237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3988597227333515906143445 93482747515629279050237)
                    ·
                      rfl

theorem cell23_546171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 7].length) (baseStart_546171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546171 prefixEnd_546171 := by exact prefixLift 546171
  have htrace : WordTrace (prefixWord ++ tailWord_546171) baseStart_546171 baseEnd_546171 := by
    simpa [prefixWord, tailWord_546171, baseEnd_546171] using wordTrace_append hprefix tailTrace_546171
  have hstable : (prefixWord ++ tailWord_546171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546171).length < 2 ^ (prefixWord ++ tailWord_546171).sum := by decide
  have hdescent : baseEnd_546171 < baseStart_546171 := by decide
  rcases family_descends (prefixWord ++ tailWord_546171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546181 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 3, 2, 5]
def baseStart_546181 : Nat := 118140960795 + 546181 * 2 ^ 59
def prefixEnd_546181 : Nat := 4983230072969 + 3 ^ 40 * 546181 * 2
def baseEnd_546181 : Nat := 280453377353432798025665

theorem tailTrace_546181 : CollatzResearch.WordTrace tailWord_546181 prefixEnd_546181 280453377353432798025665 := by
  unfold tailWord_546181
  simp only [CollatzResearch.WordTrace]
  refine ⟨19920857634286992133486397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13280571756191328088990931 19920857634286992133486397)
  ·
    refine ⟨7470321612857622050057399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19920857634286992133486397 7470321612857622050057399)
    ·
      refine ⟨11205482419286433075086099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7470321612857622050057399 11205482419286433075086099)
      ·
        refine ⟨16808223628929649612629149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11205482419286433075086099 16808223628929649612629149)
        ·
          refine ⟨6303083860848618604735931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16808223628929649612629149 6303083860848618604735931)
          ·
            refine ⟨9454625791272927907103897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6303083860848618604735931 9454625791272927907103897)
            ·
              refine ⟨7090969343454695930327923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9454625791272927907103897 7090969343454695930327923)
              ·
                refine ⟨10636454015182043895491885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7090969343454695930327923 10636454015182043895491885)
                ·
                  refine ⟨3988670255693266460809457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10636454015182043895491885 3988670255693266460809457)
                  ·
                    refine ⟨2991502691769949845607093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3988670255693266460809457 2991502691769949845607093)
                    ·
                      refine ⟨280453377353432798025665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2991502691769949845607093 280453377353432798025665)
                      ·
                        rfl

theorem cell23_546181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_546181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546181 prefixEnd_546181 := by exact prefixLift 546181
  have htrace : WordTrace (prefixWord ++ tailWord_546181) baseStart_546181 baseEnd_546181 := by
    simpa [prefixWord, tailWord_546181, baseEnd_546181] using wordTrace_append hprefix tailTrace_546181
  have hstable : (prefixWord ++ tailWord_546181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546181).length < 2 ^ (prefixWord ++ tailWord_546181).sum := by decide
  have hdescent : baseEnd_546181 < baseStart_546181 := by decide
  rcases family_descends (prefixWord ++ tailWord_546181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546231 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 10]
def baseStart_546231 : Nat := 118140960795 + 546231 * 2 ^ 59
def prefixEnd_546231 : Nat := 4983230072969 + 3 ^ 40 * 546231 * 2
def baseEnd_546231 : Nat := 31164339042906400266715

theorem tailTrace_546231 : CollatzResearch.WordTrace tailWord_546231 prefixEnd_546231 31164339042906400266715 := by
  unfold tailWord_546231
  simp only [CollatzResearch.WordTrace]
  refine ⟨19922681284105850672806547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13281787522737233781871031 19922681284105850672806547)
  ·
    refine ⟨29884021926158776009209821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19922681284105850672806547 29884021926158776009209821)
    ·
      refine ⟨11206508222309541003453683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29884021926158776009209821 11206508222309541003453683)
      ·
        refine ⟨16809762333464311505180525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11206508222309541003453683 16809762333464311505180525)
        ·
          refine ⟨6303660875049116814442697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16809762333464311505180525 6303660875049116814442697)
          ·
            refine ⟨4727745656286837610832023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6303660875049116814442697 4727745656286837610832023)
            ·
              refine ⟨7091618484430256416248035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4727745656286837610832023 7091618484430256416248035)
              ·
                refine ⟨10637427726645384624372053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7091618484430256416248035 10637427726645384624372053)
                ·
                  refine ⟨31164339042906400266715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 10637427726645384624372053 31164339042906400266715)
                  ·
                    rfl

theorem cell23_546231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 10].length) (baseStart_546231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546231 prefixEnd_546231 := by exact prefixLift 546231
  have htrace : WordTrace (prefixWord ++ tailWord_546231) baseStart_546231 baseEnd_546231 := by
    simpa [prefixWord, tailWord_546231, baseEnd_546231] using wordTrace_append hprefix tailTrace_546231
  have hstable : (prefixWord ++ tailWord_546231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546231).length < 2 ^ (prefixWord ++ tailWord_546231).sum := by decide
  have hdescent : baseEnd_546231 < baseStart_546231 := by decide
  rcases family_descends (prefixWord ++ tailWord_546231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546248 : List Nat := [2, 1, 3, 1, 3, 1, 2, 4, 6]
def baseStart_546248 : Nat := 118140960795 + 546248 * 2 ^ 59
def prefixEnd_546248 : Nat := 4983230072969 + 3 ^ 40 * 546248 * 2
def baseEnd_546248 : Nat := 31165308950809337320873

theorem tailTrace_546248 : CollatzResearch.WordTrace tailWord_546248 prefixEnd_546248 31165308950809337320873 := by
  unfold tailWord_546248
  simp only [CollatzResearch.WordTrace]
  refine ⟨9961650662522131288087699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13282200883362841717450265 9961650662522131288087699)
  ·
    refine ⟨14942475993783196932131549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9961650662522131288087699 14942475993783196932131549)
    ·
      refine ⟨5603428497668698849549331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14942475993783196932131549 5603428497668698849549331)
      ·
        refine ⟨8405142746503048274323997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5603428497668698849549331 8405142746503048274323997)
        ·
          refine ⟨3151928529938643102871499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8405142746503048274323997 3151928529938643102871499)
          ·
            refine ⟨4727892794907964654307249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3151928529938643102871499 4727892794907964654307249)
            ·
              refine ⟨3545919596180973490730437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4727892794907964654307249 3545919596180973490730437)
              ·
                refine ⟨664859924283932529511957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3545919596180973490730437 664859924283932529511957)
                ·
                  refine ⟨31165308950809337320873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 664859924283932529511957 31165308950809337320873)
                  ·
                    rfl

theorem cell23_546248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 6].length) (baseStart_546248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546248 prefixEnd_546248 := by exact prefixLift 546248
  have htrace : WordTrace (prefixWord ++ tailWord_546248) baseStart_546248 baseEnd_546248 := by
    simpa [prefixWord, tailWord_546248, baseEnd_546248] using wordTrace_append hprefix tailTrace_546248
  have hstable : (prefixWord ++ tailWord_546248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546248).length < 2 ^ (prefixWord ++ tailWord_546248).sum := by decide
  have hdescent : baseEnd_546248 < baseStart_546248 := by decide
  rcases family_descends (prefixWord ++ tailWord_546248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546251 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 8]
def baseStart_546251 : Nat := 118140960795 + 546251 * 2 ^ 59
def prefixEnd_546251 : Nat := 4983230072969 + 3 ^ 40 * 546251 * 2
def baseEnd_546251 : Nat := 280489320999247524150343

theorem tailTrace_546251 : CollatzResearch.WordTrace tailWord_546251 prefixEnd_546251 280489320999247524150343 := by
  unfold tailWord_546251
  simp only [CollatzResearch.WordTrace]
  refine ⟨19923410744033394088534607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13282273829355596059023071 19923410744033394088534607)
  ·
    refine ⟨29885116116050091132801911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19923410744033394088534607 29885116116050091132801911)
    ·
      refine ⟨44827674174075136699202867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29885116116050091132801911 44827674174075136699202867)
      ·
        refine ⟨67241511261112705048804301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44827674174075136699202867 67241511261112705048804301)
        ·
          refine ⟨25215566722917264393301613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67241511261112705048804301 25215566722917264393301613)
          ·
            refine ⟨9455837521093974147488105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25215566722917264393301613 9455837521093974147488105)
            ·
              refine ⟨7091878140820480610616079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9455837521093974147488105 7091878140820480610616079)
              ·
                refine ⟨10637817211230720915924119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7091878140820480610616079 10637817211230720915924119)
                ·
                  refine ⟨15956725816846081373886179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10637817211230720915924119 15956725816846081373886179)
                  ·
                    refine ⟨23935088725269122060829269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15956725816846081373886179 23935088725269122060829269)
                    ·
                      refine ⟨280489320999247524150343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 23935088725269122060829269 280489320999247524150343)
                      ·
                        rfl

theorem cell23_546251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 8].length) (baseStart_546251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546251 prefixEnd_546251 := by exact prefixLift 546251
  have htrace : WordTrace (prefixWord ++ tailWord_546251) baseStart_546251 baseEnd_546251 := by
    simpa [prefixWord, tailWord_546251, baseEnd_546251] using wordTrace_append hprefix tailTrace_546251
  have hstable : (prefixWord ++ tailWord_546251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546251).length < 2 ^ (prefixWord ++ tailWord_546251).sum := by decide
  have hdescent : baseEnd_546251 < baseStart_546251 := by decide
  rcases family_descends (prefixWord ++ tailWord_546251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546252 : List Nat := [2, 2, 1, 4, 2, 3, 1, 1, 3, 4]
def baseStart_546252 : Nat := 118140960795 + 546252 * 2 ^ 59
def prefixEnd_546252 : Nat := 4983230072969 + 3 ^ 40 * 546252 * 2
def baseEnd_546252 : Nat := 93496611493300673412613

theorem tailTrace_546252 : CollatzResearch.WordTrace tailWord_546252 prefixEnd_546252 93496611493300673412613 := by
  unfold tailWord_546252
  simp only [CollatzResearch.WordTrace]
  refine ⟨9961723608514885629660505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13282298144686514172880673 9961723608514885629660505)
  ·
    refine ⟨7471292706386164222245379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9961723608514885629660505 7471292706386164222245379)
    ·
      refine ⟨11206939059579246333368069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7471292706386164222245379 11206939059579246333368069)
      ·
        refine ⟨2101301073671108687506513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11206939059579246333368069 2101301073671108687506513)
        ·
          refine ⟨1575975805253331515629885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2101301073671108687506513 1575975805253331515629885)
          ·
            refine ⟨590990926969999318361207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1575975805253331515629885 590990926969999318361207)
            ·
              refine ⟨886486390454998977541811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 590990926969999318361207 886486390454998977541811)
              ·
                refine ⟨1329729585682498466312717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 886486390454998977541811 1329729585682498466312717)
                ·
                  refine ⟨498648594630936924867269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1329729585682498466312717 498648594630936924867269)
                  ·
                    refine ⟨93496611493300673412613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 498648594630936924867269 93496611493300673412613)
                    ·
                      rfl

theorem cell23_546252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 3, 4].length) (baseStart_546252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546252 prefixEnd_546252 := by exact prefixLift 546252
  have htrace : WordTrace (prefixWord ++ tailWord_546252) baseStart_546252 baseEnd_546252 := by
    simpa [prefixWord, tailWord_546252, baseEnd_546252] using wordTrace_append hprefix tailTrace_546252
  have hstable : (prefixWord ++ tailWord_546252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546252).length < 2 ^ (prefixWord ++ tailWord_546252).sum := by decide
  have hdescent : baseEnd_546252 < baseStart_546252 := by decide
  rcases family_descends (prefixWord ++ tailWord_546252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546265 : List Nat := [1, 2, 1, 2, 4, 2, 4, 1, 6]
def baseStart_546265 : Nat := 118140960795 + 546265 * 2 ^ 59
def prefixEnd_546265 : Nat := 4983230072969 + 3 ^ 40 * 546265 * 2
def baseEnd_546265 : Nat := 31166278858712274375031

theorem tailTrace_546265 : CollatzResearch.WordTrace tailWord_546265 prefixEnd_546265 31166278858712274375031 := by
  unfold tailWord_546265
  simp only [CollatzResearch.WordTrace]
  refine ⟨19923921365982674479544249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13282614243988449653029499 19923921365982674479544249)
  ·
    refine ⟨14942941024487005859658187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19923921365982674479544249 14942941024487005859658187)
    ·
      refine ⟨22414411536730508789487281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14942941024487005859658187 22414411536730508789487281)
      ·
        refine ⟨16810808652547881592115461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22414411536730508789487281 16810808652547881592115461)
        ·
          refine ⟨3152026622352727798521649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16810808652547881592115461 3152026622352727798521649)
          ·
            refine ⟨2364019966764545848891237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3152026622352727798521649 2364019966764545848891237)
            ·
              refine ⟨443253743768352346667107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2364019966764545848891237 443253743768352346667107)
              ·
                refine ⟨664880615652528520000661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 443253743768352346667107 664880615652528520000661)
                ·
                  refine ⟨31166278858712274375031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 664880615652528520000661 31166278858712274375031)
                  ·
                    rfl

theorem cell23_546265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 6].length) (baseStart_546265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546265 prefixEnd_546265 := by exact prefixLift 546265
  have htrace : WordTrace (prefixWord ++ tailWord_546265) baseStart_546265 baseEnd_546265 := by
    simpa [prefixWord, tailWord_546265, baseEnd_546265] using wordTrace_append hprefix tailTrace_546265
  have hstable : (prefixWord ++ tailWord_546265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546265).length < 2 ^ (prefixWord ++ tailWord_546265).sum := by decide
  have hdescent : baseEnd_546265 < baseStart_546265 := by decide
  rcases family_descends (prefixWord ++ tailWord_546265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546325 : List Nat := [1, 3, 2, 1, 3, 3, 2, 1, 1, 6]
def baseStart_546325 : Nat := 118140960795 + 546325 * 2 ^ 59
def prefixEnd_546325 : Nat := 4983230072969 + 3 ^ 40 * 546325 * 2
def baseEnd_546325 : Nat := 93509106189226744875001

theorem tailTrace_546325 : CollatzResearch.WordTrace tailWord_546325 prefixEnd_546325 93509106189226744875001 := by
  unfold tailWord_546325
  simp only [CollatzResearch.WordTrace]
  refine ⟨19926109745765304726728429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13284073163843536484485619 19926109745765304726728429)
  ·
    refine ⟨7472291154661989272523161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19926109745765304726728429 7472291154661989272523161)
    ·
      refine ⟨5604218365996491954392371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7472291154661989272523161 5604218365996491954392371)
      ·
        refine ⟨8406327548994737931588557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5604218365996491954392371 8406327548994737931588557)
        ·
          refine ⟨3152372830873026724345709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8406327548994737931588557 3152372830873026724345709)
          ·
            refine ⟨1182139811577385021629641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3152372830873026724345709 1182139811577385021629641)
            ·
              refine ⟨886604858683038766222231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1182139811577385021629641 886604858683038766222231)
              ·
                refine ⟨1329907288024558149333347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 886604858683038766222231 1329907288024558149333347)
                ·
                  refine ⟨1994860932036837224000021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1329907288024558149333347 1994860932036837224000021)
                  ·
                    refine ⟨93509106189226744875001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1994860932036837224000021 93509106189226744875001)
                    ·
                      rfl

theorem cell23_546325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_546325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546325 prefixEnd_546325 := by exact prefixLift 546325
  have htrace : WordTrace (prefixWord ++ tailWord_546325) baseStart_546325 baseEnd_546325 := by
    simpa [prefixWord, tailWord_546325, baseEnd_546325] using wordTrace_append hprefix tailTrace_546325
  have hstable : (prefixWord ++ tailWord_546325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546325).length < 2 ^ (prefixWord ++ tailWord_546325).sum := by decide
  have hdescent : baseEnd_546325 < baseStart_546325 := by decide
  rcases family_descends (prefixWord ++ tailWord_546325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546335 : List Nat := [1, 1, 2, 4, 1, 1, 4, 1, 3, 2, 3]
def baseStart_546335 : Nat := 118140960795 + 546335 * 2 ^ 59
def prefixEnd_546335 : Nat := 4983230072969 + 3 ^ 40 * 546335 * 2
def baseEnd_546335 : Nat := 280532453374225195499957

theorem tailTrace_546335 : CollatzResearch.WordTrace tailWord_546335 prefixEnd_546335 280532453374225195499957 := by
  unfold tailWord_546335
  simp only [CollatzResearch.WordTrace]
  refine ⟨19926474475729076434592459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13284316317152717623061639 19926474475729076434592459)
  ·
    refine ⟨29889711713593614651888689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19926474475729076434592459 29889711713593614651888689)
    ·
      refine ⟨22417283785195210988916517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29889711713593614651888689 22417283785195210988916517)
      ·
        refine ⟨4203240709724102060421847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22417283785195210988916517 4203240709724102060421847)
        ·
          refine ⟨6304861064586153090632771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4203240709724102060421847 6304861064586153090632771)
          ·
            refine ⟨9457291596879229635949157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6304861064586153090632771 9457291596879229635949157)
            ·
              refine ⟨1773242174414855556740467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9457291596879229635949157 1773242174414855556740467)
              ·
                refine ⟨2659863261622283335110701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1773242174414855556740467 2659863261622283335110701)
                ·
                  refine ⟨997448723108356250666513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2659863261622283335110701 997448723108356250666513)
                  ·
                    refine ⟨748086542331267187999885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 997448723108356250666513 748086542331267187999885)
                    ·
                      refine ⟨280532453374225195499957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 748086542331267187999885 280532453374225195499957)
                      ·
                        rfl

theorem cell23_546335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_546335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546335 prefixEnd_546335 := by exact prefixLift 546335
  have htrace : WordTrace (prefixWord ++ tailWord_546335) baseStart_546335 baseEnd_546335 := by
    simpa [prefixWord, tailWord_546335, baseEnd_546335] using wordTrace_append hprefix tailTrace_546335
  have hstable : (prefixWord ++ tailWord_546335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546335).length < 2 ^ (prefixWord ++ tailWord_546335).sum := by decide
  have hdescent : baseEnd_546335 < baseStart_546335 := by decide
  rcases family_descends (prefixWord ++ tailWord_546335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546338 : List Nat := [3, 3, 1, 1, 1, 1, 2, 11]
def baseStart_546338 : Nat := 118140960795 + 546338 * 2 ^ 59
def prefixEnd_546338 : Nat := 4983230072969 + 3 ^ 40 * 546338 * 2
def baseEnd_546338 : Nat := 10390147919118099398609

theorem tailTrace_546338 : CollatzResearch.WordTrace tailWord_546338 prefixEnd_546338 10390147919118099398609 := by
  unfold tailWord_546338
  simp only [CollatzResearch.WordTrace]
  refine ⟨4981645973679551986737917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13284389263145471964634445 4981645973679551986737917)
  ·
    refine ⟨1868117240129831995026719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4981645973679551986737917 1868117240129831995026719)
    ·
      refine ⟨2802175860194747992540079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1868117240129831995026719 2802175860194747992540079)
      ·
        refine ⟨4203263790292121988810119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2802175860194747992540079 4203263790292121988810119)
        ·
          refine ⟨6304895685438182983215179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4203263790292121988810119 6304895685438182983215179)
          ·
            refine ⟨9457343528157274474822769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6304895685438182983215179 9457343528157274474822769)
            ·
              refine ⟨7093007646117955856117077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9457343528157274474822769 7093007646117955856117077)
              ·
                refine ⟨10390147919118099398609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 7093007646117955856117077 10390147919118099398609)
                ·
                  rfl

theorem cell23_546338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 11].length) (baseStart_546338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546338 prefixEnd_546338 := by exact prefixLift 546338
  have htrace : WordTrace (prefixWord ++ tailWord_546338) baseStart_546338 baseEnd_546338 := by
    simpa [prefixWord, tailWord_546338, baseEnd_546338] using wordTrace_append hprefix tailTrace_546338
  have hstable : (prefixWord ++ tailWord_546338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546338).length < 2 ^ (prefixWord ++ tailWord_546338).sum := by decide
  have hdescent : baseEnd_546338 < baseStart_546338 := by decide
  rcases family_descends (prefixWord ++ tailWord_546338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546425 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 2, 4, 3]
def baseStart_546425 : Nat := 118140960795 + 546425 * 2 ^ 59
def prefixEnd_546425 : Nat := 4983230072969 + 3 ^ 40 * 546425 * 2
def baseEnd_546425 : Nat := 280578666633129843374543

theorem tailTrace_546425 : CollatzResearch.WordTrace tailWord_546425 prefixEnd_546425 280578666633129843374543 := by
  unfold tailWord_546425
  simp only [CollatzResearch.WordTrace]
  refine ⟨19929757045403021805368729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13286504696935347870245819 19929757045403021805368729)
  ·
    refine ⟨14947317784052266354026547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19929757045403021805368729 14947317784052266354026547)
    ·
      refine ⟨22420976676078399531039821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14947317784052266354026547 22420976676078399531039821)
      ·
        refine ⟨8407866253529399824139933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22420976676078399531039821 8407866253529399824139933)
        ·
          refine ⟨3152949845073524934052475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8407866253529399824139933 3152949845073524934052475)
          ·
            refine ⟨4729424767610287401078713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3152949845073524934052475 4729424767610287401078713)
            ·
              refine ⟨3547068575707715550809035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4729424767610287401078713 3547068575707715550809035)
              ·
                refine ⟨5320602863561573326213553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3547068575707715550809035 5320602863561573326213553)
                ·
                  refine ⟨3990452147671179994660165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5320602863561573326213553 3990452147671179994660165)
                  ·
                    refine ⟨748209777688346248998781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3990452147671179994660165 748209777688346248998781)
                    ·
                      refine ⟨280578666633129843374543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 748209777688346248998781 280578666633129843374543)
                      ·
                        rfl

theorem cell23_546425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_546425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546425 prefixEnd_546425 := by exact prefixLift 546425
  have htrace : WordTrace (prefixWord ++ tailWord_546425) baseStart_546425 baseEnd_546425 := by
    simpa [prefixWord, tailWord_546425, baseEnd_546425] using wordTrace_append hprefix tailTrace_546425
  have hstable : (prefixWord ++ tailWord_546425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546425).length < 2 ^ (prefixWord ++ tailWord_546425).sum := by decide
  have hdescent : baseEnd_546425 < baseStart_546425 := by decide
  rcases family_descends (prefixWord ++ tailWord_546425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546448 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 8]
def baseStart_546448 : Nat := 118140960795 + 546448 * 2 ^ 59
def prefixEnd_546448 : Nat := 4983230072969 + 3 ^ 40 * 546448 * 2
def baseEnd_546448 : Nat := 280590476688183253386937

theorem tailTrace_546448 : CollatzResearch.WordTrace tailWord_546448 prefixEnd_546448 280590476688183253386937 := by
  unfold tailWord_546448
  simp only [CollatzResearch.WordTrace]
  refine ⟨9965297962159848366727999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13287063949546464488970665 9965297962159848366727999)
  ·
    refine ⟨14947946943239772550091999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9965297962159848366727999 14947946943239772550091999)
    ·
      refine ⟨22421920414859658825137999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14947946943239772550091999 22421920414859658825137999)
      ·
        refine ⟨33632880622289488237706999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22421920414859658825137999 33632880622289488237706999)
        ·
          refine ⟨50449320933434232356560499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33632880622289488237706999 50449320933434232356560499)
          ·
            refine ⟨75673981400151348534840749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50449320933434232356560499 75673981400151348534840749)
            ·
              refine ⟨28377743025056755700565281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75673981400151348534840749 28377743025056755700565281)
              ·
                refine ⟨21283307268792566775423961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28377743025056755700565281 21283307268792566775423961)
                ·
                  refine ⟨15962480451594425081567971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21283307268792566775423961 15962480451594425081567971)
                  ·
                    refine ⟨23943720677391637622351957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15962480451594425081567971 23943720677391637622351957)
                    ·
                      refine ⟨280590476688183253386937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 23943720677391637622351957 280590476688183253386937)
                      ·
                        rfl

theorem cell23_546448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 8].length) (baseStart_546448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546448 prefixEnd_546448 := by exact prefixLift 546448
  have htrace : WordTrace (prefixWord ++ tailWord_546448) baseStart_546448 baseEnd_546448 := by
    simpa [prefixWord, tailWord_546448, baseEnd_546448] using wordTrace_append hprefix tailTrace_546448
  have hstable : (prefixWord ++ tailWord_546448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546448).length < 2 ^ (prefixWord ++ tailWord_546448).sum := by decide
  have hdescent : baseEnd_546448 < baseStart_546448 := by decide
  rcases family_descends (prefixWord ++ tailWord_546448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546482 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2]
def baseStart_546482 : Nat := 118140960795 + 546482 * 2 ^ 59
def prefixEnd_546482 : Nat := 4983230072969 + 3 ^ 40 * 546482 * 2
def baseEnd_546482 : Nat := 280607935030436120361781

theorem tailTrace_546482 : CollatzResearch.WordTrace tailWord_546482 prefixEnd_546482 280607935030436120361781 := by
  unfold tailWord_546482
  simp only [CollatzResearch.WordTrace]
  refine ⟨4982959001549130135048425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13287890670797680360129133 4982959001549130135048425)
  ·
    refine ⟨3737219251161847601286319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4982959001549130135048425 3737219251161847601286319)
    ·
      refine ⟨5605828876742771401929479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3737219251161847601286319 5605828876742771401929479)
      ·
        refine ⟨8408743315114157102894219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5605828876742771401929479 8408743315114157102894219)
        ·
          refine ⟨12613114972671235654341329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8408743315114157102894219 12613114972671235654341329)
          ·
            refine ⟨9459836229503426740755997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12613114972671235654341329 9459836229503426740755997)
            ·
              refine ⟨3547438586063785027783499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9459836229503426740755997 3547438586063785027783499)
              ·
                refine ⟨5321157879095677541675249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3547438586063785027783499 5321157879095677541675249)
                ·
                  refine ⟨3990868409321758156256437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5321157879095677541675249 3990868409321758156256437)
                  ·
                    refine ⟨374143913373914827149041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3990868409321758156256437 374143913373914827149041)
                    ·
                      refine ⟨280607935030436120361781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 374143913373914827149041 280607935030436120361781)
                      ·
                        rfl

theorem cell23_546482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2].length) (baseStart_546482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546482 prefixEnd_546482 := by exact prefixLift 546482
  have htrace : WordTrace (prefixWord ++ tailWord_546482) baseStart_546482 baseEnd_546482 := by
    simpa [prefixWord, tailWord_546482, baseEnd_546482] using wordTrace_append hprefix tailTrace_546482
  have hstable : (prefixWord ++ tailWord_546482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546482).length < 2 ^ (prefixWord ++ tailWord_546482).sum := by decide
  have hdescent : baseEnd_546482 < baseStart_546482 := by decide
  rcases family_descends (prefixWord ++ tailWord_546482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546495 : List Nat := [1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 4]
def baseStart_546495 : Nat := 118140960795 + 546495 * 2 ^ 59
def prefixEnd_546495 : Nat := 4983230072969 + 3 ^ 40 * 546495 * 2
def baseEnd_546495 : Nat := 280614610278944569499221

theorem tailTrace_546495 : CollatzResearch.WordTrace tailWord_546495 prefixEnd_546495 280614610278944569499221 := by
  unfold tailWord_546495
  simp only [CollatzResearch.WordTrace]
  refine ⟨19932310155149423760416939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13288206770099615840277959 19932310155149423760416939)
  ·
    refine ⟨29898465232724135640625409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19932310155149423760416939 29898465232724135640625409)
    ·
      refine ⟨22423848924543101730469057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29898465232724135640625409 22423848924543101730469057)
      ·
        refine ⟨16817886693407326297851793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22423848924543101730469057 16817886693407326297851793)
        ·
          refine ⟨12613415020055494723388845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16817886693407326297851793 12613415020055494723388845)
          ·
            refine ⟨4730030632520810521270817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12613415020055494723388845 4730030632520810521270817)
            ·
              refine ⟨3547522974390607890953113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4730030632520810521270817 3547522974390607890953113)
              ·
                refine ⟨2660642230792955918214835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3547522974390607890953113 2660642230792955918214835)
                ·
                  refine ⟨3990963346189433877322253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2660642230792955918214835 3990963346189433877322253)
                  ·
                    refine ⟨1496611254821037703995845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3990963346189433877322253 1496611254821037703995845)
                    ·
                      refine ⟨280614610278944569499221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1496611254821037703995845 280614610278944569499221)
                      ·
                        rfl

theorem cell23_546495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_546495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546495 prefixEnd_546495 := by exact prefixLift 546495
  have htrace : WordTrace (prefixWord ++ tailWord_546495) baseStart_546495 baseEnd_546495 := by
    simpa [prefixWord, tailWord_546495, baseEnd_546495] using wordTrace_append hprefix tailTrace_546495
  have hstable : (prefixWord ++ tailWord_546495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546495).length < 2 ^ (prefixWord ++ tailWord_546495).sum := by decide
  have hdescent : baseEnd_546495 < baseStart_546495 := by decide
  rcases family_descends (prefixWord ++ tailWord_546495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546509 : List Nat := [1, 6, 2, 1, 1, 2, 1, 1, 1, 7]
def baseStart_546509 : Nat := 118140960795 + 546509 * 2 ^ 59
def prefixEnd_546509 : Nat := 4983230072969 + 3 ^ 40 * 546509 * 2
def baseEnd_546509 : Nat := 93540599669369171574719

theorem tailTrace_546509 : CollatzResearch.WordTrace tailWord_546509 prefixEnd_546509 93540599669369171574719 := by
  unfold tailWord_546509
  simp only [CollatzResearch.WordTrace]
  refine ⟨19932820777098704151426581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13288547184732469434284387 19932820777098704151426581)
  ·
    refine ⟨934350973926501757098121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19932820777098704151426581 934350973926501757098121)
    ·
      refine ⟨700763230444876317823591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 934350973926501757098121 700763230444876317823591)
      ·
        refine ⟨1051144845667314476735387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 700763230444876317823591 1051144845667314476735387)
        ·
          refine ⟨1576717268500971715103081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1051144845667314476735387 1576717268500971715103081)
          ·
            refine ⟨1182537951375728786327311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1576717268500971715103081 1182537951375728786327311)
            ·
              refine ⟨1773806927063593179490967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1182537951375728786327311 1773806927063593179490967)
              ·
                refine ⟨2660710390595389769236451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1773806927063593179490967 2660710390595389769236451)
                ·
                  refine ⟨3991065585893084653854677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2660710390595389769236451 3991065585893084653854677)
                  ·
                    refine ⟨93540599669369171574719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3991065585893084653854677 93540599669369171574719)
                    ·
                      rfl

theorem cell23_546509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_546509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546509 prefixEnd_546509 := by exact prefixLift 546509
  have htrace : WordTrace (prefixWord ++ tailWord_546509) baseStart_546509 baseEnd_546509 := by
    simpa [prefixWord, tailWord_546509, baseEnd_546509] using wordTrace_append hprefix tailTrace_546509
  have hstable : (prefixWord ++ tailWord_546509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546509).length < 2 ^ (prefixWord ++ tailWord_546509).sum := by decide
  have hdescent : baseEnd_546509 < baseStart_546509 := by decide
  rcases family_descends (prefixWord ++ tailWord_546509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546532 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 4, 2, 3]
def baseStart_546532 : Nat := 118140960795 + 546532 * 2 ^ 59
def prefixEnd_546532 : Nat := 4983230072969 + 3 ^ 40 * 546532 * 2
def baseEnd_546532 : Nat := 280633609063160924736551

theorem tailTrace_546532 : CollatzResearch.WordTrace tailWord_546532 prefixEnd_546532 280633609063160924736551 := by
  unfold tailWord_546532
  simp only [CollatzResearch.WordTrace]
  refine ⟨9966829828007689539756925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13289106437343586053009233 9966829828007689539756925)
  ·
    refine ⟨3737561185502883577408847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9966829828007689539756925 3737561185502883577408847)
    ·
      refine ⟨5606341778254325366113271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3737561185502883577408847 5606341778254325366113271)
      ·
        refine ⟨8409512667381488049169907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5606341778254325366113271 8409512667381488049169907)
        ·
          refine ⟨12614269001072232073754861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8409512667381488049169907 12614269001072232073754861)
          ·
            refine ⟨4730350875402087027658073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12614269001072232073754861 4730350875402087027658073)
            ·
              refine ⟨3547763156551565270743555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4730350875402087027658073 3547763156551565270743555)
              ·
                refine ⟨5321644734827347906115333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3547763156551565270743555 5321644734827347906115333)
                ·
                  refine ⟨997808387780127732396625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5321644734827347906115333 997808387780127732396625)
                  ·
                    refine ⟨748356290835095799297469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 997808387780127732396625 748356290835095799297469)
                    ·
                      refine ⟨280633609063160924736551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 748356290835095799297469 280633609063160924736551)
                      ·
                        rfl

theorem cell23_546532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_546532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546532 prefixEnd_546532 := by exact prefixLift 546532
  have htrace : WordTrace (prefixWord ++ tailWord_546532) baseStart_546532 baseEnd_546532 := by
    simpa [prefixWord, tailWord_546532, baseEnd_546532] using wordTrace_append hprefix tailTrace_546532
  have hstable : (prefixWord ++ tailWord_546532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546532).length < 2 ^ (prefixWord ++ tailWord_546532).sum := by decide
  have hdescent : baseEnd_546532 < baseStart_546532 := by decide
  rcases family_descends (prefixWord ++ tailWord_546532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546539 : List Nat := [1, 1, 1, 1, 2, 4, 4, 4, 1, 4]
def baseStart_546539 : Nat := 118140960795 + 546539 * 2 ^ 59
def prefixEnd_546539 : Nat := 4983230072969 + 3 ^ 40 * 546539 * 2
def baseEnd_546539 : Nat := 93545734475914132449673

theorem tailTrace_546539 : CollatzResearch.WordTrace tailWord_546539 prefixEnd_546539 93545734475914132449673 := by
  unfold tailWord_546539
  simp only [CollatzResearch.WordTrace]
  refine ⟨19933914966990019275018671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13289276644660012850012447 19933914966990019275018671)
  ·
    refine ⟨29900872450485028912528007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19933914966990019275018671 29900872450485028912528007)
    ·
      refine ⟨44851308675727543368792011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29900872450485028912528007 44851308675727543368792011)
      ·
        refine ⟨67276963013591315053188017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44851308675727543368792011 67276963013591315053188017)
        ·
          refine ⟨50457722260193486289891013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67276963013591315053188017 50457722260193486289891013)
          ·
            refine ⟨9460822923786278679354565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50457722260193486289891013 9460822923786278679354565)
            ·
              refine ⟨1773904298209927252378981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9460822923786278679354565 1773904298209927252378981)
              ·
                refine ⟨332607055914361359821059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1773904298209927252378981 332607055914361359821059)
                ·
                  refine ⟨498910583871542039731589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 332607055914361359821059 498910583871542039731589)
                  ·
                    refine ⟨93545734475914132449673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 498910583871542039731589 93545734475914132449673)
                    ·
                      rfl

theorem cell23_546539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4, 1, 4].length) (baseStart_546539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546539 prefixEnd_546539 := by exact prefixLift 546539
  have htrace : WordTrace (prefixWord ++ tailWord_546539) baseStart_546539 baseEnd_546539 := by
    simpa [prefixWord, tailWord_546539, baseEnd_546539] using wordTrace_append hprefix tailTrace_546539
  have hstable : (prefixWord ++ tailWord_546539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546539).length < 2 ^ (prefixWord ++ tailWord_546539).sum := by decide
  have hdescent : baseEnd_546539 < baseStart_546539 := by decide
  rcases family_descends (prefixWord ++ tailWord_546539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546585 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 1, 7, 4]
def baseStart_546585 : Nat := 118140960795 + 546585 * 2 ^ 59
def prefixEnd_546585 : Nat := 4983230072969 + 3 ^ 40 * 546585 * 2
def baseEnd_546585 : Nat := 280660823537849217373807

theorem tailTrace_546585 : CollatzResearch.WordTrace tailWord_546585 prefixEnd_546585 280660823537849217373807 := by
  unfold tailWord_546585
  simp only [CollatzResearch.WordTrace]
  refine ⟨19935592724823369131193209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13290395149882246087462139 19935592724823369131193209)
  ·
    refine ⟨14951694543617526848394907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19935592724823369131193209 14951694543617526848394907)
    ·
      refine ⟨22427541815426290272592361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14951694543617526848394907 22427541815426290272592361)
      ·
        refine ⟨16820656361569717704444271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22427541815426290272592361 16820656361569717704444271)
        ·
          refine ⟨25230984542354576556666407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16820656361569717704444271 25230984542354576556666407)
          ·
            refine ⟨37846476813531864834999611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25230984542354576556666407 37846476813531864834999611)
            ·
              refine ⟨56769715220297797252499417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37846476813531864834999611 56769715220297797252499417)
              ·
                refine ⟨42577286415223347939374563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56769715220297797252499417 42577286415223347939374563)
                ·
                  refine ⟨63865929622835021909061845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42577286415223347939374563 63865929622835021909061845)
                  ·
                    refine ⟨1496857725535195825993637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 63865929622835021909061845 1496857725535195825993637)
                    ·
                      refine ⟨280660823537849217373807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1496857725535195825993637 280660823537849217373807)
                      ·
                        rfl

theorem cell23_546585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_546585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546585 prefixEnd_546585 := by exact prefixLift 546585
  have htrace : WordTrace (prefixWord ++ tailWord_546585) baseStart_546585 baseEnd_546585 := by
    simpa [prefixWord, tailWord_546585, baseEnd_546585] using wordTrace_append hprefix tailTrace_546585
  have hstable : (prefixWord ++ tailWord_546585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546585).length < 2 ^ (prefixWord ++ tailWord_546585).sum := by decide
  have hdescent : baseEnd_546585 < baseStart_546585 := by decide
  rcases family_descends (prefixWord ++ tailWord_546585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546590 : List Nat := [4, 3, 2, 2, 1, 2, 1, 1, 3, 4]
def baseStart_546590 : Nat := 118140960795 + 546590 * 2 ^ 59
def prefixEnd_546590 : Nat := 4983230072969 + 3 ^ 40 * 546590 * 2
def baseEnd_546590 : Nat := 93554463647040565937095

theorem tailTrace_546590 : CollatzResearch.WordTrace tailWord_546590 prefixEnd_546590 93554463647040565937095 := by
  unfold tailWord_546590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2491971886225656873140653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13290516726536836656750149 2491971886225656873140653)
  ·
    refine ⟨934489457334621327427745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2491971886225656873140653 934489457334621327427745)
    ·
      refine ⟨700867093000965995570809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 934489457334621327427745 700867093000965995570809)
      ·
        refine ⟨525650319750724496678107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 700867093000965995570809 525650319750724496678107)
        ·
          refine ⟨788475479626086745017161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 525650319750724496678107 788475479626086745017161)
          ·
            refine ⟨591356609719565058762871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 788475479626086745017161 591356609719565058762871)
            ·
              refine ⟨887034914579347588144307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 591356609719565058762871 887034914579347588144307)
              ·
                refine ⟨1330552371869021382216461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 887034914579347588144307 1330552371869021382216461)
                ·
                  refine ⟨498957139450883018331173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1330552371869021382216461 498957139450883018331173)
                  ·
                    refine ⟨93554463647040565937095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 498957139450883018331173 93554463647040565937095)
                    ·
                      rfl

theorem cell23_546590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_546590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546590 prefixEnd_546590 := by exact prefixLift 546590
  have htrace : WordTrace (prefixWord ++ tailWord_546590) baseStart_546590 baseEnd_546590 := by
    simpa [prefixWord, tailWord_546590, baseEnd_546590] using wordTrace_append hprefix tailTrace_546590
  have hstable : (prefixWord ++ tailWord_546590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546590).length < 2 ^ (prefixWord ++ tailWord_546590).sum := by decide
  have hdescent : baseEnd_546590 < baseStart_546590 := by decide
  rcases family_descends (prefixWord ++ tailWord_546590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546596 : List Nat := [2, 3, 1, 3, 2, 1, 3, 1, 3, 1, 3]
def baseStart_546596 : Nat := 118140960795 + 546596 * 2 ^ 59
def prefixEnd_546596 : Nat := 4983230072969 + 3 ^ 40 * 546596 * 2
def baseEnd_546596 : Nat := 280666471825048674336257

theorem tailTrace_546596 : CollatzResearch.WordTrace tailWord_546596 prefixEnd_546596 280666471825048674336257 := by
  unfold tailWord_546596
  simp only [CollatzResearch.WordTrace]
  refine ⟨9967996963891759004921821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13290662618522345339895761 9967996963891759004921821)
  ·
    refine ⟨3737998861459409626845683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9967996963891759004921821 3737998861459409626845683)
    ·
      refine ⟨5606998292189114440268525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3737998861459409626845683 5606998292189114440268525)
      ·
        refine ⟨2102624359570917915100697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5606998292189114440268525 2102624359570917915100697)
        ·
          refine ⟨1576968269678188436325523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2102624359570917915100697 1576968269678188436325523)
          ·
            refine ⟨2365452404517282654488285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1576968269678188436325523 2365452404517282654488285)
            ·
              refine ⟨887044651693980995433107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2365452404517282654488285 887044651693980995433107)
              ·
                refine ⟨1330566977540971493149661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 887044651693980995433107 1330566977540971493149661)
                ·
                  refine ⟨498962616577864309931123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1330566977540971493149661 498962616577864309931123)
                  ·
                    refine ⟨748443924866796464896685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 498962616577864309931123 748443924866796464896685)
                    ·
                      refine ⟨280666471825048674336257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 748443924866796464896685 280666471825048674336257)
                      ·
                        rfl

theorem cell23_546596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_546596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546596 prefixEnd_546596 := by exact prefixLift 546596
  have htrace : WordTrace (prefixWord ++ tailWord_546596) baseStart_546596 baseEnd_546596 := by
    simpa [prefixWord, tailWord_546596, baseEnd_546596] using wordTrace_append hprefix tailTrace_546596
  have hstable : (prefixWord ++ tailWord_546596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546596).length < 2 ^ (prefixWord ++ tailWord_546596).sum := by decide
  have hdescent : baseEnd_546596 < baseStart_546596 := by decide
  rcases family_descends (prefixWord ++ tailWord_546596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546632 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 3, 2, 4]
def baseStart_546632 : Nat := 118140960795 + 546632 * 2 ^ 59
def prefixEnd_546632 : Nat := 4983230072969 + 3 ^ 40 * 546632 * 2
def baseEnd_546632 : Nat := 280684957128610533486091

theorem tailTrace_546632 : CollatzResearch.WordTrace tailWord_546632 prefixEnd_546632 280684957128610533486091 := by
  unfold tailWord_546632
  simp only [CollatzResearch.WordTrace]
  refine ⟨9968653477826548079077075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13291537970435397438769433 9968653477826548079077075)
  ·
    refine ⟨14952980216739822118615613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9968653477826548079077075 14952980216739822118615613)
    ·
      refine ⟨5607367581277433294480855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14952980216739822118615613 5607367581277433294480855)
      ·
        refine ⟨8411051371916149941721283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5607367581277433294480855 8411051371916149941721283)
        ·
          refine ⟨12616577057874224912581925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8411051371916149941721283 12616577057874224912581925)
          ·
            refine ⟨2365608198351417171109111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12616577057874224912581925 2365608198351417171109111)
            ·
              refine ⟨3548412297527125756663667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2365608198351417171109111 3548412297527125756663667)
              ·
                refine ⟨5322618446290688634995501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3548412297527125756663667 5322618446290688634995501)
                ·
                  refine ⟨1995981917359008238123313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5322618446290688634995501 1995981917359008238123313)
                  ·
                    refine ⟨1496986438019256178592485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1995981917359008238123313 1496986438019256178592485)
                    ·
                      refine ⟨280684957128610533486091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1496986438019256178592485 280684957128610533486091)
                      ·
                        rfl

theorem cell23_546632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_546632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546632 prefixEnd_546632 := by exact prefixLift 546632
  have htrace : WordTrace (prefixWord ++ tailWord_546632) baseStart_546632 baseEnd_546632 := by
    simpa [prefixWord, tailWord_546632, baseEnd_546632] using wordTrace_append hprefix tailTrace_546632
  have hstable : (prefixWord ++ tailWord_546632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546632).length < 2 ^ (prefixWord ++ tailWord_546632).sum := by decide
  have hdescent : baseEnd_546632 < baseStart_546632 := by decide
  rcases family_descends (prefixWord ++ tailWord_546632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546647 : List Nat := [1, 1, 3, 2, 6, 1, 2, 2, 1, 1, 3]
def baseStart_546647 : Nat := 118140960795 + 546647 * 2 ^ 59
def prefixEnd_546647 : Nat := 4983230072969 + 3 ^ 40 * 546647 * 2
def baseEnd_546647 : Nat := 280692659338427974798523

theorem tailTrace_546647 : CollatzResearch.WordTrace tailWord_546647 prefixEnd_546647 280692659338427974798523 := by
  unfold tailWord_546647
  simp only [CollatzResearch.WordTrace]
  refine ⟨19937854050598753719950195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13291902700399169146633463 19937854050598753719950195)
  ·
    refine ⟨29906781075898130579925293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19937854050598753719950195 29906781075898130579925293)
    ·
      refine ⟨11215042903461798967471985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29906781075898130579925293 11215042903461798967471985)
      ·
        refine ⟨8411282177596349225603989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11215042903461798967471985 8411282177596349225603989)
        ·
          refine ⟨394278852074828869950187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8411282177596349225603989 394278852074828869950187)
          ·
            refine ⟨591418278112243304925281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394278852074828869950187 591418278112243304925281)
            ·
              refine ⟨443563708584182478693961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 591418278112243304925281 443563708584182478693961)
              ·
                refine ⟨332672781438136859020471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443563708584182478693961 332672781438136859020471)
                ·
                  refine ⟨499009172157205288530707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 332672781438136859020471 499009172157205288530707)
                  ·
                    refine ⟨748513758235807932796061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 499009172157205288530707 748513758235807932796061)
                    ·
                      refine ⟨280692659338427974798523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 748513758235807932796061 280692659338427974798523)
                      ·
                        rfl

theorem cell23_546647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 2, 1, 1, 3].length) (baseStart_546647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546647 prefixEnd_546647 := by exact prefixLift 546647
  have htrace : WordTrace (prefixWord ++ tailWord_546647) baseStart_546647 baseEnd_546647 := by
    simpa [prefixWord, tailWord_546647, baseEnd_546647] using wordTrace_append hprefix tailTrace_546647
  have hstable : (prefixWord ++ tailWord_546647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546647).length < 2 ^ (prefixWord ++ tailWord_546647).sum := by decide
  have hdescent : baseEnd_546647 < baseStart_546647 := by decide
  rcases family_descends (prefixWord ++ tailWord_546647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546659 : List Nat := [1, 1, 1, 5, 4, 2, 1, 8]
def baseStart_546659 : Nat := 118140960795 + 546659 * 2 ^ 59
def prefixEnd_546659 : Nat := 4983230072969 + 3 ^ 40 * 546659 * 2
def baseEnd_546659 : Nat := 10396252633565997327721

theorem tailTrace_546659 : CollatzResearch.WordTrace tailWord_546659 prefixEnd_546659 10396252633565997327721 := by
  unfold tailWord_546659
  simp only [CollatzResearch.WordTrace]
  refine ⟨19938291726555279769387031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13292194484370186512924687 19938291726555279769387031)
  ·
    refine ⟨29907437589832919654080547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19938291726555279769387031 29907437589832919654080547)
    ·
      refine ⟨44861156384749379481120821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29907437589832919654080547 44861156384749379481120821)
      ·
        refine ⟨4205733411070254326355077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44861156384749379481120821 4205733411070254326355077)
        ·
          refine ⟨788575014575672686191577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4205733411070254326355077 788575014575672686191577)
          ·
            refine ⟨591431260931754514643683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 788575014575672686191577 591431260931754514643683)
            ·
              refine ⟨887146891397631771965525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 591431260931754514643683 887146891397631771965525)
              ·
                refine ⟨10396252633565997327721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 887146891397631771965525 10396252633565997327721)
                ·
                  rfl

theorem cell23_546659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 8].length) (baseStart_546659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546659 prefixEnd_546659 := by exact prefixLift 546659
  have htrace : WordTrace (prefixWord ++ tailWord_546659) baseStart_546659 baseEnd_546659 := by
    simpa [prefixWord, tailWord_546659, baseEnd_546659] using wordTrace_append hprefix tailTrace_546659
  have hstable : (prefixWord ++ tailWord_546659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546659).length < 2 ^ (prefixWord ++ tailWord_546659).sum := by decide
  have hdescent : baseEnd_546659 < baseStart_546659 := by decide
  rcases family_descends (prefixWord ++ tailWord_546659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546669 : List Nat := [1, 5, 1, 1, 1, 1, 3, 3, 1, 3, 3]
def baseStart_546669 : Nat := 118140960795 + 546669 * 2 ^ 59
def prefixEnd_546669 : Nat := 4983230072969 + 3 ^ 40 * 546669 * 2
def baseEnd_546669 : Nat := 280703955912826888723421

theorem tailTrace_546669 : CollatzResearch.WordTrace tailWord_546669 prefixEnd_546669 280703955912826888723421 := by
  unfold tailWord_546669
  simp only [CollatzResearch.WordTrace]
  refine ⟨19938656456519051477251061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13292437637679367651500707 19938656456519051477251061)
  ·
    refine ⟨1869249042798661075992287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19938656456519051477251061 1869249042798661075992287)
    ·
      refine ⟨2803873564197991613988431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1869249042798661075992287 2803873564197991613988431)
      ·
        refine ⟨4205810346296987420982647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2803873564197991613988431 4205810346296987420982647)
        ·
          refine ⟨6308715519445481131473971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4205810346296987420982647 6308715519445481131473971)
          ·
            refine ⟨9463073279168221697210957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6308715519445481131473971 9463073279168221697210957)
            ·
              refine ⟨3548652479688083136454109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9463073279168221697210957 3548652479688083136454109)
              ·
                refine ⟨1330744679883031176170291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3548652479688083136454109 1330744679883031176170291)
                ·
                  refine ⟨1996117019824546764255437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1330744679883031176170291 1996117019824546764255437)
                  ·
                    refine ⟨748543882434205036595789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1996117019824546764255437 748543882434205036595789)
                    ·
                      refine ⟨280703955912826888723421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 748543882434205036595789 280703955912826888723421)
                      ·
                        rfl

theorem cell23_546669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_546669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546669 prefixEnd_546669 := by exact prefixLift 546669
  have htrace : WordTrace (prefixWord ++ tailWord_546669) baseStart_546669 baseEnd_546669 := by
    simpa [prefixWord, tailWord_546669, baseEnd_546669] using wordTrace_append hprefix tailTrace_546669
  have hstable : (prefixWord ++ tailWord_546669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546669).length < 2 ^ (prefixWord ++ tailWord_546669).sum := by decide
  have hdescent : baseEnd_546669 < baseStart_546669 := by decide
  rcases family_descends (prefixWord ++ tailWord_546669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546777 : List Nat := [1, 2, 1, 2, 6, 2, 2, 1, 2, 2, 2]
def baseStart_546777 : Nat := 118140960795 + 546777 * 2 ^ 59
def prefixEnd_546777 : Nat := 4983230072969 + 3 ^ 40 * 546777 * 2
def baseEnd_546777 : Nat := 280759411823512466172925

theorem tailTrace_546777 : CollatzResearch.WordTrace tailWord_546777 prefixEnd_546777 280759411823512466172925 := by
  unfold tailWord_546777
  simp only [CollatzResearch.WordTrace]
  refine ⟨19942595540127785922182585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13295063693418523948121723 19942595540127785922182585)
  ·
    refine ⟨14956946655095839441636939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19942595540127785922182585 14956946655095839441636939)
    ·
      refine ⟨22435419982643759162455409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14956946655095839441636939 22435419982643759162455409)
      ·
        refine ⟨16826564986982819371841557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22435419982643759162455409 16826564986982819371841557)
        ·
          refine ⟨788745233764819658055073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16826564986982819371841557 788745233764819658055073)
          ·
            refine ⟨591558925323614743541305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 788745233764819658055073 591558925323614743541305)
            ·
              refine ⟨443669193992711057655979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 591558925323614743541305 443669193992711057655979)
              ·
                refine ⟨665503790989066586483969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 443669193992711057655979 665503790989066586483969)
                ·
                  refine ⟨499127843241799939862977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 665503790989066586483969 499127843241799939862977)
                  ·
                    refine ⟨374345882431349954897233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 499127843241799939862977 374345882431349954897233)
                    ·
                      refine ⟨280759411823512466172925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 374345882431349954897233 280759411823512466172925)
                      ·
                        rfl

theorem cell23_546777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 2, 2, 2].length) (baseStart_546777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546777 prefixEnd_546777 := by exact prefixLift 546777
  have htrace : WordTrace (prefixWord ++ tailWord_546777) baseStart_546777 baseEnd_546777 := by
    simpa [prefixWord, tailWord_546777, baseEnd_546777] using wordTrace_append hprefix tailTrace_546777
  have hstable : (prefixWord ++ tailWord_546777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546777).length < 2 ^ (prefixWord ++ tailWord_546777).sum := by decide
  have hdescent : baseEnd_546777 < baseStart_546777 := by decide
  rcases family_descends (prefixWord ++ tailWord_546777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546853 : List Nat := [1, 3, 1, 2, 2, 5, 1, 1, 2, 2, 3]
def baseStart_546853 : Nat := 118140960795 + 546853 * 2 ^ 59
def prefixEnd_546853 : Nat := 4983230072969 + 3 ^ 40 * 546853 * 2
def baseEnd_546853 : Nat := 280798436353254168822575

theorem tailTrace_546853 : CollatzResearch.WordTrace tailWord_546853 prefixEnd_546853 280798436353254168822575 := by
  unfold tailWord_546853
  simp only [CollatzResearch.WordTrace]
  refine ⟨19945367487852450901949213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13296911658568300601299475 19945367487852450901949213)
  ·
    refine ⟨7479512807944669088230955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19945367487852450901949213 7479512807944669088230955)
    ·
      refine ⟨11219269211917003632346433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7479512807944669088230955 11219269211917003632346433)
      ·
        refine ⟨8414451908937752724259825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11219269211917003632346433 8414451908937752724259825)
        ·
          refine ⟨6310838931703314543194869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8414451908937752724259825 6310838931703314543194869)
          ·
            refine ⟨591641149847185738424519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6310838931703314543194869 591641149847185738424519)
            ·
              refine ⟨887461724770778607636779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 591641149847185738424519 887461724770778607636779)
              ·
                refine ⟨1331192587156167911455169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 887461724770778607636779 1331192587156167911455169)
                ·
                  refine ⟨998394440367125933591377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1331192587156167911455169 998394440367125933591377)
                  ·
                    refine ⟨748795830275344450193533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 998394440367125933591377 748795830275344450193533)
                    ·
                      refine ⟨280798436353254168822575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 748795830275344450193533 280798436353254168822575)
                      ·
                        rfl

theorem cell23_546853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_546853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546853 prefixEnd_546853 := by exact prefixLift 546853
  have htrace : WordTrace (prefixWord ++ tailWord_546853) baseStart_546853 baseEnd_546853 := by
    simpa [prefixWord, tailWord_546853, baseEnd_546853] using wordTrace_append hprefix tailTrace_546853
  have hstable : (prefixWord ++ tailWord_546853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546853).length < 2 ^ (prefixWord ++ tailWord_546853).sum := by decide
  have hdescent : baseEnd_546853 < baseStart_546853 := by decide
  rcases family_descends (prefixWord ++ tailWord_546853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546873 : List Nat := [1, 2, 1, 5, 3, 2, 1, 2, 6]
def baseStart_546873 : Nat := 118140960795 + 546873 * 2 ^ 59
def prefixEnd_546873 : Nat := 4983230072969 + 3 ^ 40 * 546873 * 2
def baseEnd_546873 : Nat := 31200967329593787841387

theorem tailTrace_546873 : CollatzResearch.WordTrace tailWord_546873 prefixEnd_546873 31200967329593787841387 := by
  unfold tailWord_546873
  simp only [CollatzResearch.WordTrace]
  refine ⟨19946096947779994317677273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13297397965186662878451515 19946096947779994317677273)
  ·
    refine ⟨14959572710834995738257955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19946096947779994317677273 14959572710834995738257955)
    ·
      refine ⟨22439359066252493607386933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14959572710834995738257955 22439359066252493607386933)
      ·
        refine ⟨2103689912461171275692525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22439359066252493607386933 2103689912461171275692525)
        ·
          refine ⟨788883717172939228384697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2103689912461171275692525 788883717172939228384697)
          ·
            refine ⟨591662787879704421288523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 788883717172939228384697 591662787879704421288523)
            ·
              refine ⟨887494181819556631932785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 591662787879704421288523 887494181819556631932785)
              ·
                refine ⟨665620636364667473949589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 887494181819556631932785 665620636364667473949589)
                ·
                  refine ⟨31200967329593787841387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 665620636364667473949589 31200967329593787841387)
                  ·
                    rfl

theorem cell23_546873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 6].length) (baseStart_546873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546873 prefixEnd_546873 := by exact prefixLift 546873
  have htrace : WordTrace (prefixWord ++ tailWord_546873) baseStart_546873 baseEnd_546873 := by
    simpa [prefixWord, tailWord_546873, baseEnd_546873] using wordTrace_append hprefix tailTrace_546873
  have hstable : (prefixWord ++ tailWord_546873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546873).length < 2 ^ (prefixWord ++ tailWord_546873).sum := by decide
  have hdescent : baseEnd_546873 < baseStart_546873 := by decide
  rcases family_descends (prefixWord ++ tailWord_546873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546893 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 3, 5, 2]
def baseStart_546893 : Nat := 118140960795 + 546893 * 2 ^ 59
def prefixEnd_546893 : Nat := 4983230072969 + 3 ^ 40 * 546893 * 2
def baseEnd_546893 : Nat := 280818975579434012322391

theorem tailTrace_546893 : CollatzResearch.WordTrace tailWord_546893 prefixEnd_546893 280818975579434012322391 := by
  unfold tailWord_546893
  simp only [CollatzResearch.WordTrace]
  refine ⟨19946826407707537733405333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13297884271805025155603555 19946826407707537733405333)
  ·
    refine ⟨935007487861290831253375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19946826407707537733405333 935007487861290831253375)
    ·
      refine ⟨1402511231791936246880063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 935007487861290831253375 1402511231791936246880063)
      ·
        refine ⟨2103766847687904370320095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1402511231791936246880063 2103766847687904370320095)
        ·
          refine ⟨3155650271531856555480143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2103766847687904370320095 3155650271531856555480143)
          ·
            refine ⟨4733475407297784833220215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3155650271531856555480143 4733475407297784833220215)
            ·
              refine ⟨7100213110946677249830323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4733475407297784833220215 7100213110946677249830323)
              ·
                refine ⟨10650319666420015874745485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7100213110946677249830323 10650319666420015874745485)
                ·
                  refine ⟨3993869874907505953029557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10650319666420015874745485 3993869874907505953029557)
                  ·
                    refine ⟨374425300772578683096521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3993869874907505953029557 374425300772578683096521)
                    ·
                      refine ⟨280818975579434012322391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 374425300772578683096521 280818975579434012322391)
                      ·
                        rfl

theorem cell23_546893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_546893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546893 prefixEnd_546893 := by exact prefixLift 546893
  have htrace : WordTrace (prefixWord ++ tailWord_546893) baseStart_546893 baseEnd_546893 := by
    simpa [prefixWord, tailWord_546893, baseEnd_546893] using wordTrace_append hprefix tailTrace_546893
  have hstable : (prefixWord ++ tailWord_546893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546893).length < 2 ^ (prefixWord ++ tailWord_546893).sum := by decide
  have hdescent : baseEnd_546893 < baseStart_546893 := by decide
  rcases family_descends (prefixWord ++ tailWord_546893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546906 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 2, 6, 2]
def baseStart_546906 : Nat := 118140960795 + 546906 * 2 ^ 59
def prefixEnd_546906 : Nat := 4983230072969 + 3 ^ 40 * 546906 * 2
def baseEnd_546906 : Nat := 280825650827942461459831

theorem tailTrace_546906 : CollatzResearch.WordTrace tailWord_546906 prefixEnd_546906 280825650827942461459831 := by
  unfold tailWord_546906
  simp only [CollatzResearch.WordTrace]
  refine ⟨4986825139165110238407143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13298200371106960635752381 4986825139165110238407143)
  ·
    refine ⟨7480237708747665357610715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4986825139165110238407143 7480237708747665357610715)
    ·
      refine ⟨11220356563121498036416073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7480237708747665357610715 11220356563121498036416073)
      ·
        refine ⟨8415267422341123527312055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11220356563121498036416073 8415267422341123527312055)
        ·
          refine ⟨12622901133511685290968083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8415267422341123527312055 12622901133511685290968083)
          ·
            refine ⟨18934351700267527936452125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12622901133511685290968083 18934351700267527936452125)
            ·
              refine ⟨7100381887600322976169547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18934351700267527936452125 7100381887600322976169547)
              ·
                refine ⟨10650572831400484464254321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7100381887600322976169547 10650572831400484464254321)
                ·
                  refine ⟨7987929623550363348190741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10650572831400484464254321 7987929623550363348190741)
                  ·
                    refine ⟨374434201103923281946441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7987929623550363348190741 374434201103923281946441)
                    ·
                      refine ⟨280825650827942461459831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 374434201103923281946441 280825650827942461459831)
                      ·
                        rfl

theorem cell23_546906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 2, 6, 2].length) (baseStart_546906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546906 prefixEnd_546906 := by exact prefixLift 546906
  have htrace : WordTrace (prefixWord ++ tailWord_546906) baseStart_546906 baseEnd_546906 := by
    simpa [prefixWord, tailWord_546906, baseEnd_546906] using wordTrace_append hprefix tailTrace_546906
  have hstable : (prefixWord ++ tailWord_546906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546906).length < 2 ^ (prefixWord ++ tailWord_546906).sum := by decide
  have hdescent : baseEnd_546906 < baseStart_546906 := by decide
  rcases family_descends (prefixWord ++ tailWord_546906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546916 : List Nat := [2, 3, 1, 1, 2, 1, 3, 2, 4, 4]
def baseStart_546916 : Nat := 118140960795 + 546916 * 2 ^ 59
def prefixEnd_546916 : Nat := 4983230072969 + 3 ^ 40 * 546916 * 2
def baseEnd_546916 : Nat := 93610261878162474111595

theorem tailTrace_546916 : CollatzResearch.WordTrace tailWord_546916 prefixEnd_546916 93610261878162474111595 := by
  unfold tailWord_546916
  simp only [CollatzResearch.WordTrace]
  refine ⟨9973832643312106330746301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13298443524416141774328401 9973832643312106330746301)
  ·
    refine ⟨3740187241242039874029863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9973832643312106330746301 3740187241242039874029863)
    ·
      refine ⟨5610280861863059811044795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3740187241242039874029863 5610280861863059811044795)
      ·
        refine ⟨8415421292794589716567193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5610280861863059811044795 8415421292794589716567193)
        ·
          refine ⟨6311565969595942287425395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8415421292794589716567193 6311565969595942287425395)
          ·
            refine ⟨9467348954393913431138093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6311565969595942287425395 9467348954393913431138093)
            ·
              refine ⟨3550255857897717536676785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9467348954393913431138093 3550255857897717536676785)
              ·
                refine ⟨2662691893423288152507589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3550255857897717536676785 2662691893423288152507589)
                ·
                  refine ⟨499254730016866528595173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2662691893423288152507589 499254730016866528595173)
                  ·
                    refine ⟨93610261878162474111595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 499254730016866528595173 93610261878162474111595)
                    ·
                      rfl

theorem cell23_546916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_546916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546916 prefixEnd_546916 := by exact prefixLift 546916
  have htrace : WordTrace (prefixWord ++ tailWord_546916) baseStart_546916 baseEnd_546916 := by
    simpa [prefixWord, tailWord_546916, baseEnd_546916] using wordTrace_append hprefix tailTrace_546916
  have hstable : (prefixWord ++ tailWord_546916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546916).length < 2 ^ (prefixWord ++ tailWord_546916).sum := by decide
  have hdescent : baseEnd_546916 < baseStart_546916 := by decide
  rcases family_descends (prefixWord ++ tailWord_546916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546917 : List Nat := [1, 3, 1, 3, 2, 4, 1, 3, 1, 1, 3]
def baseStart_546917 : Nat := 118140960795 + 546917 * 2 ^ 59
def prefixEnd_546917 : Nat := 4983230072969 + 3 ^ 40 * 546917 * 2
def baseEnd_546917 : Nat := 280831299115141918422281

theorem tailTrace_546917 : CollatzResearch.WordTrace tailWord_546917 prefixEnd_546917 280831299115141918422281 := by
  unfold tailWord_546917
  simp only [CollatzResearch.WordTrace]
  refine ⟨19947701759620589832279005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13298467839747059888186003 19947701759620589832279005)
  ·
    refine ⟨7480388159857721187104627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19947701759620589832279005 7480388159857721187104627)
    ·
      refine ⟨11220582239786581780656941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7480388159857721187104627 11220582239786581780656941)
      ·
        refine ⟨4207718339919968167746353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11220582239786581780656941 4207718339919968167746353)
        ·
          refine ⟨3155788754939976125809765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4207718339919968167746353 3155788754939976125809765)
          ·
            refine ⟨591710391551245523589331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3155788754939976125809765 591710391551245523589331)
            ·
              refine ⟨887565587326868285383997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 591710391551245523589331 887565587326868285383997)
              ·
                refine ⟨332837095247575607018999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 887565587326868285383997 332837095247575607018999)
                ·
                  refine ⟨499255642871363410528499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 332837095247575607018999 499255642871363410528499)
                  ·
                    refine ⟨748883464307045115792749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 499255642871363410528499 748883464307045115792749)
                    ·
                      refine ⟨280831299115141918422281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 748883464307045115792749 280831299115141918422281)
                      ·
                        rfl

theorem cell23_546917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_546917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546917 prefixEnd_546917 := by exact prefixLift 546917
  have htrace : WordTrace (prefixWord ++ tailWord_546917) baseStart_546917 baseEnd_546917 := by
    simpa [prefixWord, tailWord_546917, baseEnd_546917] using wordTrace_append hprefix tailTrace_546917
  have hstable : (prefixWord ++ tailWord_546917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546917).length < 2 ^ (prefixWord ++ tailWord_546917).sum := by decide
  have hdescent : baseEnd_546917 < baseStart_546917 := by decide
  rcases family_descends (prefixWord ++ tailWord_546917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546934 : List Nat := [5, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3]
def baseStart_546934 : Nat := 118140960795 + 546934 * 2 ^ 59
def prefixEnd_546934 : Nat := 4983230072969 + 3 ^ 40 * 546934 * 2
def baseEnd_546934 : Nat := 280840028286268351909703

theorem tailTrace_546934 : CollatzResearch.WordTrace tailWord_546934 prefixEnd_546934 280840028286268351909703 := by
  unfold tailWord_546934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1246770112534937608477991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13298881200372667823765237 1246770112534937608477991)
  ·
    refine ⟨1870155168802406412716987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1246770112534937608477991 1870155168802406412716987)
    ·
      refine ⟨2805232753203609619075481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1870155168802406412716987 2805232753203609619075481)
      ·
        refine ⟨2103924564902707214306611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2805232753203609619075481 2103924564902707214306611)
        ·
          refine ⟨3155886847354060821459917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2103924564902707214306611 3155886847354060821459917)
          ·
            refine ⟨1183457567757772808047469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3155886847354060821459917 1183457567757772808047469)
            ·
              refine ⟨443796587909164803017801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1183457567757772808047469 443796587909164803017801)
              ·
                refine ⟨332847440931873602263351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443796587909164803017801 332847440931873602263351)
                ·
                  refine ⟨499271161397810403395027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 332847440931873602263351 499271161397810403395027)
                  ·
                    refine ⟨748906742096715605092541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 499271161397810403395027 748906742096715605092541)
                    ·
                      refine ⟨280840028286268351909703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 748906742096715605092541 280840028286268351909703)
                      ·
                        rfl

theorem cell23_546934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_546934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546934 prefixEnd_546934 := by exact prefixLift 546934
  have htrace : WordTrace (prefixWord ++ tailWord_546934) baseStart_546934 baseEnd_546934 := by
    simpa [prefixWord, tailWord_546934, baseEnd_546934] using wordTrace_append hprefix tailTrace_546934
  have hstable : (prefixWord ++ tailWord_546934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546934).length < 2 ^ (prefixWord ++ tailWord_546934).sum := by decide
  have hdescent : baseEnd_546934 < baseStart_546934 := by decide
  rcases family_descends (prefixWord ++ tailWord_546934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546940 : List Nat := [2, 2, 2, 1, 1, 4, 3, 1, 3, 2, 2]
def baseStart_546940 : Nat := 118140960795 + 546940 * 2 ^ 59
def prefixEnd_546940 : Nat := 4983230072969 + 3 ^ 40 * 546940 * 2
def baseEnd_546940 : Nat := 280843109170195328434675

theorem tailTrace_546940 : CollatzResearch.WordTrace tailWord_546940 prefixEnd_546940 280843109170195328434675 := by
  unfold tailWord_546940
  simp only [CollatzResearch.WordTrace]
  refine ⟨9974270319268632380183137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13299027092358176506910849 9974270319268632380183137)
  ·
    refine ⟨7480702739451474285137353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9974270319268632380183137 7480702739451474285137353)
    ·
      refine ⟨5610527054588605713853015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7480702739451474285137353 5610527054588605713853015)
      ·
        refine ⟨8415790581882908570779523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5610527054588605713853015 8415790581882908570779523)
        ·
          refine ⟨12623685872824362856169285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8415790581882908570779523 12623685872824362856169285)
          ·
            refine ⟨2366941101154568035531741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12623685872824362856169285 2366941101154568035531741)
            ·
              refine ⟨887602912932963013324403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2366941101154568035531741 887602912932963013324403)
              ·
                refine ⟨1331404369399444519986605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 887602912932963013324403 1331404369399444519986605)
                ·
                  refine ⟨499276638524791694994977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1331404369399444519986605 499276638524791694994977)
                  ·
                    refine ⟨374457478893593771246233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 499276638524791694994977 374457478893593771246233)
                    ·
                      refine ⟨280843109170195328434675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 374457478893593771246233 280843109170195328434675)
                      ·
                        rfl

theorem cell23_546940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 3, 2, 2].length) (baseStart_546940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546940 prefixEnd_546940 := by exact prefixLift 546940
  have htrace : WordTrace (prefixWord ++ tailWord_546940) baseStart_546940 baseEnd_546940 := by
    simpa [prefixWord, tailWord_546940, baseEnd_546940] using wordTrace_append hprefix tailTrace_546940
  have hstable : (prefixWord ++ tailWord_546940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546940).length < 2 ^ (prefixWord ++ tailWord_546940).sum := by decide
  have hdescent : baseEnd_546940 < baseStart_546940 := by decide
  rcases family_descends (prefixWord ++ tailWord_546940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546969 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 1, 4, 5]
def baseStart_546969 : Nat := 118140960795 + 546969 * 2 ^ 59
def prefixEnd_546969 : Nat := 4983230072969 + 3 ^ 40 * 546969 * 2
def baseEnd_546969 : Nat := 280858000109175714972041

theorem tailTrace_546969 : CollatzResearch.WordTrace tailWord_546969 prefixEnd_546969 280858000109175714972041 := by
  unfold tailWord_546969
  simp only [CollatzResearch.WordTrace]
  refine ⟨19949598355432202713171961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13299732236954801808781307 19949598355432202713171961)
  ·
    refine ⟨14962198766574152034878971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19949598355432202713171961 14962198766574152034878971)
    ·
      refine ⟨22443298149861228052318457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14962198766574152034878971 22443298149861228052318457)
      ·
        refine ⟨16832473612395921039238843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22443298149861228052318457 16832473612395921039238843)
        ·
          refine ⟨25248710418593881558858265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16832473612395921039238843 25248710418593881558858265)
          ·
            refine ⟨18936532813945411169143699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25248710418593881558858265 18936532813945411169143699)
            ·
              refine ⟨28404799220918116753715549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18936532813945411169143699 28404799220918116753715549)
              ·
                refine ⟨10651799707844293782643331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28404799220918116753715549 10651799707844293782643331)
                ·
                  refine ⟨15977699561766440673964997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10651799707844293782643331 15977699561766440673964997)
                  ·
                    refine ⟨2995818667831207626368437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15977699561766440673964997 2995818667831207626368437)
                    ·
                      refine ⟨280858000109175714972041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2995818667831207626368437 280858000109175714972041)
                      ·
                        rfl

theorem cell23_546969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_546969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546969 prefixEnd_546969 := by exact prefixLift 546969
  have htrace : WordTrace (prefixWord ++ tailWord_546969) baseStart_546969 baseEnd_546969 := by
    simpa [prefixWord, tailWord_546969, baseEnd_546969] using wordTrace_append hprefix tailTrace_546969
  have hstable : (prefixWord ++ tailWord_546969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546969).length < 2 ^ (prefixWord ++ tailWord_546969).sum := by decide
  have hdescent : baseEnd_546969 < baseStart_546969 := by decide
  rcases family_descends (prefixWord ++ tailWord_546969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546973 : List Nat := [1, 4, 2, 1, 1, 4, 1, 2, 1, 3, 3]
def baseStart_546973 : Nat := 118140960795 + 546973 * 2 ^ 59
def prefixEnd_546973 : Nat := 4983230072969 + 3 ^ 40 * 546973 * 2
def baseEnd_546973 : Nat := 280860054031793699322023

theorem tailTrace_546973 : CollatzResearch.WordTrace tailWord_546973 prefixEnd_546973 280860054031793699322023 := by
  unfold tailWord_546973
  simp only [CollatzResearch.WordTrace]
  refine ⟨19949744247417711396317573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13299829498278474264211715 19949744247417711396317573)
  ·
    refine ⟨3740577046390820886809545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19949744247417711396317573 3740577046390820886809545)
    ·
      refine ⟨2805432784793115665107159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3740577046390820886809545 2805432784793115665107159)
      ·
        refine ⟨4208149177189673497660739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2805432784793115665107159 4208149177189673497660739)
        ·
          refine ⟨6312223765784510246491109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4208149177189673497660739 6312223765784510246491109)
          ·
            refine ⟨1183541956084595671217083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6312223765784510246491109 1183541956084595671217083)
            ·
              refine ⟨1775312934126893506825625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1183541956084595671217083 1775312934126893506825625)
              ·
                refine ⟨1331484700595170130119219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1775312934126893506825625 1331484700595170130119219)
                ·
                  refine ⟨1997227050892755195178829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1331484700595170130119219 1997227050892755195178829)
                  ·
                    refine ⟨748960144084783198192061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1997227050892755195178829 748960144084783198192061)
                    ·
                      refine ⟨280860054031793699322023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 748960144084783198192061 280860054031793699322023)
                      ·
                        rfl

theorem cell23_546973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_546973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_546973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_546973 prefixEnd_546973 := by exact prefixLift 546973
  have htrace : WordTrace (prefixWord ++ tailWord_546973) baseStart_546973 baseEnd_546973 := by
    simpa [prefixWord, tailWord_546973, baseEnd_546973] using wordTrace_append hprefix tailTrace_546973
  have hstable : (prefixWord ++ tailWord_546973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546973).length < 2 ^ (prefixWord ++ tailWord_546973).sum := by decide
  have hdescent : baseEnd_546973 < baseStart_546973 := by decide
  rcases family_descends (prefixWord ++ tailWord_546973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547013 : List Nat := [1, 3, 1, 1, 1, 1, 5, 3, 1, 4, 2]
def baseStart_547013 : Nat := 118140960795 + 547013 * 2 ^ 59
def prefixEnd_547013 : Nat := 4983230072969 + 3 ^ 40 * 547013 * 2
def baseEnd_547013 : Nat := 280880593257973542821839

theorem tailTrace_547013 : CollatzResearch.WordTrace tailWord_547013 prefixEnd_547013 280880593257973542821839 := by
  unfold tailWord_547013
  simp only [CollatzResearch.WordTrace]
  refine ⟨19951203167272798227773693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13300802111515198818515795 19951203167272798227773693)
  ·
    refine ⟨7481701187727299335415135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19951203167272798227773693 7481701187727299335415135)
    ·
      refine ⟨11222551781590949003122703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7481701187727299335415135 11222551781590949003122703)
      ·
        refine ⟨16833827672386423504684055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11222551781590949003122703 16833827672386423504684055)
        ·
          refine ⟨25250741508579635257026083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16833827672386423504684055 25250741508579635257026083)
          ·
            refine ⟨37876112262869452885539125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25250741508579635257026083 37876112262869452885539125)
            ·
              refine ⟨3550885524644011208019293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37876112262869452885539125 3550885524644011208019293)
              ·
                refine ⟨1331582071741504203007235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3550885524644011208019293 1331582071741504203007235)
                ·
                  refine ⟨1997373107612256304510853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1331582071741504203007235 1997373107612256304510853)
                  ·
                    refine ⟨374507457677298057095785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1997373107612256304510853 374507457677298057095785)
                    ·
                      refine ⟨280880593257973542821839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 374507457677298057095785 280880593257973542821839)
                      ·
                        rfl

theorem cell23_547013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 1, 4, 2].length) (baseStart_547013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547013 prefixEnd_547013 := by exact prefixLift 547013
  have htrace : WordTrace (prefixWord ++ tailWord_547013) baseStart_547013 baseEnd_547013 := by
    simpa [prefixWord, tailWord_547013, baseEnd_547013] using wordTrace_append hprefix tailTrace_547013
  have hstable : (prefixWord ++ tailWord_547013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547013).length < 2 ^ (prefixWord ++ tailWord_547013).sum := by decide
  have hdescent : baseEnd_547013 < baseStart_547013 := by decide
  rcases family_descends (prefixWord ++ tailWord_547013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547016 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 4, 4, 3]
def baseStart_547016 : Nat := 118140960795 + 547016 * 2 ^ 59
def prefixEnd_547016 : Nat := 4983230072969 + 3 ^ 40 * 547016 * 2
def baseEnd_547016 : Nat := 280882133699937031084325

theorem tailTrace_547016 : CollatzResearch.WordTrace tailWord_547016 prefixEnd_547016 280882133699937031084325 := by
  unfold tailWord_547016
  simp only [CollatzResearch.WordTrace]
  refine ⟨9975656293130964870066451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13300875057507953160088601 9975656293130964870066451)
  ·
    refine ⟨14963484439696447305099677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9975656293130964870066451 14963484439696447305099677)
    ·
      refine ⟨5611306664886167739412379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14963484439696447305099677 5611306664886167739412379)
      ·
        refine ⟨8416959997329251609118569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5611306664886167739412379 8416959997329251609118569)
        ·
          refine ⟨6312719997996938706838927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8416959997329251609118569 6312719997996938706838927)
          ·
            refine ⟨9469079996995408060258391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6312719997996938706838927 9469079996995408060258391)
            ·
              refine ⟨14203619995493112090387587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9469079996995408060258391 14203619995493112090387587)
              ·
                refine ⟨21305429993239668135581381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14203619995493112090387587 21305429993239668135581381)
                ·
                  refine ⟨3994768123732437775421509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21305429993239668135581381 3994768123732437775421509)
                  ·
                    refine ⟨749019023199832082891533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3994768123732437775421509 749019023199832082891533)
                    ·
                      refine ⟨280882133699937031084325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 749019023199832082891533 280882133699937031084325)
                      ·
                        rfl

theorem cell23_547016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_547016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547016 prefixEnd_547016 := by exact prefixLift 547016
  have htrace : WordTrace (prefixWord ++ tailWord_547016) baseStart_547016 baseEnd_547016 := by
    simpa [prefixWord, tailWord_547016, baseEnd_547016] using wordTrace_append hprefix tailTrace_547016
  have hstable : (prefixWord ++ tailWord_547016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547016).length < 2 ^ (prefixWord ++ tailWord_547016).sum := by decide
  have hdescent : baseEnd_547016 < baseStart_547016 := by decide
  rcases family_descends (prefixWord ++ tailWord_547016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547047 : List Nat := [1, 1, 5, 3, 1, 2, 1, 1, 4, 2, 2]
def baseStart_547047 : Nat := 118140960795 + 547047 * 2 ^ 59
def prefixEnd_547047 : Nat := 4983230072969 + 3 ^ 40 * 547047 * 2
def baseEnd_547047 : Nat := 280898051600226409796683

theorem tailTrace_547047 : CollatzResearch.WordTrace tailWord_547047 prefixEnd_547047 280898051600226409796683 := by
  unfold tailWord_547047
  simp only [CollatzResearch.WordTrace]
  refine ⟨19952443249149622034511395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13301628832766414689674263 19952443249149622034511395)
  ·
    refine ⟨29928664873724433051767093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19952443249149622034511395 29928664873724433051767093)
    ·
      refine ⟨2805812331911665598603165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29928664873724433051767093 2805812331911665598603165)
      ·
        refine ⟨1052179624466874599476187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2805812331911665598603165 1052179624466874599476187)
        ·
          refine ⟨1578269436700311899214281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1052179624466874599476187 1578269436700311899214281)
          ·
            refine ⟨1183702077525233924410711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1578269436700311899214281 1183702077525233924410711)
            ·
              refine ⟨1775553116287850886616067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1183702077525233924410711 1775553116287850886616067)
              ·
                refine ⟨2663329674431776329924101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1775553116287850886616067 2663329674431776329924101)
                ·
                  refine ⟨499374313955958061860769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2663329674431776329924101 499374313955958061860769)
                  ·
                    refine ⟨374530735466968546395577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 499374313955958061860769 374530735466968546395577)
                    ·
                      refine ⟨280898051600226409796683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 374530735466968546395577 280898051600226409796683)
                      ·
                        rfl

theorem cell23_547047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_547047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547047 prefixEnd_547047 := by exact prefixLift 547047
  have htrace : WordTrace (prefixWord ++ tailWord_547047) baseStart_547047 baseEnd_547047 := by
    simpa [prefixWord, tailWord_547047, baseEnd_547047] using wordTrace_append hprefix tailTrace_547047
  have hstable : (prefixWord ++ tailWord_547047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547047).length < 2 ^ (prefixWord ++ tailWord_547047).sum := by decide
  have hdescent : baseEnd_547047 < baseStart_547047 := by decide
  rcases family_descends (prefixWord ++ tailWord_547047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547066 : List Nat := [3, 1, 1, 1, 1, 5, 1, 2, 1, 7]
def baseStart_547066 : Nat := 118140960795 + 547066 * 2 ^ 59
def prefixEnd_547066 : Nat := 4983230072969 + 3 ^ 40 * 547066 * 2
def baseEnd_547066 : Nat := 93635935910887278486365

theorem tailTrace_547066 : CollatzResearch.WordTrace tailWord_547066 prefixEnd_547066 93635935910887278486365 := by
  unfold tailWord_547066
  simp only [CollatzResearch.WordTrace]
  refine ⟨4988284059020197069863263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13302090824053858852968701 4988284059020197069863263)
  ·
    refine ⟨7482426088530295604794895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4988284059020197069863263 7482426088530295604794895)
    ·
      refine ⟨11223639132795443407192343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7482426088530295604794895 11223639132795443407192343)
      ·
        refine ⟨16835458699193165110788515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11223639132795443407192343 16835458699193165110788515)
        ·
          refine ⟨25253188048789747666182773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16835458699193165110788515 25253188048789747666182773)
          ·
            refine ⟨2367486379574038843704635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25253188048789747666182773 2367486379574038843704635)
            ·
              refine ⟨3551229569361058265556953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2367486379574038843704635 3551229569361058265556953)
              ·
                refine ⟨2663422177020793699167715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3551229569361058265556953 2663422177020793699167715)
                ·
                  refine ⟨3995133265531190548751573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2663422177020793699167715 3995133265531190548751573)
                  ·
                    refine ⟨93635935910887278486365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3995133265531190548751573 93635935910887278486365)
                    ·
                      rfl

theorem cell23_547066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 1, 7].length) (baseStart_547066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547066 prefixEnd_547066 := by exact prefixLift 547066
  have htrace : WordTrace (prefixWord ++ tailWord_547066) baseStart_547066 baseEnd_547066 := by
    simpa [prefixWord, tailWord_547066, baseEnd_547066] using wordTrace_append hprefix tailTrace_547066
  have hstable : (prefixWord ++ tailWord_547066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547066).length < 2 ^ (prefixWord ++ tailWord_547066).sum := by decide
  have hdescent : baseEnd_547066 < baseStart_547066 := by decide
  rcases family_descends (prefixWord ++ tailWord_547066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547103 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 4]
def baseStart_547103 : Nat := 118140960795 + 547103 * 2 ^ 59
def prefixEnd_547103 : Nat := 4983230072969 + 3 ^ 40 * 547103 * 2
def baseEnd_547103 : Nat := 280926806516878190696425

theorem tailTrace_547103 : CollatzResearch.WordTrace tailWord_547103 prefixEnd_547103 280926806516878190696425 := by
  unfold tailWord_547103
  simp only [CollatzResearch.WordTrace]
  refine ⟨19954485736946743598549963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13302990491297829065699975 19954485736946743598549963)
  ·
    refine ⟨29931728605420115397824945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19954485736946743598549963 29931728605420115397824945)
    ·
      refine ⟨22448796454065086548368709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29931728605420115397824945 22448796454065086548368709)
      ·
        refine ⟨4209149335137203727819133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22448796454065086548368709 4209149335137203727819133)
        ·
          refine ⟨1578431000676451397932175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4209149335137203727819133 1578431000676451397932175)
          ·
            refine ⟨2367646501014677096898263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1578431000676451397932175 2367646501014677096898263)
            ·
              refine ⟨3551469751522015645347395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2367646501014677096898263 3551469751522015645347395)
              ·
                refine ⟨5327204627283023468021093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3551469751522015645347395 5327204627283023468021093)
                ·
                  refine ⟨998850867615566900253955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5327204627283023468021093 998850867615566900253955)
                  ·
                    refine ⟨1498276301423350350380933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 998850867615566900253955 1498276301423350350380933)
                    ·
                      refine ⟨280926806516878190696425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1498276301423350350380933 280926806516878190696425)
                      ·
                        rfl

theorem cell23_547103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_547103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547103 prefixEnd_547103 := by exact prefixLift 547103
  have htrace : WordTrace (prefixWord ++ tailWord_547103) baseStart_547103 baseEnd_547103 := by
    simpa [prefixWord, tailWord_547103, baseEnd_547103] using wordTrace_append hprefix tailTrace_547103
  have hstable : (prefixWord ++ tailWord_547103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547103).length < 2 ^ (prefixWord ++ tailWord_547103).sum := by decide
  have hdescent : baseEnd_547103 < baseStart_547103 := by decide
  rcases family_descends (prefixWord ++ tailWord_547103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547116 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 6]
def baseStart_547116 : Nat := 118140960795 + 547116 * 2 ^ 59
def prefixEnd_547116 : Nat := 4983230072969 + 3 ^ 40 * 547116 * 2
def baseEnd_547116 : Nat := 280933481765386639833865

theorem tailTrace_547116 : CollatzResearch.WordTrace tailWord_547116 prefixEnd_547116 280933481765386639833865 := by
  unfold tailWord_547116
  simp only [CollatzResearch.WordTrace]
  refine ⟨9977479942949823409386601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13303306590599764545848801 9977479942949823409386601)
  ·
    refine ⟨7483109957212367557039951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9977479942949823409386601 7483109957212367557039951)
    ·
      refine ⟨11224664935818551335559927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7483109957212367557039951 11224664935818551335559927)
      ·
        refine ⟨16836997403727827003339891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11224664935818551335559927 16836997403727827003339891)
        ·
          refine ⟨25255496105591740505009837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16836997403727827003339891 25255496105591740505009837)
          ·
            refine ⟨9470811039596902689378689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25255496105591740505009837 9470811039596902689378689)
            ·
              refine ⟨7103108279697677017034017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9470811039596902689378689 7103108279697677017034017)
              ·
                refine ⟨5327331209773257762775513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7103108279697677017034017 5327331209773257762775513)
                ·
                  refine ⟨3995498407329943322081635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5327331209773257762775513 3995498407329943322081635)
                  ·
                    refine ⟨5993247610994914983122453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3995498407329943322081635 5993247610994914983122453)
                    ·
                      refine ⟨280933481765386639833865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5993247610994914983122453 280933481765386639833865)
                      ·
                        rfl

theorem cell23_547116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_547116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547116 prefixEnd_547116 := by exact prefixLift 547116
  have htrace : WordTrace (prefixWord ++ tailWord_547116) baseStart_547116 baseEnd_547116 := by
    simpa [prefixWord, tailWord_547116, baseEnd_547116] using wordTrace_append hprefix tailTrace_547116
  have hstable : (prefixWord ++ tailWord_547116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547116).length < 2 ^ (prefixWord ++ tailWord_547116).sum := by decide
  have hdescent : baseEnd_547116 < baseStart_547116 := by decide
  rcases family_descends (prefixWord ++ tailWord_547116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547123 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 4, 2, 3]
def baseStart_547123 : Nat := 118140960795 + 547123 * 2 ^ 59
def prefixEnd_547123 : Nat := 4983230072969 + 3 ^ 40 * 547123 * 2
def baseEnd_547123 : Nat := 280937076129968112446333

theorem tailTrace_547123 : CollatzResearch.WordTrace tailWord_547123 prefixEnd_547123 280937076129968112446333 := by
  unfold tailWord_547123
  simp only [CollatzResearch.WordTrace]
  refine ⟨19955215196874287014278023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13303476797916191342852015 19955215196874287014278023)
  ·
    refine ⟨29932822795311430521417035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19955215196874287014278023 29932822795311430521417035)
    ·
      refine ⟨44899234192967145782125553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29932822795311430521417035 44899234192967145782125553)
      ·
        refine ⟨33674425644725359336594165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44899234192967145782125553 33674425644725359336594165)
        ·
          refine ⟨3156977404193002437805703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33674425644725359336594165 3156977404193002437805703)
          ·
            refine ⟨4735466106289503656708555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3156977404193002437805703 4735466106289503656708555)
            ·
              refine ⟨7103199159434255485062833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4735466106289503656708555 7103199159434255485062833)
              ·
                refine ⟨5327399369575691613797125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7103199159434255485062833 5327399369575691613797125)
                ·
                  refine ⟨998887381795442177586961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5327399369575691613797125 998887381795442177586961)
                  ·
                    refine ⟨749165536346581633190221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 998887381795442177586961 749165536346581633190221)
                    ·
                      refine ⟨280937076129968112446333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 749165536346581633190221 280937076129968112446333)
                      ·
                        rfl

theorem cell23_547123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 4, 2, 3].length) (baseStart_547123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547123 prefixEnd_547123 := by exact prefixLift 547123
  have htrace : WordTrace (prefixWord ++ tailWord_547123) baseStart_547123 baseEnd_547123 := by
    simpa [prefixWord, tailWord_547123, baseEnd_547123] using wordTrace_append hprefix tailTrace_547123
  have hstable : (prefixWord ++ tailWord_547123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547123).length < 2 ^ (prefixWord ++ tailWord_547123).sum := by decide
  have hdescent : baseEnd_547123 < baseStart_547123 := by decide
  rcases family_descends (prefixWord ++ tailWord_547123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547137 : List Nat := [1, 2, 5, 2, 2, 1, 2, 1, 2, 1, 4]
def baseStart_547137 : Nat := 118140960795 + 547137 * 2 ^ 59
def prefixEnd_547137 : Nat := 4983230072969 + 3 ^ 40 * 547137 * 2
def baseEnd_547137 : Nat := 280944264859131057671269

theorem tailTrace_547137 : CollatzResearch.WordTrace tailWord_547137 prefixEnd_547137 280944264859131057671269 := by
  unfold tailWord_547137
  simp only [CollatzResearch.WordTrace]
  refine ⟨19955725818823567405287665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13303817212549044936858443 19955725818823567405287665)
  ·
    refine ⟨14966794364117675553965749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19955725818823567405287665 14966794364117675553965749)
    ·
      refine ⟨1403136971636032083184289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14966794364117675553965749 1403136971636032083184289)
      ·
        refine ⟨1052352728727024062388217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1403136971636032083184289 1052352728727024062388217)
        ·
          refine ⟨789264546545268046791163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1052352728727024062388217 789264546545268046791163)
          ·
            refine ⟨1183896819817902070186745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 789264546545268046791163 1183896819817902070186745)
            ·
              refine ⟨887922614863426552640059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1183896819817902070186745 887922614863426552640059)
              ·
                refine ⟨1331883922295139828960089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 887922614863426552640059 1331883922295139828960089)
                ·
                  refine ⟨998912941721354871720067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1331883922295139828960089 998912941721354871720067)
                  ·
                    refine ⟨1498369412582032307580101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 998912941721354871720067 1498369412582032307580101)
                    ·
                      refine ⟨280944264859131057671269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1498369412582032307580101 280944264859131057671269)
                      ·
                        rfl

theorem cell23_547137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_547137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547137 prefixEnd_547137 := by exact prefixLift 547137
  have htrace : WordTrace (prefixWord ++ tailWord_547137) baseStart_547137 baseEnd_547137 := by
    simpa [prefixWord, tailWord_547137, baseEnd_547137] using wordTrace_append hprefix tailTrace_547137
  have hstable : (prefixWord ++ tailWord_547137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547137).length < 2 ^ (prefixWord ++ tailWord_547137).sum := by decide
  have hdescent : baseEnd_547137 < baseStart_547137 := by decide
  rcases family_descends (prefixWord ++ tailWord_547137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547146 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 8]
def baseStart_547146 : Nat := 118140960795 + 547146 * 2 ^ 59
def prefixEnd_547146 : Nat := 4983230072969 + 3 ^ 40 * 547146 * 2
def baseEnd_547146 : Nat := 280948886185021522458727

theorem tailTrace_547146 : CollatzResearch.WordTrace tailWord_547146 prefixEnd_547146 280948886185021522458727 := by
  unfold tailWord_547146
  simp only [CollatzResearch.WordTrace]
  refine ⟨4989013518947740485591323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13304036050527307961576861 4989013518947740485591323)
  ·
    refine ⟨7483520278421610728386985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4989013518947740485591323 7483520278421610728386985)
    ·
      refine ⟨5612640208816208046290239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7483520278421610728386985 5612640208816208046290239)
      ·
        refine ⟨8418960313224312069435359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5612640208816208046290239 8418960313224312069435359)
        ·
          refine ⟨12628440469836468104153039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8418960313224312069435359 12628440469836468104153039)
          ·
            refine ⟨18942660704754702156229559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12628440469836468104153039 18942660704754702156229559)
            ·
              refine ⟨28413991057132053234344339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18942660704754702156229559 28413991057132053234344339)
              ·
                refine ⟨42620986585698079851516509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28413991057132053234344339 42620986585698079851516509)
                ·
                  refine ⟨15982869969636779944318691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42620986585698079851516509 15982869969636779944318691)
                  ·
                    refine ⟨23974304954455169916478037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15982869969636779944318691 23974304954455169916478037)
                    ·
                      refine ⟨280948886185021522458727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 23974304954455169916478037 280948886185021522458727)
                      ·
                        rfl

theorem cell23_547146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_547146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547146 prefixEnd_547146 := by exact prefixLift 547146
  have htrace : WordTrace (prefixWord ++ tailWord_547146) baseStart_547146 baseEnd_547146 := by
    simpa [prefixWord, tailWord_547146, baseEnd_547146] using wordTrace_append hprefix tailTrace_547146
  have hstable : (prefixWord ++ tailWord_547146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547146).length < 2 ^ (prefixWord ++ tailWord_547146).sum := by decide
  have hdescent : baseEnd_547146 < baseStart_547146 := by decide
  rcases family_descends (prefixWord ++ tailWord_547146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547173 : List Nat := [1, 3, 1, 3, 1, 3, 1, 2, 3, 5]
def baseStart_547173 : Nat := 118140960795 + 547173 * 2 ^ 59
def prefixEnd_547173 : Nat := 4983230072969 + 3 ^ 40 * 547173 * 2
def baseEnd_547173 : Nat := 93654250054230972273701

theorem tailTrace_547173 : CollatzResearch.WordTrace tailWord_547173 prefixEnd_547173 93654250054230972273701 := by
  unfold tailWord_547173
  simp only [CollatzResearch.WordTrace]
  refine ⟨19957038846693145553598173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13304692564462097035732115 19957038846693145553598173)
  ·
    refine ⟨7483889567509929582599315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19957038846693145553598173 7483889567509929582599315)
    ·
      refine ⟨11225834351264894373898973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7483889567509929582599315 11225834351264894373898973)
      ·
        refine ⟨4209687881724335390212115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11225834351264894373898973 4209687881724335390212115)
        ·
          refine ⟨6314531822586503085318173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4209687881724335390212115 6314531822586503085318173)
          ·
            refine ⟨2367949433469938656994315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6314531822586503085318173 2367949433469938656994315)
            ·
              refine ⟨3551924150204907985491473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2367949433469938656994315 3551924150204907985491473)
              ·
                refine ⟨2663943112653680989118605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3551924150204907985491473 2663943112653680989118605)
                ·
                  refine ⟨998978667245130370919477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2663943112653680989118605 998978667245130370919477)
                  ·
                    refine ⟨93654250054230972273701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 998978667245130370919477 93654250054230972273701)
                    ·
                      rfl

theorem cell23_547173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 5].length) (baseStart_547173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547173 prefixEnd_547173 := by exact prefixLift 547173
  have htrace : WordTrace (prefixWord ++ tailWord_547173) baseStart_547173 baseEnd_547173 := by
    simpa [prefixWord, tailWord_547173, baseEnd_547173] using wordTrace_append hprefix tailTrace_547173
  have hstable : (prefixWord ++ tailWord_547173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547173).length < 2 ^ (prefixWord ++ tailWord_547173).sum := by decide
  have hdescent : baseEnd_547173 < baseStart_547173 := by decide
  rcases family_descends (prefixWord ++ tailWord_547173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547197 : List Nat := [1, 4, 1, 1, 2, 3, 3, 1, 2, 3, 2]
def baseStart_547197 : Nat := 118140960795 + 547197 * 2 ^ 59
def prefixEnd_547197 : Nat := 4983230072969 + 3 ^ 40 * 547197 * 2
def baseEnd_547197 : Nat := 280975073698400822920993

theorem tailTrace_547197 : CollatzResearch.WordTrace tailWord_547197 prefixEnd_547197 280975073698400822920993 := by
  unfold tailWord_547197
  simp only [CollatzResearch.WordTrace]
  refine ⟨19957914198606197652471845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13305276132404131768314563 19957914198606197652471845)
  ·
    refine ⟨3742108912238662059838471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19957914198606197652471845 3742108912238662059838471)
    ·
      refine ⟨5613163368357993089757707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3742108912238662059838471 5613163368357993089757707)
      ·
        refine ⟨8419745052536989634636561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5613163368357993089757707 8419745052536989634636561)
        ·
          refine ⟨6314808789402742225977421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8419745052536989634636561 6314808789402742225977421)
          ·
            refine ⟨2368053296026028334741533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6314808789402742225977421 2368053296026028334741533)
            ·
              refine ⟨888019986009760625528075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2368053296026028334741533 888019986009760625528075)
              ·
                refine ⟨1332029979014640938292113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 888019986009760625528075 1332029979014640938292113)
                ·
                  refine ⟨999022484260980703719085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1332029979014640938292113 999022484260980703719085)
                  ·
                    refine ⟨374633431597867763894657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 999022484260980703719085 374633431597867763894657)
                    ·
                      refine ⟨280975073698400822920993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 374633431597867763894657 280975073698400822920993)
                      ·
                        rfl

theorem cell23_547197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 3, 2].length) (baseStart_547197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547197 prefixEnd_547197 := by exact prefixLift 547197
  have htrace : WordTrace (prefixWord ++ tailWord_547197) baseStart_547197 baseEnd_547197 := by
    simpa [prefixWord, tailWord_547197, baseEnd_547197] using wordTrace_append hprefix tailTrace_547197
  have hstable : (prefixWord ++ tailWord_547197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547197).length < 2 ^ (prefixWord ++ tailWord_547197).sum := by decide
  have hdescent : baseEnd_547197 < baseStart_547197 := by decide
  rcases family_descends (prefixWord ++ tailWord_547197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547204 : List Nat := [2, 3, 2, 1, 1, 2, 4, 3, 1, 1, 3]
def baseStart_547204 : Nat := 118140960795 + 547204 * 2 ^ 59
def prefixEnd_547204 : Nat := 4983230072969 + 3 ^ 40 * 547204 * 2
def baseEnd_547204 : Nat := 280978668062982295533461

theorem tailTrace_547204 : CollatzResearch.WordTrace tailWord_547204 prefixEnd_547204 280978668062982295533461 := by
  unfold tailWord_547204
  simp only [CollatzResearch.WordTrace]
  refine ⟨9979084754790418923988333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13305446339720558565317777 9979084754790418923988333)
  ·
    refine ⟨3742156783046407096495625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9979084754790418923988333 3742156783046407096495625)
    ·
      refine ⟨2806617587284805322371719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3742156783046407096495625 2806617587284805322371719)
      ·
        refine ⟨4209926380927207983557579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2806617587284805322371719 4209926380927207983557579)
        ·
          refine ⟨6314889571390811975336369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4209926380927207983557579 6314889571390811975336369)
          ·
            refine ⟨4736167178543108981502277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6314889571390811975336369 4736167178543108981502277)
            ·
              refine ⟨888031345976832934031677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4736167178543108981502277 888031345976832934031677)
              ·
                refine ⟨333011754741312350261879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 888031345976832934031677 333011754741312350261879)
                ·
                  refine ⟨499517632111968525392819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 333011754741312350261879 499517632111968525392819)
                  ·
                    refine ⟨749276448167952788089229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 499517632111968525392819 749276448167952788089229)
                    ·
                      refine ⟨280978668062982295533461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 749276448167952788089229 280978668062982295533461)
                      ·
                        rfl

theorem cell23_547204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_547204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547204 prefixEnd_547204 := by exact prefixLift 547204
  have htrace : WordTrace (prefixWord ++ tailWord_547204) baseStart_547204 baseEnd_547204 := by
    simpa [prefixWord, tailWord_547204, baseEnd_547204] using wordTrace_append hprefix tailTrace_547204
  have hstable : (prefixWord ++ tailWord_547204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547204).length < 2 ^ (prefixWord ++ tailWord_547204).sum := by decide
  have hdescent : baseEnd_547204 < baseStart_547204 := by decide
  rcases family_descends (prefixWord ++ tailWord_547204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547223 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 4]
def baseStart_547223 : Nat := 118140960795 + 547223 * 2 ^ 59
def prefixEnd_547223 : Nat := 4983230072969 + 3 ^ 40 * 547223 * 2
def baseEnd_547223 : Nat := 280988424195417721195873

theorem tailTrace_547223 : CollatzResearch.WordTrace tailWord_547223 prefixEnd_547223 280988424195417721195873 := by
  unfold tailWord_547223
  simp only [CollatzResearch.WordTrace]
  refine ⟨19958862496512004092918323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13305908331008002728612215 19958862496512004092918323)
  ·
    refine ⟨29938293744768006139377485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19958862496512004092918323 29938293744768006139377485)
    ·
      refine ⟨11226860154288002302266557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29938293744768006139377485 11226860154288002302266557)
      ·
        refine ⟨4210072557858000863349959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11226860154288002302266557 4210072557858000863349959)
        ·
          refine ⟨6315108836787001295024939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4210072557858000863349959 6315108836787001295024939)
          ·
            refine ⟨9472663255180501942537409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6315108836787001295024939 9472663255180501942537409)
            ·
              refine ⟨7104497441385376456903057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9472663255180501942537409 7104497441385376456903057)
              ·
                refine ⟨5328373081039032342677293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7104497441385376456903057 5328373081039032342677293)
                ·
                  refine ⟨1998139905389637128503985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5328373081039032342677293 1998139905389637128503985)
                  ·
                    refine ⟨1498604929042227846377989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1998139905389637128503985 1498604929042227846377989)
                    ·
                      refine ⟨280988424195417721195873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1498604929042227846377989 280988424195417721195873)
                      ·
                        rfl

theorem cell23_547223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_547223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547223 prefixEnd_547223 := by exact prefixLift 547223
  have htrace : WordTrace (prefixWord ++ tailWord_547223) baseStart_547223 baseEnd_547223 := by
    simpa [prefixWord, tailWord_547223, baseEnd_547223] using wordTrace_append hprefix tailTrace_547223
  have hstable : (prefixWord ++ tailWord_547223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547223).length < 2 ^ (prefixWord ++ tailWord_547223).sum := by decide
  have hdescent : baseEnd_547223 < baseStart_547223 := by decide
  rcases family_descends (prefixWord ++ tailWord_547223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547237 : List Nat := [1, 3, 1, 2, 1, 1, 7, 1, 2, 4]
def baseStart_547237 : Nat := 118140960795 + 547237 * 2 ^ 59
def prefixEnd_547237 : Nat := 4983230072969 + 3 ^ 40 * 547237 * 2
def baseEnd_547237 : Nat := 93665204308193555473603

theorem tailTrace_547237 : CollatzResearch.WordTrace tailWord_547237 prefixEnd_547237 93665204308193555473603 := by
  unfold tailWord_547237
  simp only [CollatzResearch.WordTrace]
  refine ⟨19959373118461284483927965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13306248745640856322618643 19959373118461284483927965)
  ·
    refine ⟨7484764919422981681472987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19959373118461284483927965 7484764919422981681472987)
    ·
      refine ⟨11227147379134472522209481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7484764919422981681472987 11227147379134472522209481)
      ·
        refine ⟨8420360534350854391657111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11227147379134472522209481 8420360534350854391657111)
        ·
          refine ⟨12630540801526281587485667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8420360534350854391657111 12630540801526281587485667)
          ·
            refine ⟨18945811202289422381228501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12630540801526281587485667 18945811202289422381228501)
            ·
              refine ⟨444042450053658337060043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 18945811202289422381228501 444042450053658337060043)
              ·
                refine ⟨666063675080487505590065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 444042450053658337060043 666063675080487505590065)
                ·
                  refine ⟨499547756310365629192549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 666063675080487505590065 499547756310365629192549)
                  ·
                    refine ⟨93665204308193555473603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 499547756310365629192549 93665204308193555473603)
                    ·
                      rfl

theorem cell23_547237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 2, 4].length) (baseStart_547237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547237 prefixEnd_547237 := by exact prefixLift 547237
  have htrace : WordTrace (prefixWord ++ tailWord_547237) baseStart_547237 baseEnd_547237 := by
    simpa [prefixWord, tailWord_547237, baseEnd_547237] using wordTrace_append hprefix tailTrace_547237
  have hstable : (prefixWord ++ tailWord_547237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547237).length < 2 ^ (prefixWord ++ tailWord_547237).sum := by decide
  have hdescent : baseEnd_547237 < baseStart_547237 := by decide
  rcases family_descends (prefixWord ++ tailWord_547237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547261 : List Nat := [1, 4, 1, 2, 2, 2, 3, 3, 1, 2, 2]
def baseStart_547261 : Nat := 118140960795 + 547261 * 2 ^ 59
def prefixEnd_547261 : Nat := 4983230072969 + 3 ^ 40 * 547261 * 2
def baseEnd_547261 : Nat := 281007936460288572520699

theorem tailTrace_547261 : CollatzResearch.WordTrace tailWord_547261 prefixEnd_547261 281007936460288572520699 := by
  unfold tailWord_547261
  simp only [CollatzResearch.WordTrace]
  refine ⟨19960248470374336582801637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13306832313582891055201091 19960248470374336582801637)
  ·
    refine ⟨3742546588195188109275307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19960248470374336582801637 3742546588195188109275307)
    ·
      refine ⟨5613819882292782163912961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3742546588195188109275307 5613819882292782163912961)
      ·
        refine ⟨4210364911719586622934721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5613819882292782163912961 4210364911719586622934721)
        ·
          refine ⟨3157773683789689967201041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4210364911719586622934721 3157773683789689967201041)
          ·
            refine ⟨2368330262842267475400781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3157773683789689967201041 2368330262842267475400781)
            ·
              refine ⟨888123848565850303275293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2368330262842267475400781 888123848565850303275293)
              ·
                refine ⟨333046443212193863728235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 888123848565850303275293 333046443212193863728235)
                ·
                  refine ⟨499569664818290795592353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 333046443212193863728235 499569664818290795592353)
                  ·
                    refine ⟨374677248613718096694265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 499569664818290795592353 374677248613718096694265)
                    ·
                      refine ⟨281007936460288572520699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 374677248613718096694265 281007936460288572520699)
                      ·
                        rfl

theorem cell23_547261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_547261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547261 prefixEnd_547261 := by exact prefixLift 547261
  have htrace : WordTrace (prefixWord ++ tailWord_547261) baseStart_547261 baseEnd_547261 := by
    simpa [prefixWord, tailWord_547261, baseEnd_547261] using wordTrace_append hprefix tailTrace_547261
  have hstable : (prefixWord ++ tailWord_547261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547261).length < 2 ^ (prefixWord ++ tailWord_547261).sum := by decide
  have hdescent : baseEnd_547261 < baseStart_547261 := by decide
  rcases family_descends (prefixWord ++ tailWord_547261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547298 : List Nat := [3, 3, 3, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_547298 : Nat := 118140960795 + 547298 * 2 ^ 59
def prefixEnd_547298 : Nat := 4983230072969 + 3 ^ 40 * 547298 * 2
def baseEnd_547298 : Nat := 281026935244504927758029

theorem tailTrace_547298 : CollatzResearch.WordTrace tailWord_547298 prefixEnd_547298 281026935244504927758029 := by
  unfold tailWord_547298
  simp only [CollatzResearch.WordTrace]
  refine ⟨4990399492810072975474637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13307731980826861267932365 4990399492810072975474637)
  ·
    refine ⟨1871399809803777365802989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4990399492810072975474637 1871399809803777365802989)
    ·
      refine ⟨701774928676416512176121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1871399809803777365802989 701774928676416512176121)
      ·
        refine ⟨526331196507312384132091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 701774928676416512176121 526331196507312384132091)
        ·
          refine ⟨789496794760968576198137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 526331196507312384132091 789496794760968576198137)
          ·
            refine ⟨592122596070726432148603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 789496794760968576198137 592122596070726432148603)
            ·
              refine ⟨888183894106089648222905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 592122596070726432148603 888183894106089648222905)
              ·
                refine ⟨666137920579567236167179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 888183894106089648222905 666137920579567236167179)
                ·
                  refine ⟨999206880869350854250769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 666137920579567236167179 999206880869350854250769)
                  ·
                    refine ⟨749405160652013140688077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 999206880869350854250769 749405160652013140688077)
                    ·
                      refine ⟨281026935244504927758029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 749405160652013140688077 281026935244504927758029)
                      ·
                        rfl

theorem cell23_547298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_547298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547298 prefixEnd_547298 := by exact prefixLift 547298
  have htrace : WordTrace (prefixWord ++ tailWord_547298) baseStart_547298 baseEnd_547298 := by
    simpa [prefixWord, tailWord_547298, baseEnd_547298] using wordTrace_append hprefix tailTrace_547298
  have hstable : (prefixWord ++ tailWord_547298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547298).length < 2 ^ (prefixWord ++ tailWord_547298).sum := by decide
  have hdescent : baseEnd_547298 < baseStart_547298 := by decide
  rcases family_descends (prefixWord ++ tailWord_547298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547304 : List Nat := [2, 1, 4, 1, 1, 3, 3, 2, 1, 3, 2]
def baseStart_547304 : Nat := 118140960795 + 547304 * 2 ^ 59
def prefixEnd_547304 : Nat := 4983230072969 + 3 ^ 40 * 547304 * 2
def baseEnd_547304 : Nat := 281030016128431904283001

theorem tailTrace_547304 : CollatzResearch.WordTrace tailWord_547304 prefixEnd_547304 281030016128431904283001 := by
  unfold tailWord_547304
  simp only [CollatzResearch.WordTrace]
  refine ⟨9980908404609277463308483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13307877872812369951077977 9980908404609277463308483)
  ·
    refine ⟨14971362606913916194962725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9980908404609277463308483 14971362606913916194962725)
    ·
      refine ⟨2807130488796359286555511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14971362606913916194962725 2807130488796359286555511)
      ·
        refine ⟨4210695733194538929833267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2807130488796359286555511 4210695733194538929833267)
        ·
          refine ⟨6316043599791808394749901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4210695733194538929833267 6316043599791808394749901)
          ·
            refine ⟨2368516349921928148031213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6316043599791808394749901 2368516349921928148031213)
            ·
              refine ⟨888193631220723055511705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2368516349921928148031213 888193631220723055511705)
              ·
                refine ⟨666145223415542291633779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 888193631220723055511705 666145223415542291633779)
                ·
                  refine ⟨999217835123313437450669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 666145223415542291633779 999217835123313437450669)
                  ·
                    refine ⟨374706688171242539044001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 999217835123313437450669 374706688171242539044001)
                    ·
                      refine ⟨281030016128431904283001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 374706688171242539044001 281030016128431904283001)
                      ·
                        rfl

theorem cell23_547304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_547304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547304 prefixEnd_547304 := by exact prefixLift 547304
  have htrace : WordTrace (prefixWord ++ tailWord_547304) baseStart_547304 baseEnd_547304 := by
    simpa [prefixWord, tailWord_547304, baseEnd_547304] using wordTrace_append hprefix tailTrace_547304
  have hstable : (prefixWord ++ tailWord_547304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547304).length < 2 ^ (prefixWord ++ tailWord_547304).sum := by decide
  have hdescent : baseEnd_547304 < baseStart_547304 := by decide
  rcases family_descends (prefixWord ++ tailWord_547304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547333 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 1, 2, 7]
def baseStart_547333 : Nat := 118140960795 + 547333 * 2 ^ 59
def prefixEnd_547333 : Nat := 4983230072969 + 3 ^ 40 * 547333 * 2
def baseEnd_547333 : Nat := 281044907067412290820367

theorem tailTrace_547333 : CollatzResearch.WordTrace tailWord_547333 prefixEnd_547333 281044907067412290820367 := by
  unfold tailWord_547333
  simp only [CollatzResearch.WordTrace]
  refine ⟨19962874526113492879422653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13308583017408995252948435 19962874526113492879422653)
  ·
    refine ⟨7486077947292559829783495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19962874526113492879422653 7486077947292559829783495)
    ·
      refine ⟨11229116920938839744675243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7486077947292559829783495 11229116920938839744675243)
      ·
        refine ⟨16843675381408259617012865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11229116920938839744675243 16843675381408259617012865)
        ·
          refine ⟨12632756536056194712759649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16843675381408259617012865 12632756536056194712759649)
          ·
            refine ⟨9474567402042146034569737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12632756536056194712759649 9474567402042146034569737)
            ·
              refine ⟨7105925551531609525927303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9474567402042146034569737 7105925551531609525927303)
              ·
                refine ⟨10658888327297414288890955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7105925551531609525927303 10658888327297414288890955)
                ·
                  refine ⟨15988332490946121433336433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10658888327297414288890955 15988332490946121433336433)
                  ·
                    refine ⟨11991249368209591075002325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15988332490946121433336433 11991249368209591075002325)
                    ·
                      refine ⟨281044907067412290820367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11991249368209591075002325 281044907067412290820367)
                      ·
                        rfl

theorem cell23_547333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_547333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547333 prefixEnd_547333 := by exact prefixLift 547333
  have htrace : WordTrace (prefixWord ++ tailWord_547333) baseStart_547333 baseEnd_547333 := by
    simpa [prefixWord, tailWord_547333, baseEnd_547333] using wordTrace_append hprefix tailTrace_547333
  have hstable : (prefixWord ++ tailWord_547333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547333).length < 2 ^ (prefixWord ++ tailWord_547333).sum := by decide
  have hdescent : baseEnd_547333 < baseStart_547333 := by decide
  rcases family_descends (prefixWord ++ tailWord_547333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547351 : List Nat := [1, 1, 3, 6, 1, 1, 2, 1, 1, 4, 2]
def baseStart_547351 : Nat := 118140960795 + 547351 * 2 ^ 59
def prefixEnd_547351 : Nat := 4983230072969 + 3 ^ 40 * 547351 * 2
def baseEnd_547351 : Nat := 281054149719193220395285

theorem tailTrace_547351 : CollatzResearch.WordTrace tailWord_547351 prefixEnd_547351 281054149719193220395285 := by
  unfold tailWord_547351
  simp only [CollatzResearch.WordTrace]
  refine ⟨19963531040048281953577907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13309020693365521302385271 19963531040048281953577907)
  ·
    refine ⟨29945296560072422930366861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19963531040048281953577907 29945296560072422930366861)
    ·
      refine ⟨11229486210027158598887573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29945296560072422930366861 11229486210027158598887573)
      ·
        refine ⟨526382166095023059322855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11229486210027158598887573 526382166095023059322855)
        ·
          refine ⟨789573249142534588984283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 526382166095023059322855 789573249142534588984283)
          ·
            refine ⟨1184359873713801883476425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 789573249142534588984283 1184359873713801883476425)
            ·
              refine ⟨888269905285351412607319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1184359873713801883476425 888269905285351412607319)
              ·
                refine ⟨1332404857928027118910979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 888269905285351412607319 1332404857928027118910979)
                ·
                  refine ⟨1998607286892040678366469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1332404857928027118910979 1998607286892040678366469)
                  ·
                    refine ⟨374738866292257627193713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1998607286892040678366469 374738866292257627193713)
                    ·
                      refine ⟨281054149719193220395285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 374738866292257627193713 281054149719193220395285)
                      ·
                        rfl

theorem cell23_547351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_547351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547351 prefixEnd_547351 := by exact prefixLift 547351
  have htrace : WordTrace (prefixWord ++ tailWord_547351) baseStart_547351 baseEnd_547351 := by
    simpa [prefixWord, tailWord_547351, baseEnd_547351] using wordTrace_append hprefix tailTrace_547351
  have hstable : (prefixWord ++ tailWord_547351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547351).length < 2 ^ (prefixWord ++ tailWord_547351).sum := by decide
  have hdescent : baseEnd_547351 < baseStart_547351 := by decide
  rcases family_descends (prefixWord ++ tailWord_547351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547353 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 3, 7]
def baseStart_547353 : Nat := 118140960795 + 547353 * 2 ^ 59
def prefixEnd_547353 : Nat := 4983230072969 + 3 ^ 40 * 547353 * 2
def baseEnd_547353 : Nat := 93685058893500737523425

theorem tailTrace_547353 : CollatzResearch.WordTrace tailWord_547353 prefixEnd_547353 93685058893500737523425 := by
  unfold tailWord_547353
  simp only [CollatzResearch.WordTrace]
  refine ⟨19963603986041036295150713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13309069324027357530100475 19963603986041036295150713)
  ·
    refine ⟨14972702989530777221363035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19963603986041036295150713 14972702989530777221363035)
    ·
      refine ⟨22459054484296165832044553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14972702989530777221363035 22459054484296165832044553)
      ·
        refine ⟨16844290863222124374033415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22459054484296165832044553 16844290863222124374033415)
        ·
          refine ⟨25266436294833186561050123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16844290863222124374033415 25266436294833186561050123)
          ·
            refine ⟨37899654442249779841575185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25266436294833186561050123 37899654442249779841575185)
            ·
              refine ⟨28424740831687334881181389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37899654442249779841575185 28424740831687334881181389)
              ·
                refine ⟨10659277811882750580443021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28424740831687334881181389 10659277811882750580443021)
                ·
                  refine ⟨3997229179456031467666133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10659277811882750580443021 3997229179456031467666133)
                  ·
                    refine ⟨93685058893500737523425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3997229179456031467666133 93685058893500737523425)
                    ·
                      rfl

theorem cell23_547353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 7].length) (baseStart_547353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547353 prefixEnd_547353 := by exact prefixLift 547353
  have htrace : WordTrace (prefixWord ++ tailWord_547353) baseStart_547353 baseEnd_547353 := by
    simpa [prefixWord, tailWord_547353, baseEnd_547353] using wordTrace_append hprefix tailTrace_547353
  have hstable : (prefixWord ++ tailWord_547353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547353).length < 2 ^ (prefixWord ++ tailWord_547353).sum := by decide
  have hdescent : baseEnd_547353 < baseStart_547353 := by decide
  rcases family_descends (prefixWord ++ tailWord_547353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547407 : List Nat := [1, 1, 2, 1, 1, 2, 6, 1, 2, 4, 2]
def baseStart_547407 : Nat := 118140960795 + 547407 * 2 ^ 59
def prefixEnd_547407 : Nat := 4983230072969 + 3 ^ 40 * 547407 * 2
def baseEnd_547407 : Nat := 281082904635845001295027

theorem tailTrace_547407 : CollatzResearch.WordTrace tailWord_547407 prefixEnd_547407 281082904635845001295027 := by
  unfold tailWord_547407
  simp only [CollatzResearch.WordTrace]
  refine ⟨19965573527845403517616475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13310382351896935678410983 19965573527845403517616475)
  ·
    refine ⟨29948360291768105276424713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19965573527845403517616475 29948360291768105276424713)
    ·
      refine ⟨22461270218826078957318535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29948360291768105276424713 22461270218826078957318535)
      ·
        refine ⟨33691905328239118435977803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22461270218826078957318535 33691905328239118435977803)
        ·
          refine ⟨50537857992358677653966705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33691905328239118435977803 50537857992358677653966705)
          ·
            refine ⟨37903393494269008240475029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50537857992358677653966705 37903393494269008240475029)
            ·
              refine ⟨1776721570043859761272267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37903393494269008240475029 1776721570043859761272267)
              ·
                refine ⟨2665082355065789641908401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1776721570043859761272267 2665082355065789641908401)
                ·
                  refine ⟨1998811766299342231431301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2665082355065789641908401 1998811766299342231431301)
                  ·
                    refine ⟨374777206181126668393369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1998811766299342231431301 374777206181126668393369)
                    ·
                      refine ⟨281082904635845001295027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 374777206181126668393369 281082904635845001295027)
                      ·
                        rfl

theorem cell23_547407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 4, 2].length) (baseStart_547407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547407 prefixEnd_547407 := by exact prefixLift 547407
  have htrace : WordTrace (prefixWord ++ tailWord_547407) baseStart_547407 baseEnd_547407 := by
    simpa [prefixWord, tailWord_547407, baseEnd_547407] using wordTrace_append hprefix tailTrace_547407
  have hstable : (prefixWord ++ tailWord_547407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547407).length < 2 ^ (prefixWord ++ tailWord_547407).sum := by decide
  have hdescent : baseEnd_547407 < baseStart_547407 := by decide
  rcases family_descends (prefixWord ++ tailWord_547407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547427 : List Nat := [1, 1, 1, 5, 1, 2, 2, 3, 2, 2, 3]
def baseStart_547427 : Nat := 118140960795 + 547427 * 2 ^ 59
def prefixEnd_547427 : Nat := 4983230072969 + 3 ^ 40 * 547427 * 2
def baseEnd_547427 : Nat := 281093174248934923044935

theorem tailTrace_547427 : CollatzResearch.WordTrace tailWord_547427 prefixEnd_547427 281093174248934923044935 := by
  unfold tailWord_547427
  simp only [CollatzResearch.WordTrace]
  refine ⟨19966302987772946933344535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13310868658515297955563023 19966302987772946933344535)
  ·
    refine ⟨29949454481659420400016803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19966302987772946933344535 29949454481659420400016803)
    ·
      refine ⟨44924181722489130600025205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29949454481659420400016803 44924181722489130600025205)
      ·
        refine ⟨4211642036483355993752363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44924181722489130600025205 4211642036483355993752363)
        ·
          refine ⟨6317463054725033990628545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4211642036483355993752363 6317463054725033990628545)
          ·
            refine ⟨4738097291043775492971409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6317463054725033990628545 4738097291043775492971409)
            ·
              refine ⟨3553572968282831619728557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4738097291043775492971409 3553572968282831619728557)
              ·
                refine ⟨1332589863106061857398209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3553572968282831619728557 1332589863106061857398209)
                ·
                  refine ⟨999442397329546393048657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1332589863106061857398209 999442397329546393048657)
                  ·
                    refine ⟨749581797997159794786493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 999442397329546393048657 749581797997159794786493)
                    ·
                      refine ⟨281093174248934923044935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 749581797997159794786493 281093174248934923044935)
                      ·
                        rfl

theorem cell23_547427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_547427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547427 prefixEnd_547427 := by exact prefixLift 547427
  have htrace : WordTrace (prefixWord ++ tailWord_547427) baseStart_547427 baseEnd_547427 := by
    simpa [prefixWord, tailWord_547427, baseEnd_547427] using wordTrace_append hprefix tailTrace_547427
  have hstable : (prefixWord ++ tailWord_547427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547427).length < 2 ^ (prefixWord ++ tailWord_547427).sum := by decide
  have hdescent : baseEnd_547427 < baseStart_547427 := by decide
  rcases family_descends (prefixWord ++ tailWord_547427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547467 : List Nat := [1, 1, 1, 1, 4, 1, 2, 4, 1, 5, 2]
def baseStart_547467 : Nat := 118140960795 + 547467 * 2 ^ 59
def prefixEnd_547467 : Nat := 4983230072969 + 3 ^ 40 * 547467 * 2
def baseEnd_547467 : Nat := 281113713475114766544751

theorem tailTrace_547467 : CollatzResearch.WordTrace tailWord_547467 prefixEnd_547467 281113713475114766544751 := by
  unfold tailWord_547467
  simp only [CollatzResearch.WordTrace]
  refine ⟨19967761907628033764800655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13311841271752022509867103 19967761907628033764800655)
  ·
    refine ⟨29951642861442050647200983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19967761907628033764800655 29951642861442050647200983)
    ·
      refine ⟨44927464292163075970801475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29951642861442050647200983 44927464292163075970801475)
      ·
        refine ⟨67391196438244613956202213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44927464292163075970801475 67391196438244613956202213)
        ·
          refine ⟨12635849332170865116787915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67391196438244613956202213 12635849332170865116787915)
          ·
            refine ⟨18953773998256297675181873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12635849332170865116787915 18953773998256297675181873)
            ·
              refine ⟨14215330498692223256386405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18953773998256297675181873 14215330498692223256386405)
              ·
                refine ⟨2665374468504791860572451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14215330498692223256386405 2665374468504791860572451)
                ·
                  refine ⟨3998061702757187790858677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2665374468504791860572451 3998061702757187790858677)
                  ·
                    refine ⟨374818284633486355393001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3998061702757187790858677 374818284633486355393001)
                    ·
                      refine ⟨281113713475114766544751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 374818284633486355393001 281113713475114766544751)
                      ·
                        rfl

theorem cell23_547467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 5, 2].length) (baseStart_547467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547467 prefixEnd_547467 := by exact prefixLift 547467
  have htrace : WordTrace (prefixWord ++ tailWord_547467) baseStart_547467 baseEnd_547467 := by
    simpa [prefixWord, tailWord_547467, baseEnd_547467] using wordTrace_append hprefix tailTrace_547467
  have hstable : (prefixWord ++ tailWord_547467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547467).length < 2 ^ (prefixWord ++ tailWord_547467).sum := by decide
  have hdescent : baseEnd_547467 < baseStart_547467 := by decide
  rcases family_descends (prefixWord ++ tailWord_547467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547501 : List Nat := [1, 5, 2, 1, 1, 2, 2, 2, 2, 3, 2]
def baseStart_547501 : Nat := 118140960795 + 547501 * 2 ^ 59
def prefixEnd_547501 : Nat := 4983230072969 + 3 ^ 40 * 547501 * 2
def baseEnd_547501 : Nat := 281131171817367633519595

theorem tailTrace_547501 : CollatzResearch.WordTrace tailWord_547501 prefixEnd_547501 281131171817367633519595 := by
  unfold tailWord_547501
  simp only [CollatzResearch.WordTrace]
  refine ⟨19969001989504857571538357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13312667993003238381025571 19969001989504857571538357)
  ·
    refine ⟨1872093936516080397331721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19969001989504857571538357 1872093936516080397331721)
    ·
      refine ⟨1404070452387060297998791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1872093936516080397331721 1404070452387060297998791)
      ·
        refine ⟨2106105678580590446998187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1404070452387060297998791 2106105678580590446998187)
        ·
          refine ⟨3159158517870885670497281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2106105678580590446998187 3159158517870885670497281)
          ·
            refine ⟨2369368888403164252872961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3159158517870885670497281 2369368888403164252872961)
            ·
              refine ⟨1777026666302373189654721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2369368888403164252872961 1777026666302373189654721)
              ·
                refine ⟨1332769999726779892241041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1777026666302373189654721 1332769999726779892241041)
                ·
                  refine ⟨999577499795084919180781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1332769999726779892241041 999577499795084919180781)
                  ·
                    refine ⟨374841562423156844692793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 999577499795084919180781 374841562423156844692793)
                    ·
                      refine ⟨281131171817367633519595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 374841562423156844692793 281131171817367633519595)
                      ·
                        rfl

theorem cell23_547501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_547501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547501 prefixEnd_547501 := by exact prefixLift 547501
  have htrace : WordTrace (prefixWord ++ tailWord_547501) baseStart_547501 baseEnd_547501 := by
    simpa [prefixWord, tailWord_547501, baseEnd_547501] using wordTrace_append hprefix tailTrace_547501
  have hstable : (prefixWord ++ tailWord_547501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547501).length < 2 ^ (prefixWord ++ tailWord_547501).sum := by decide
  have hdescent : baseEnd_547501 < baseStart_547501 := by decide
  rcases family_descends (prefixWord ++ tailWord_547501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547524 : List Nat := [2, 3, 3, 1, 1, 3, 2, 1, 1, 6]
def baseStart_547524 : Nat := 118140960795 + 547524 * 2 ^ 59
def prefixEnd_547524 : Nat := 4983230072969 + 3 ^ 40 * 547524 * 2
def baseEnd_547524 : Nat := 93714327290807014510663

theorem tailTrace_547524 : CollatzResearch.WordTrace tailWord_547524 prefixEnd_547524 93714327290807014510663 := by
  unfold tailWord_547524
  simp only [CollatzResearch.WordTrace]
  refine ⟨9984920434210766249812813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13313227245614354999750417 9984920434210766249812813)
  ·
    refine ⟨3744345162829037343679805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9984920434210766249812813 3744345162829037343679805)
    ·
      refine ⟨1404129436060889003879927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3744345162829037343679805 1404129436060889003879927)
      ·
        refine ⟨2106194154091333505819891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1404129436060889003879927 2106194154091333505819891)
        ·
          refine ⟨3159291231137000258729837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2106194154091333505819891 3159291231137000258729837)
          ·
            refine ⟨1184734211676375097023689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3159291231137000258729837 1184734211676375097023689)
            ·
              refine ⟨888550658757281322767767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1184734211676375097023689 888550658757281322767767)
              ·
                refine ⟨1332825988135921984151651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 888550658757281322767767 1332825988135921984151651)
                ·
                  refine ⟨1999238982203882976227477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1332825988135921984151651 1999238982203882976227477)
                  ·
                    refine ⟨93714327290807014510663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1999238982203882976227477 93714327290807014510663)
                    ·
                      rfl

theorem cell23_547524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_547524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547524 prefixEnd_547524 := by exact prefixLift 547524
  have htrace : WordTrace (prefixWord ++ tailWord_547524) baseStart_547524 baseEnd_547524 := by
    simpa [prefixWord, tailWord_547524, baseEnd_547524] using wordTrace_append hprefix tailTrace_547524
  have hstable : (prefixWord ++ tailWord_547524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547524).length < 2 ^ (prefixWord ++ tailWord_547524).sum := by decide
  have hdescent : baseEnd_547524 < baseStart_547524 := by decide
  rcases family_descends (prefixWord ++ tailWord_547524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547534 : List Nat := [4, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3]
def baseStart_547534 : Nat := 118140960795 + 547534 * 2 ^ 59
def prefixEnd_547534 : Nat := 4983230072969 + 3 ^ 40 * 547534 * 2
def baseEnd_547534 : Nat := 281148116678966004406943

theorem tailTrace_547534 : CollatzResearch.WordTrace tailWord_547534 prefixEnd_547534 281148116678966004406943 := by
  unfold tailWord_547534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2496275699798163025936207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13313470398923536138326437 2496275699798163025936207)
  ·
    refine ⟨3744413549697244538904311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2496275699798163025936207 3744413549697244538904311)
    ·
      refine ⟨5616620324545866808356467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3744413549697244538904311 5616620324545866808356467)
      ·
        refine ⟨8424930486818800212534701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5616620324545866808356467 8424930486818800212534701)
        ·
          refine ⟨3159348932557050079700513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8424930486818800212534701 3159348932557050079700513)
          ·
            refine ⟨2369511699417787559775385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3159348932557050079700513 2369511699417787559775385)
            ·
              refine ⟨1777133774563340669831539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2369511699417787559775385 1777133774563340669831539)
              ·
                refine ⟨2665700661845011004747309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1777133774563340669831539 2665700661845011004747309)
                ·
                  refine ⟨999637748191879126780241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2665700661845011004747309 999637748191879126780241)
                  ·
                    refine ⟨749728311143909345085181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 999637748191879126780241 749728311143909345085181)
                    ·
                      refine ⟨281148116678966004406943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 749728311143909345085181 281148116678966004406943)
                      ·
                        rfl

theorem cell23_547534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_547534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547534 prefixEnd_547534 := by exact prefixLift 547534
  have htrace : WordTrace (prefixWord ++ tailWord_547534) baseStart_547534 baseEnd_547534 := by
    simpa [prefixWord, tailWord_547534, baseEnd_547534] using wordTrace_append hprefix tailTrace_547534
  have hstable : (prefixWord ++ tailWord_547534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547534).length < 2 ^ (prefixWord ++ tailWord_547534).sum := by decide
  have hdescent : baseEnd_547534 < baseStart_547534 := by decide
  rcases family_descends (prefixWord ++ tailWord_547534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547537 : List Nat := [1, 2, 2, 1, 2, 3, 5, 7]
def baseStart_547537 : Nat := 118140960795 + 547537 * 2 ^ 59
def prefixEnd_547537 : Nat := 4983230072969 + 3 ^ 40 * 547537 * 2
def baseEnd_547537 : Nat := 10412950263738129358127

theorem tailTrace_547537 : CollatzResearch.WordTrace tailWord_547537 prefixEnd_547537 10412950263738129358127 := by
  unfold tailWord_547537
  simp only [CollatzResearch.WordTrace]
  refine ⟨19970315017374435719848865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13313543344916290479899243 19970315017374435719848865)
  ·
    refine ⟨14977736263030826789886649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19970315017374435719848865 14977736263030826789886649)
    ·
      refine ⟨11233302197273120092414987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14977736263030826789886649 11233302197273120092414987)
      ·
        refine ⟨16849953295909680138622481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11233302197273120092414987 16849953295909680138622481)
        ·
          refine ⟨12637464971932260103966861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16849953295909680138622481 12637464971932260103966861)
          ·
            refine ⟨4739049364474597538987573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12637464971932260103966861 4739049364474597538987573)
            ·
              refine ⟨444285877919493519280085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4739049364474597538987573 444285877919493519280085)
              ·
                refine ⟨10412950263738129358127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 444285877919493519280085 10412950263738129358127)
                ·
                  rfl

theorem cell23_547537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 7].length) (baseStart_547537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547537 prefixEnd_547537 := by exact prefixLift 547537
  have htrace : WordTrace (prefixWord ++ tailWord_547537) baseStart_547537 baseEnd_547537 := by
    simpa [prefixWord, tailWord_547537, baseEnd_547537] using wordTrace_append hprefix tailTrace_547537
  have hstable : (prefixWord ++ tailWord_547537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547537).length < 2 ^ (prefixWord ++ tailWord_547537).sum := by decide
  have hdescent : baseEnd_547537 < baseStart_547537 := by decide
  rcases family_descends (prefixWord ++ tailWord_547537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547548 : List Nat := [2, 2, 5, 1, 1, 1, 4, 1, 1, 1, 4]
def baseStart_547548 : Nat := 118140960795 + 547548 * 2 ^ 59
def prefixEnd_547548 : Nat := 4983230072969 + 3 ^ 40 * 547548 * 2
def baseEnd_547548 : Nat := 281155305408128949631879

theorem tailTrace_547548 : CollatzResearch.WordTrace tailWord_547548 prefixEnd_547548 281155305408128949631879 := by
  unfold tailWord_547548
  simp only [CollatzResearch.WordTrace]
  refine ⟨9985358110167292299249649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13313810813556389732332865 9985358110167292299249649)
  ·
    refine ⟨7489018582625469224437237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9985358110167292299249649 7489018582625469224437237)
    ·
      refine ⟨702095492121137739790991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7489018582625469224437237 702095492121137739790991)
      ·
        refine ⟨1053143238181706609686487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 702095492121137739790991 1053143238181706609686487)
        ·
          refine ⟨1579714857272559914529731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1053143238181706609686487 1579714857272559914529731)
          ·
            refine ⟨2369572285908839871794597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1579714857272559914529731 2369572285908839871794597)
            ·
              refine ⟨444294803607907475961487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2369572285908839871794597 444294803607907475961487)
              ·
                refine ⟨666442205411861213942231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 444294803607907475961487 666442205411861213942231)
                ·
                  refine ⟨999663308117791820913347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 666442205411861213942231 999663308117791820913347)
                  ·
                    refine ⟨1499494962176687731370021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 999663308117791820913347 1499494962176687731370021)
                    ·
                      refine ⟨281155305408128949631879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1499494962176687731370021 281155305408128949631879)
                      ·
                        rfl

theorem cell23_547548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_547548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547548 prefixEnd_547548 := by exact prefixLift 547548
  have htrace : WordTrace (prefixWord ++ tailWord_547548) baseStart_547548 baseEnd_547548 := by
    simpa [prefixWord, tailWord_547548, baseEnd_547548] using wordTrace_append hprefix tailTrace_547548
  have hstable : (prefixWord ++ tailWord_547548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547548).length < 2 ^ (prefixWord ++ tailWord_547548).sum := by decide
  have hdescent : baseEnd_547548 < baseStart_547548 := by decide
  rcases family_descends (prefixWord ++ tailWord_547548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547551 : List Nat := [1, 1, 2, 3, 2, 3, 4, 1, 1, 2, 3]
def baseStart_547551 : Nat := 118140960795 + 547551 * 2 ^ 59
def prefixEnd_547551 : Nat := 4983230072969 + 3 ^ 40 * 547551 * 2
def baseEnd_547551 : Nat := 281156845850092437894365

theorem tailTrace_547551 : CollatzResearch.WordTrace tailWord_547551 prefixEnd_547551 281156845850092437894365 := by
  unfold tailWord_547551
  simp only [CollatzResearch.WordTrace]
  refine ⟨19970825639323716110858507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13313883759549144073905671 19970825639323716110858507)
  ·
    refine ⟨29956238458985574166287761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19970825639323716110858507 29956238458985574166287761)
    ·
      refine ⟨22467178844239180624715821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29956238458985574166287761 22467178844239180624715821)
      ·
        refine ⟨8425192066589692734268433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22467178844239180624715821 8425192066589692734268433)
        ·
          refine ⟨6318894049942269550701325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8425192066589692734268433 6318894049942269550701325)
          ·
            refine ⟨2369585268728351081512997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6318894049942269550701325 2369585268728351081512997)
            ·
              refine ⟨444297237886565827783687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2369585268728351081512997 444297237886565827783687)
              ·
                refine ⟨666445856829848741675531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 444297237886565827783687 666445856829848741675531)
                ·
                  refine ⟨999668785244773112513297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 666445856829848741675531 999668785244773112513297)
                  ·
                    refine ⟨749751588933579834384973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 999668785244773112513297 749751588933579834384973)
                    ·
                      refine ⟨281156845850092437894365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 749751588933579834384973 281156845850092437894365)
                      ·
                        rfl

theorem cell23_547551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 1, 2, 3].length) (baseStart_547551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547551 prefixEnd_547551 := by exact prefixLift 547551
  have htrace : WordTrace (prefixWord ++ tailWord_547551) baseStart_547551 baseEnd_547551 := by
    simpa [prefixWord, tailWord_547551, baseEnd_547551] using wordTrace_append hprefix tailTrace_547551
  have hstable : (prefixWord ++ tailWord_547551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547551).length < 2 ^ (prefixWord ++ tailWord_547551).sum := by decide
  have hdescent : baseEnd_547551 < baseStart_547551 := by decide
  rcases family_descends (prefixWord ++ tailWord_547551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547621 : List Nat := [1, 3, 1, 2, 3, 1, 1, 3, 4, 2, 2]
def baseStart_547621 : Nat := 118140960795 + 547621 * 2 ^ 59
def prefixEnd_547621 : Nat := 4983230072969 + 3 ^ 40 * 547621 * 2
def baseEnd_547621 : Nat := 281192789495907164019043

theorem tailTrace_547621 : CollatzResearch.WordTrace tailWord_547621 prefixEnd_547621 281192789495907164019043 := by
  unfold tailWord_547621
  simp only [CollatzResearch.WordTrace]
  refine ⟨19973378749070118065906717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13315585832713412043937811 19973378749070118065906717)
  ·
    refine ⟨7490017030901294274715019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19973378749070118065906717 7490017030901294274715019)
    ·
      refine ⟨11235025546351941412072529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7490017030901294274715019 11235025546351941412072529)
      ·
        refine ⟨8426269159763956059054397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11235025546351941412072529 8426269159763956059054397)
        ·
          refine ⟨3159850934911483522145399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8426269159763956059054397 3159850934911483522145399)
          ·
            refine ⟨4739776402367225283218099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3159850934911483522145399 4739776402367225283218099)
            ·
              refine ⟨7109664603550837924827149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4739776402367225283218099 7109664603550837924827149)
              ·
                refine ⟨2666124226331564221810181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7109664603550837924827149 2666124226331564221810181)
                ·
                  refine ⟨499898292437168291589409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2666124226331564221810181 499898292437168291589409)
                  ·
                    refine ⟨374923719327876218692057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 499898292437168291589409 374923719327876218692057)
                    ·
                      refine ⟨281192789495907164019043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 374923719327876218692057 281192789495907164019043)
                      ·
                        rfl

theorem cell23_547621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4, 2, 2].length) (baseStart_547621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547621 prefixEnd_547621 := by exact prefixLift 547621
  have htrace : WordTrace (prefixWord ++ tailWord_547621) baseStart_547621 baseEnd_547621 := by
    simpa [prefixWord, tailWord_547621, baseEnd_547621] using wordTrace_append hprefix tailTrace_547621
  have hstable : (prefixWord ++ tailWord_547621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547621).length < 2 ^ (prefixWord ++ tailWord_547621).sum := by decide
  have hdescent : baseEnd_547621 < baseStart_547621 := by decide
  rcases family_descends (prefixWord ++ tailWord_547621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547624 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 2, 4, 3]
def baseStart_547624 : Nat := 118140960795 + 547624 * 2 ^ 59
def prefixEnd_547624 : Nat := 4983230072969 + 3 ^ 40 * 547624 * 2
def baseEnd_547624 : Nat := 281194329937870652281529

theorem tailTrace_547624 : CollatzResearch.WordTrace tailWord_547624 prefixEnd_547624 281194329937870652281529 := by
  unfold tailWord_547624
  simp only [CollatzResearch.WordTrace]
  refine ⟨9986744084029624789132963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13315658778706166385510617 9986744084029624789132963)
  ·
    refine ⟨14980116126044437183699445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9986744084029624789132963 14980116126044437183699445)
    ·
      refine ⟨1404385886816665985971823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14980116126044437183699445 1404385886816665985971823)
      ·
        refine ⟨2106578830224998978957735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1404385886816665985971823 2106578830224998978957735)
        ·
          refine ⟨3159868245337498468436603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2106578830224998978957735 3159868245337498468436603)
          ·
            refine ⟨4739802368006247702654905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3159868245337498468436603 4739802368006247702654905)
            ·
              refine ⟨3554851776004685776991179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4739802368006247702654905 3554851776004685776991179)
              ·
                refine ⟨5332277664007028665486769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3554851776004685776991179 5332277664007028665486769)
                ·
                  refine ⟨3999208248005271499115077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5332277664007028665486769 3999208248005271499115077)
                  ·
                    refine ⟨749851546500988406084077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3999208248005271499115077 749851546500988406084077)
                    ·
                      refine ⟨281194329937870652281529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 749851546500988406084077 281194329937870652281529)
                      ·
                        rfl

theorem cell23_547624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_547624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547624 prefixEnd_547624 := by exact prefixLift 547624
  have htrace : WordTrace (prefixWord ++ tailWord_547624) baseStart_547624 baseEnd_547624 := by
    simpa [prefixWord, tailWord_547624, baseEnd_547624] using wordTrace_append hprefix tailTrace_547624
  have hstable : (prefixWord ++ tailWord_547624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547624).length < 2 ^ (prefixWord ++ tailWord_547624).sum := by decide
  have hdescent : baseEnd_547624 < baseStart_547624 := by decide
  rcases family_descends (prefixWord ++ tailWord_547624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547674 : List Nat := [3, 1, 1, 2, 1, 4, 2, 2, 2, 5]
def baseStart_547674 : Nat := 118140960795 + 547674 * 2 ^ 59
def prefixEnd_547674 : Nat := 4983230072969 + 3 ^ 40 * 547674 * 2
def baseEnd_547674 : Nat := 93740001323531818885433

theorem tailTrace_547674 : CollatzResearch.WordTrace tailWord_547674 prefixEnd_547674 93740001323531818885433 := by
  unfold tailWord_547674
  simp only [CollatzResearch.WordTrace]
  refine ⟨4993827954469527029396519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13316874545252072078390717 4993827954469527029396519)
  ·
    refine ⟨7490741931704290544094779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4993827954469527029396519 7490741931704290544094779)
    ·
      refine ⟨11236112897556435816142169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7490741931704290544094779 11236112897556435816142169)
      ·
        refine ⟨8427084673167326862106627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11236112897556435816142169 8427084673167326862106627)
        ·
          refine ⟨12640627009750990293159941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8427084673167326862106627 12640627009750990293159941)
          ·
            refine ⟨2370117564328310679967489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12640627009750990293159941 2370117564328310679967489)
            ·
              refine ⟨1777588173246233009975617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2370117564328310679967489 1777588173246233009975617)
              ·
                refine ⟨1333191129934674757481713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1777588173246233009975617 1333191129934674757481713)
                ·
                  refine ⟨999893347451006068111285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1333191129934674757481713 999893347451006068111285)
                  ·
                    refine ⟨93740001323531818885433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 999893347451006068111285 93740001323531818885433)
                    ·
                      rfl

theorem cell23_547674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 2, 5].length) (baseStart_547674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547674 prefixEnd_547674 := by exact prefixLift 547674
  have htrace : WordTrace (prefixWord ++ tailWord_547674) baseStart_547674 baseEnd_547674 := by
    simpa [prefixWord, tailWord_547674, baseEnd_547674] using wordTrace_append hprefix tailTrace_547674
  have hstable : (prefixWord ++ tailWord_547674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547674).length < 2 ^ (prefixWord ++ tailWord_547674).sum := by decide
  have hdescent : baseEnd_547674 < baseStart_547674 := by decide
  rcases family_descends (prefixWord ++ tailWord_547674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547684 : List Nat := [2, 3, 1, 1, 4, 1, 2, 1, 1, 2, 5]
def baseStart_547684 : Nat := 118140960795 + 547684 * 2 ^ 59
def prefixEnd_547684 : Nat := 4983230072969 + 3 ^ 40 * 547684 * 2
def baseEnd_547684 : Nat := 281225138777140417531253

theorem tailTrace_547684 : CollatzResearch.WordTrace tailWord_547684 prefixEnd_547684 281225138777140417531253 := by
  unfold tailWord_547684
  simp only [CollatzResearch.WordTrace]
  refine ⟨9987838273920939912725053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13317117698561253216966737 9987838273920939912725053)
  ·
    refine ⟨3745439352720352467271895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9987838273920939912725053 3745439352720352467271895)
    ·
      refine ⟨5618159029080528700907843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3745439352720352467271895 5618159029080528700907843)
      ·
        refine ⟨8427238543620793051361765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5618159029080528700907843 8427238543620793051361765)
        ·
          refine ⟨1580107226928898697130331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8427238543620793051361765 1580107226928898697130331)
          ·
            refine ⟨2370160840393348045695497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1580107226928898697130331 2370160840393348045695497)
            ·
              refine ⟨1777620630295011034271623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2370160840393348045695497 1777620630295011034271623)
              ·
                refine ⟨2666430945442516551407435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1777620630295011034271623 2666430945442516551407435)
                ·
                  refine ⟨3999646418163774827111153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2666430945442516551407435 3999646418163774827111153)
                  ·
                    refine ⟨2999734813622831120333365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3999646418163774827111153 2999734813622831120333365)
                    ·
                      refine ⟨281225138777140417531253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2999734813622831120333365 281225138777140417531253)
                      ·
                        rfl

theorem cell23_547684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_547684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547684 prefixEnd_547684 := by exact prefixLift 547684
  have htrace : WordTrace (prefixWord ++ tailWord_547684) baseStart_547684 baseEnd_547684 := by
    simpa [prefixWord, tailWord_547684, baseEnd_547684] using wordTrace_append hprefix tailTrace_547684
  have hstable : (prefixWord ++ tailWord_547684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547684).length < 2 ^ (prefixWord ++ tailWord_547684).sum := by decide
  have hdescent : baseEnd_547684 < baseStart_547684 := by decide
  rcases family_descends (prefixWord ++ tailWord_547684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547738 : List Nat := [3, 1, 1, 4, 3, 1, 2, 1, 3, 4]
def baseStart_547738 : Nat := 118140960795 + 547738 * 2 ^ 59
def prefixEnd_547738 : Nat := 4983230072969 + 3 ^ 40 * 547738 * 2
def baseEnd_547738 : Nat := 93750955577494402085335

theorem tailTrace_547738 : CollatzResearch.WordTrace tailWord_547738 prefixEnd_547738 93750955577494402085335 := by
  unfold tailWord_547738
  simp only [CollatzResearch.WordTrace]
  refine ⟨4994411522411561761978967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13318430726430831365277245 4994411522411561761978967)
  ·
    refine ⟨7491617283617342642968451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4994411522411561761978967 7491617283617342642968451)
    ·
      refine ⟨11237425925426013964452677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7491617283617342642968451 11237425925426013964452677)
      ·
        refine ⟨2107017361017377618334877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11237425925426013964452677 2107017361017377618334877)
        ·
          refine ⟨790131510381516606875579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2107017361017377618334877 790131510381516606875579)
          ·
            refine ⟨1185197265572274910313369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 790131510381516606875579 1185197265572274910313369)
            ·
              refine ⟨888897949179206182735027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1185197265572274910313369 888897949179206182735027)
              ·
                refine ⟨1333346923768809274102541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 888897949179206182735027 1333346923768809274102541)
                ·
                  refine ⟨500005096413303477788453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1333346923768809274102541 500005096413303477788453)
                  ·
                    refine ⟨93750955577494402085335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 500005096413303477788453 93750955577494402085335)
                    ·
                      rfl

theorem cell23_547738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 3, 4].length) (baseStart_547738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547738 prefixEnd_547738 := by exact prefixLift 547738
  have htrace : WordTrace (prefixWord ++ tailWord_547738) baseStart_547738 baseEnd_547738 := by
    simpa [prefixWord, tailWord_547738, baseEnd_547738] using wordTrace_append hprefix tailTrace_547738
  have hstable : (prefixWord ++ tailWord_547738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547738).length < 2 ^ (prefixWord ++ tailWord_547738).sum := by decide
  have hdescent : baseEnd_547738 < baseStart_547738 := by decide
  rcases family_descends (prefixWord ++ tailWord_547738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547788 : List Nat := [2, 2, 1, 4, 1, 1, 3, 2, 2, 3, 2]
def baseStart_547788 : Nat := 118140960795 + 547788 * 2 ^ 59
def prefixEnd_547788 : Nat := 4983230072969 + 3 ^ 40 * 547788 * 2
def baseEnd_547788 : Nat := 281278540765208010630775

theorem tailTrace_547788 : CollatzResearch.WordTrace tailWord_547788 prefixEnd_547788 281278540765208010630775 := by
  unfold tailWord_547788
  simp only [CollatzResearch.WordTrace]
  refine ⟨9989734869732552793618009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13319646492976737058157345 9989734869732552793618009)
  ·
    refine ⟨7492301152299414595213507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9989734869732552793618009 7492301152299414595213507)
    ·
      refine ⟨11238451728449121892820261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7492301152299414595213507 11238451728449121892820261)
      ·
        refine ⟨2107209699084210354903799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11238451728449121892820261 2107209699084210354903799)
        ·
          refine ⟨3160814548626315532355699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2107209699084210354903799 3160814548626315532355699)
          ·
            refine ⟨4741221822939473298533549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3160814548626315532355699 4741221822939473298533549)
            ·
              refine ⟨1777958183602302486950081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4741221822939473298533549 1777958183602302486950081)
              ·
                refine ⟨1333468637701726865212561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1777958183602302486950081 1333468637701726865212561)
                ·
                  refine ⟨1000101478276295148909421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1333468637701726865212561 1000101478276295148909421)
                  ·
                    refine ⟨375038054353610680841033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1000101478276295148909421 375038054353610680841033)
                    ·
                      refine ⟨281278540765208010630775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 375038054353610680841033 281278540765208010630775)
                      ·
                        rfl

theorem cell23_547788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_547788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547788 prefixEnd_547788 := by exact prefixLift 547788
  have htrace : WordTrace (prefixWord ++ tailWord_547788) baseStart_547788 baseEnd_547788 := by
    simpa [prefixWord, tailWord_547788, baseEnd_547788] using wordTrace_append hprefix tailTrace_547788
  have hstable : (prefixWord ++ tailWord_547788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547788).length < 2 ^ (prefixWord ++ tailWord_547788).sum := by decide
  have hdescent : baseEnd_547788 < baseStart_547788 := by decide
  rcases family_descends (prefixWord ++ tailWord_547788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547789 : List Nat := [1, 6, 3, 1, 1, 2, 1, 1, 3, 4]
def baseStart_547789 : Nat := 118140960795 + 547789 * 2 ^ 59
def prefixEnd_547789 : Nat := 4983230072969 + 3 ^ 40 * 547789 * 2
def baseEnd_547789 : Nat := 93759684748620835572757

theorem tailTrace_547789 : CollatzResearch.WordTrace tailWord_547789 prefixEnd_547789 93759684748620835572757 := by
  unfold tailWord_547789
  simp only [CollatzResearch.WordTrace]
  refine ⟨19979506212461482758022421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13319670808307655172014947 19979506212461482758022421)
  ·
    refine ⟨936539353709132004282301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19979506212461482758022421 936539353709132004282301)
    ·
      refine ⟨351202257640924501605863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 936539353709132004282301 351202257640924501605863)
      ·
        refine ⟨526803386461386752408795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351202257640924501605863 526803386461386752408795)
        ·
          refine ⟨790205079692080128613193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 526803386461386752408795 790205079692080128613193)
          ·
            refine ⟨592653809769060096459895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 790205079692080128613193 592653809769060096459895)
            ·
              refine ⟨888980714653590144689843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 592653809769060096459895 888980714653590144689843)
              ·
                refine ⟨1333471071980385217034765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 888980714653590144689843 1333471071980385217034765)
                ·
                  refine ⟨500051651992644456388037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1333471071980385217034765 500051651992644456388037)
                  ·
                    refine ⟨93759684748620835572757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 500051651992644456388037 93759684748620835572757)
                    ·
                      rfl

theorem cell23_547789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_547789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547789 prefixEnd_547789 := by exact prefixLift 547789
  have htrace : WordTrace (prefixWord ++ tailWord_547789) baseStart_547789 baseEnd_547789 := by
    simpa [prefixWord, tailWord_547789, baseEnd_547789] using wordTrace_append hprefix tailTrace_547789
  have hstable : (prefixWord ++ tailWord_547789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547789).length < 2 ^ (prefixWord ++ tailWord_547789).sum := by decide
  have hdescent : baseEnd_547789 < baseStart_547789 := by decide
  rcases family_descends (prefixWord ++ tailWord_547789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547818 : List Nat := [3, 1, 3, 1, 2, 2, 3, 2, 1, 1, 4]
def baseStart_547818 : Nat := 118140960795 + 547818 * 2 ^ 59
def prefixEnd_547818 : Nat := 4983230072969 + 3 ^ 40 * 547818 * 2
def baseEnd_547818 : Nat := 281293945184842893255637

theorem tailTrace_547818 : CollatzResearch.WordTrace tailWord_547818 prefixEnd_547818 281293945184842893255637 := by
  unfold tailWord_547818
  simp only [CollatzResearch.WordTrace]
  refine ⟨4995140982339105177707027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13320375952904280473885405 4995140982339105177707027)
  ·
    refine ⟨7492711473508657766560541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4995140982339105177707027 7492711473508657766560541)
    ·
      refine ⟨2809766802565746662460203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7492711473508657766560541 2809766802565746662460203)
      ·
        refine ⟨4214650203848619993690305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2809766802565746662460203 4214650203848619993690305)
        ·
          refine ⟨3160987652886464995267729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4214650203848619993690305 3160987652886464995267729)
          ·
            refine ⟨2370740739664848746450797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3160987652886464995267729 2370740739664848746450797)
            ·
              refine ⟨889027777374318279919049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2370740739664848746450797 889027777374318279919049)
              ·
                refine ⟨666770833030738709939287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 889027777374318279919049 666770833030738709939287)
                ·
                  refine ⟨1000156249546108064908931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 666770833030738709939287 1000156249546108064908931)
                  ·
                    refine ⟨1500234374319162097363397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1000156249546108064908931 1500234374319162097363397)
                    ·
                      refine ⟨281293945184842893255637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1500234374319162097363397 281293945184842893255637)
                      ·
                        rfl

theorem cell23_547818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_547818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547818 prefixEnd_547818 := by exact prefixLift 547818
  have htrace : WordTrace (prefixWord ++ tailWord_547818) baseStart_547818 baseEnd_547818 := by
    simpa [prefixWord, tailWord_547818, baseEnd_547818] using wordTrace_append hprefix tailTrace_547818
  have hstable : (prefixWord ++ tailWord_547818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547818).length < 2 ^ (prefixWord ++ tailWord_547818).sum := by decide
  have hdescent : baseEnd_547818 < baseStart_547818 := by decide
  rcases family_descends (prefixWord ++ tailWord_547818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547835 : List Nat := [1, 1, 1, 1, 1, 3, 3, 7, 1, 2, 2]
def baseStart_547835 : Nat := 118140960795 + 547835 * 2 ^ 59
def prefixEnd_547835 : Nat := 4983230072969 + 3 ^ 40 * 547835 * 2
def baseEnd_547835 : Nat := 281302674355969326743059

theorem tailTrace_547835 : CollatzResearch.WordTrace tailWord_547835 prefixEnd_547835 281302674355969326743059 := by
  unfold tailWord_547835
  simp only [CollatzResearch.WordTrace]
  refine ⟨19981183970294832614196959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13320789313529888409464639 19981183970294832614196959)
  ·
    refine ⟨29971775955442248921295439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19981183970294832614196959 29971775955442248921295439)
    ·
      refine ⟨44957663933163373381943159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29971775955442248921295439 44957663933163373381943159)
      ·
        refine ⟨67436495899745060072914739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44957663933163373381943159 67436495899745060072914739)
        ·
          refine ⟨101154743849617590109372109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67436495899745060072914739 101154743849617590109372109)
          ·
            refine ⟨37933028943606596291014541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101154743849617590109372109 37933028943606596291014541)
            ·
              refine ⟨14224885853852473609130453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37933028943606596291014541 14224885853852473609130453)
              ·
                refine ⟨333395762199667350213995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 14224885853852473609130453 333395762199667350213995)
                ·
                  refine ⟨500093643299501025320993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 333395762199667350213995 500093643299501025320993)
                  ·
                    refine ⟨375070232474625768990745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 500093643299501025320993 375070232474625768990745)
                    ·
                      refine ⟨281302674355969326743059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 375070232474625768990745 281302674355969326743059)
                      ·
                        rfl

theorem cell23_547835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7, 1, 2, 2].length) (baseStart_547835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547835 prefixEnd_547835 := by exact prefixLift 547835
  have htrace : WordTrace (prefixWord ++ tailWord_547835) baseStart_547835 baseEnd_547835 := by
    simpa [prefixWord, tailWord_547835, baseEnd_547835] using wordTrace_append hprefix tailTrace_547835
  have hstable : (prefixWord ++ tailWord_547835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547835).length < 2 ^ (prefixWord ++ tailWord_547835).sum := by decide
  have hdescent : baseEnd_547835 < baseStart_547835 := by decide
  rcases family_descends (prefixWord ++ tailWord_547835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547852 : List Nat := [2, 2, 1, 2, 3, 3, 1, 4, 1, 2, 2]
def baseStart_547852 : Nat := 118140960795 + 547852 * 2 ^ 59
def prefixEnd_547852 : Nat := 4983230072969 + 3 ^ 40 * 547852 * 2
def baseEnd_547852 : Nat := 281311403527095760230481

theorem tailTrace_547852 : CollatzResearch.WordTrace tailWord_547852 prefixEnd_547852 281311403527095760230481 := by
  unfold tailWord_547852
  simp only [CollatzResearch.WordTrace]
  refine ⟨9990902005616622258782905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13321202674155496345043873 9990902005616622258782905)
  ·
    refine ⟨7493176504212466694087179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9990902005616622258782905 7493176504212466694087179)
    ·
      refine ⟨11239764756318700041130769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7493176504212466694087179 11239764756318700041130769)
      ·
        refine ⟨8429823567239025030848077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11239764756318700041130769 8429823567239025030848077)
        ·
          refine ⟨3161183837714634386568029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8429823567239025030848077 3161183837714634386568029)
          ·
            refine ⟨1185443939142987894963011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3161183837714634386568029 1185443939142987894963011)
            ·
              refine ⟨1778165908714481842444517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1185443939142987894963011 1778165908714481842444517)
              ·
                refine ⟨333406107883965345458347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1778165908714481842444517 333406107883965345458347)
                ·
                  refine ⟨500109161825948018187521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 333406107883965345458347 500109161825948018187521)
                  ·
                    refine ⟨375081871369461013640641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 500109161825948018187521 375081871369461013640641)
                    ·
                      refine ⟨281311403527095760230481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 375081871369461013640641 281311403527095760230481)
                      ·
                        rfl

theorem cell23_547852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 4, 1, 2, 2].length) (baseStart_547852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547852 prefixEnd_547852 := by exact prefixLift 547852
  have htrace : WordTrace (prefixWord ++ tailWord_547852) baseStart_547852 baseEnd_547852 := by
    simpa [prefixWord, tailWord_547852, baseEnd_547852] using wordTrace_append hprefix tailTrace_547852
  have hstable : (prefixWord ++ tailWord_547852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547852).length < 2 ^ (prefixWord ++ tailWord_547852).sum := by decide
  have hdescent : baseEnd_547852 < baseStart_547852 := by decide
  rcases family_descends (prefixWord ++ tailWord_547852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547884 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 1, 8]
def baseStart_547884 : Nat := 118140960795 + 547884 * 2 ^ 59
def prefixEnd_547884 : Nat := 4983230072969 + 3 ^ 40 * 547884 * 2
def baseEnd_547884 : Nat := 93775944969346545010111

theorem tailTrace_547884 : CollatzResearch.WordTrace tailWord_547884 prefixEnd_547884 93775944969346545010111 := by
  unfold tailWord_547884
  simp only [CollatzResearch.WordTrace]
  refine ⟨9991485573558656991365353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13321980764744875988487137 9991485573558656991365353)
  ·
    refine ⟨7493614180168992743524015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9991485573558656991365353 7493614180168992743524015)
    ·
      refine ⟨11240421270253489115286023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7493614180168992743524015 11240421270253489115286023)
      ·
        refine ⟨16860631905380233672929035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11240421270253489115286023 16860631905380233672929035)
        ·
          refine ⟨25290947858070350509393553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16860631905380233672929035 25290947858070350509393553)
          ·
            refine ⟨18968210893552762882045165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25290947858070350509393553 18968210893552762882045165)
            ·
              refine ⟨7113079085082286080766937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18968210893552762882045165 7113079085082286080766937)
              ·
                refine ⟨5334809313811714560575203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7113079085082286080766937 5334809313811714560575203)
                ·
                  refine ⟨8002213970717571840862805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5334809313811714560575203 8002213970717571840862805)
                  ·
                    refine ⟨93775944969346545010111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8002213970717571840862805 93775944969346545010111)
                    ·
                      rfl

theorem cell23_547884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 8].length) (baseStart_547884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547884 prefixEnd_547884 := by exact prefixLift 547884
  have htrace : WordTrace (prefixWord ++ tailWord_547884) baseStart_547884 baseEnd_547884 := by
    simpa [prefixWord, tailWord_547884, baseEnd_547884] using wordTrace_append hprefix tailTrace_547884
  have hstable : (prefixWord ++ tailWord_547884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547884).length < 2 ^ (prefixWord ++ tailWord_547884).sum := by decide
  have hdescent : baseEnd_547884 < baseStart_547884 := by decide
  rcases family_descends (prefixWord ++ tailWord_547884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547901 : List Nat := [1, 4, 1, 3, 1, 2, 1, 2, 2, 6]
def baseStart_547901 : Nat := 118140960795 + 547901 * 2 ^ 59
def prefixEnd_547901 : Nat := 4983230072969 + 3 ^ 40 * 547901 * 2
def baseEnd_547901 : Nat := 93778854693055356172585

theorem tailTrace_547901 : CollatzResearch.WordTrace tailWord_547901 prefixEnd_547901 93778854693055356172585 := by
  unfold tailWord_547901
  simp only [CollatzResearch.WordTrace]
  refine ⟨19983591188055725886099557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13322394125370483924066371 19983591188055725886099557)
  ·
    refine ⟨3746923347760448603643667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19983591188055725886099557 3746923347760448603643667)
    ·
      refine ⟨5620385021640672905465501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3746923347760448603643667 5620385021640672905465501)
      ·
        refine ⟨2107644383115252339549563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5620385021640672905465501 2107644383115252339549563)
        ·
          refine ⟨3161466574672878509324345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2107644383115252339549563 3161466574672878509324345)
          ·
            refine ⟨2371099931004658881993259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3161466574672878509324345 2371099931004658881993259)
            ·
              refine ⟨3556649896506988322989889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2371099931004658881993259 3556649896506988322989889)
              ·
                refine ⟨2667487422380241242242417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3556649896506988322989889 2667487422380241242242417)
                ·
                  refine ⟨2000615566785180931681813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2667487422380241242242417 2000615566785180931681813)
                  ·
                    refine ⟨93778854693055356172585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2000615566785180931681813 93778854693055356172585)
                    ·
                      rfl

theorem cell23_547901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_547901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547901 prefixEnd_547901 := by exact prefixLift 547901
  have htrace : WordTrace (prefixWord ++ tailWord_547901) baseStart_547901 baseEnd_547901 := by
    simpa [prefixWord, tailWord_547901, baseEnd_547901] using wordTrace_append hprefix tailTrace_547901
  have hstable : (prefixWord ++ tailWord_547901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547901).length < 2 ^ (prefixWord ++ tailWord_547901).sum := by decide
  have hdescent : baseEnd_547901 < baseStart_547901 := by decide
  rcases family_descends (prefixWord ++ tailWord_547901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547902 : List Nat := [4, 2, 1, 3, 1, 1, 3, 2, 2, 1, 3]
def baseStart_547902 : Nat := 118140960795 + 547902 * 2 ^ 59
def prefixEnd_547902 : Nat := 4983230072969 + 3 ^ 40 * 547902 * 2
def baseEnd_547902 : Nat := 281337077559820564605251

theorem tailTrace_547902 : CollatzResearch.WordTrace tailWord_547902 prefixEnd_547902 281337077559820564605251 := by
  unfold tailWord_547902
  simp only [CollatzResearch.WordTrace]
  refine ⟨2497953457631512882110745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13322418440701402037923973 2497953457631512882110745)
  ·
    refine ⟨1873465093223634661583059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2497953457631512882110745 1873465093223634661583059)
    ·
      refine ⟨2810197639835451992374589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1873465093223634661583059 2810197639835451992374589)
      ·
        refine ⟨1053824114938294497140471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2810197639835451992374589 1053824114938294497140471)
        ·
          refine ⟨1580736172407441745710707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1053824114938294497140471 1580736172407441745710707)
          ·
            refine ⟨2371104258611162618566061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1580736172407441745710707 2371104258611162618566061)
            ·
              refine ⟨889164096979185981962273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2371104258611162618566061 889164096979185981962273)
              ·
                refine ⟨666873072734389486471705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 889164096979185981962273 666873072734389486471705)
                ·
                  refine ⟨500154804550792114853779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 666873072734389486471705 500154804550792114853779)
                  ·
                    refine ⟨750232206826188172280669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 500154804550792114853779 750232206826188172280669)
                    ·
                      refine ⟨281337077559820564605251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 750232206826188172280669 281337077559820564605251)
                      ·
                        rfl

theorem cell23_547902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_547902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547902 prefixEnd_547902 := by exact prefixLift 547902
  have htrace : WordTrace (prefixWord ++ tailWord_547902) baseStart_547902 baseEnd_547902 := by
    simpa [prefixWord, tailWord_547902, baseEnd_547902] using wordTrace_append hprefix tailTrace_547902
  have hstable : (prefixWord ++ tailWord_547902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547902).length < 2 ^ (prefixWord ++ tailWord_547902).sum := by decide
  have hdescent : baseEnd_547902 < baseStart_547902 := by decide
  rcases family_descends (prefixWord ++ tailWord_547902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547921 : List Nat := [1, 2, 2, 1, 3, 1, 4, 1, 2, 2, 4]
def baseStart_547921 : Nat := 118140960795 + 547921 * 2 ^ 59
def prefixEnd_547921 : Nat := 4983230072969 + 3 ^ 40 * 547921 * 2
def baseEnd_547921 : Nat := 281346833692255990267663

theorem tailTrace_547921 : CollatzResearch.WordTrace tailWord_547921 prefixEnd_547921 281346833692255990267663 := by
  unfold tailWord_547921
  simp only [CollatzResearch.WordTrace]
  refine ⟨19984320647983269301827617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13322880431988846201218411 19984320647983269301827617)
  ·
    refine ⟨14988240485987451976370713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19984320647983269301827617 14988240485987451976370713)
    ·
      refine ⟨11241180364490588982278035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14988240485987451976370713 11241180364490588982278035)
      ·
        refine ⟨16861770546735883473417053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11241180364490588982278035 16861770546735883473417053)
        ·
          refine ⟨6323163955025956302531395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16861770546735883473417053 6323163955025956302531395)
          ·
            refine ⟨9484745932538934453797093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6323163955025956302531395 9484745932538934453797093)
            ·
              refine ⟨1778389862351050210086955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9484745932538934453797093 1778389862351050210086955)
              ·
                refine ⟨2667584793526575315130433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1778389862351050210086955 2667584793526575315130433)
                ·
                  refine ⟨2000688595144931486347825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2667584793526575315130433 2000688595144931486347825)
                  ·
                    refine ⟨1500516446358698614760869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2000688595144931486347825 1500516446358698614760869)
                    ·
                      refine ⟨281346833692255990267663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1500516446358698614760869 281346833692255990267663)
                      ·
                        rfl

theorem cell23_547921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_547921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547921 prefixEnd_547921 := by exact prefixLift 547921
  have htrace : WordTrace (prefixWord ++ tailWord_547921) baseStart_547921 baseEnd_547921 := by
    simpa [prefixWord, tailWord_547921, baseEnd_547921] using wordTrace_append hprefix tailTrace_547921
  have hstable : (prefixWord ++ tailWord_547921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547921).length < 2 ^ (prefixWord ++ tailWord_547921).sum := by decide
  have hdescent : baseEnd_547921 < baseStart_547921 := by decide
  rcases family_descends (prefixWord ++ tailWord_547921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547965 : List Nat := [1, 4, 1, 1, 3, 1, 5, 2, 5]
def baseStart_547965 : Nat := 118140960795 + 547965 * 2 ^ 59
def prefixEnd_547965 : Nat := 4983230072969 + 3 ^ 40 * 547965 * 2
def baseEnd_547965 : Nat := 31263269649005979790829

theorem tailTrace_547965 : CollatzResearch.WordTrace tailWord_547965 prefixEnd_547965 31263269649005979790829 := by
  unfold tailWord_547965
  simp only [CollatzResearch.WordTrace]
  refine ⟨19985925459823864816429349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13323950306549243210952899 19985925459823864816429349)
  ·
    refine ⟨3747361023716974653080503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19985925459823864816429349 3747361023716974653080503)
    ·
      refine ⟨5621041535575461979620755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3747361023716974653080503 5621041535575461979620755)
      ·
        refine ⟨8431562303363192969431133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5621041535575461979620755 8431562303363192969431133)
        ·
          refine ⟨3161835863761197363536675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8431562303363192969431133 3161835863761197363536675)
          ·
            refine ⟨4742753795641796045305013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3161835863761197363536675 4742753795641796045305013)
            ·
              refine ⟨444633168341418379247345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4742753795641796045305013 444633168341418379247345)
              ·
                refine ⟨333474876256063784435509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 444633168341418379247345 333474876256063784435509)
                ·
                  refine ⟨31263269649005979790829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 333474876256063784435509 31263269649005979790829)
                  ·
                    rfl

theorem cell23_547965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 2, 5].length) (baseStart_547965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547965 prefixEnd_547965 := by exact prefixLift 547965
  have htrace : WordTrace (prefixWord ++ tailWord_547965) baseStart_547965 baseEnd_547965 := by
    simpa [prefixWord, tailWord_547965, baseEnd_547965] using wordTrace_append hprefix tailTrace_547965
  have hstable : (prefixWord ++ tailWord_547965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547965).length < 2 ^ (prefixWord ++ tailWord_547965).sum := by decide
  have hdescent : baseEnd_547965 < baseStart_547965 := by decide
  rcases family_descends (prefixWord ++ tailWord_547965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547971 : List Nat := [1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 5]
def baseStart_547971 : Nat := 118140960795 + 547971 * 2 ^ 59
def prefixEnd_547971 : Nat := 4983230072969 + 3 ^ 40 * 547971 * 2
def baseEnd_547971 : Nat := 281372507724980794642433

theorem tailTrace_547971 : CollatzResearch.WordTrace tailWord_547971 prefixEnd_547971 281372507724980794642433 := by
  unfold tailWord_547971
  simp only [CollatzResearch.WordTrace]
  refine ⟨19986144297802127841147767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13324096198534751894098511 19986144297802127841147767)
  ·
    refine ⟨29979216446703191761721651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19986144297802127841147767 29979216446703191761721651)
    ·
      refine ⟨44968824670054787642582477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29979216446703191761721651 44968824670054787642582477)
      ·
        refine ⟨16863309251270545365968429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44968824670054787642582477 16863309251270545365968429)
        ·
          refine ⟨6323740969226454512238161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16863309251270545365968429 6323740969226454512238161)
          ·
            refine ⟨4742805726919840884178621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6323740969226454512238161 4742805726919840884178621)
            ·
              refine ⟨1778552147594940331566983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4742805726919840884178621 1778552147594940331566983)
              ·
                refine ⟨2667828221392410497350475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1778552147594940331566983 2667828221392410497350475)
                ·
                  refine ⟨4001742332088615746025713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2667828221392410497350475 4001742332088615746025713)
                  ·
                    refine ⟨3001306749066461809519285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4001742332088615746025713 3001306749066461809519285)
                    ·
                      refine ⟨281372507724980794642433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3001306749066461809519285 281372507724980794642433)
                      ·
                        rfl

theorem cell23_547971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_547971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547971 prefixEnd_547971 := by exact prefixLift 547971
  have htrace : WordTrace (prefixWord ++ tailWord_547971) baseStart_547971 baseEnd_547971 := by
    simpa [prefixWord, tailWord_547971, baseEnd_547971] using wordTrace_append hprefix tailTrace_547971
  have hstable : (prefixWord ++ tailWord_547971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547971).length < 2 ^ (prefixWord ++ tailWord_547971).sum := by decide
  have hdescent : baseEnd_547971 < baseStart_547971 := by decide
  rcases family_descends (prefixWord ++ tailWord_547971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547976 : List Nat := [2, 1, 3, 4, 2, 2, 2, 1, 2, 2, 2]
def baseStart_547976 : Nat := 118140960795 + 547976 * 2 ^ 59
def prefixEnd_547976 : Nat := 4983230072969 + 3 ^ 40 * 547976 * 2
def baseEnd_547976 : Nat := 281375075128253275079911

theorem tailTrace_547976 : CollatzResearch.WordTrace tailWord_547976 prefixEnd_547976 281375075128253275079911 := by
  unfold tailWord_547976
  simp only [CollatzResearch.WordTrace]
  refine ⟨9993163331392006847539891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13324217775189342463386521 9993163331392006847539891)
  ·
    refine ⟨14989744997088010271309837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9993163331392006847539891 14989744997088010271309837)
    ·
      refine ⟨5621154373908003851741189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14989744997088010271309837 5621154373908003851741189)
      ·
        refine ⟨1053966445107750722201473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5621154373908003851741189 1053966445107750722201473)
        ·
          refine ⟨790474833830813041651105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1053966445107750722201473 790474833830813041651105)
          ·
            refine ⟨592856125373109781238329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 790474833830813041651105 592856125373109781238329)
            ·
              refine ⟨444642094029832335928747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 592856125373109781238329 444642094029832335928747)
              ·
                refine ⟨666963141044748503893121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 444642094029832335928747 666963141044748503893121)
                ·
                  refine ⟨500222355783561377919841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 666963141044748503893121 500222355783561377919841)
                  ·
                    refine ⟨375166766837671033439881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 500222355783561377919841 375166766837671033439881)
                    ·
                      refine ⟨281375075128253275079911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 375166766837671033439881 281375075128253275079911)
                      ·
                        rfl

theorem cell23_547976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_547976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_547976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_547976 prefixEnd_547976 := by exact prefixLift 547976
  have htrace : WordTrace (prefixWord ++ tailWord_547976) baseStart_547976 baseEnd_547976 := by
    simpa [prefixWord, tailWord_547976, baseEnd_547976] using wordTrace_append hprefix tailTrace_547976
  have hstable : (prefixWord ++ tailWord_547976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547976).length < 2 ^ (prefixWord ++ tailWord_547976).sum := by decide
  have hdescent : baseEnd_547976 < baseStart_547976 := by decide
  rcases family_descends (prefixWord ++ tailWord_547976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548052 : List Nat := [2, 4, 1, 4, 1, 1, 1, 1, 1, 4, 3]
def baseStart_548052 : Nat := 118140960795 + 548052 * 2 ^ 59
def prefixEnd_548052 : Nat := 4983230072969 + 3 ^ 40 * 548052 * 2
def baseEnd_548052 : Nat := 281414099657994977729561

theorem tailTrace_548052 : CollatzResearch.WordTrace tailWord_548052 prefixEnd_548052 281414099657994977729561 := by
  unfold tailWord_548052
  simp only [CollatzResearch.WordTrace]
  refine ⟨9994549305254339337423205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13326065740339119116564273 9994549305254339337423205)
  ·
    refine ⟨1873977994735188625766851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9994549305254339337423205 1873977994735188625766851)
    ·
      refine ⟨2810966992102782938650277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1873977994735188625766851 2810966992102782938650277)
      ·
        refine ⟨527056311019271800996927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2810966992102782938650277 527056311019271800996927)
        ·
          refine ⟨790584466528907701495391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 527056311019271800996927 790584466528907701495391)
          ·
            refine ⟨1185876699793361552243087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 790584466528907701495391 1185876699793361552243087)
            ·
              refine ⟨1778815049690042328364631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1185876699793361552243087 1778815049690042328364631)
              ·
                refine ⟨2668222574535063492546947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1778815049690042328364631 2668222574535063492546947)
                ·
                  refine ⟨4002333861802595238820421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2668222574535063492546947 4002333861802595238820421)
                  ·
                    refine ⟨750437599087986607278829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4002333861802595238820421 750437599087986607278829)
                    ·
                      refine ⟨281414099657994977729561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 750437599087986607278829 281414099657994977729561)
                      ·
                        rfl

theorem cell23_548052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_548052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548052 prefixEnd_548052 := by exact prefixLift 548052
  have htrace : WordTrace (prefixWord ++ tailWord_548052) baseStart_548052 baseEnd_548052 := by
    simpa [prefixWord, tailWord_548052, baseEnd_548052] using wordTrace_append hprefix tailTrace_548052
  have hstable : (prefixWord ++ tailWord_548052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548052).length < 2 ^ (prefixWord ++ tailWord_548052).sum := by decide
  have hdescent : baseEnd_548052 < baseStart_548052 := by decide
  rcases family_descends (prefixWord ++ tailWord_548052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548105 : List Nat := [1, 2, 1, 1, 3, 3, 4, 2, 1, 1, 4]
def baseStart_548105 : Nat := 118140960795 + 548105 * 2 ^ 59
def prefixEnd_548105 : Nat := 4983230072969 + 3 ^ 40 * 548105 * 2
def baseEnd_548105 : Nat := 281441314132683270366817

theorem tailTrace_548105 : CollatzResearch.WordTrace tailWord_548105 prefixEnd_548105 281441314132683270366817 := by
  unfold tailWord_548105
  simp only [CollatzResearch.WordTrace]
  refine ⟨19991031679316668726525769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13327354452877779151017179 19991031679316668726525769)
  ·
    refine ⟨14993273759487501544894327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19991031679316668726525769 14993273759487501544894327)
    ·
      refine ⟨22489910639231252317341491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14993273759487501544894327 22489910639231252317341491)
      ·
        refine ⟨33734865958846878476012237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22489910639231252317341491 33734865958846878476012237)
        ·
          refine ⟨12650574734567579428504589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33734865958846878476012237 12650574734567579428504589)
          ·
            refine ⟨4743965525462842285689221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12650574734567579428504589 4743965525462842285689221)
            ·
              refine ⟨889493536024282928566729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4743965525462842285689221 889493536024282928566729)
              ·
                refine ⟨667120152018212196425047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 889493536024282928566729 667120152018212196425047)
                ·
                  refine ⟨1000680228027318294637571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 667120152018212196425047 1000680228027318294637571)
                  ·
                    refine ⟨1501020342040977441956357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1000680228027318294637571 1501020342040977441956357)
                    ·
                      refine ⟨281441314132683270366817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1501020342040977441956357 281441314132683270366817)
                      ·
                        rfl

theorem cell23_548105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 1, 1, 4].length) (baseStart_548105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548105 prefixEnd_548105 := by exact prefixLift 548105
  have htrace : WordTrace (prefixWord ++ tailWord_548105) baseStart_548105 baseEnd_548105 := by
    simpa [prefixWord, tailWord_548105, baseEnd_548105] using wordTrace_append hprefix tailTrace_548105
  have hstable : (prefixWord ++ tailWord_548105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548105).length < 2 ^ (prefixWord ++ tailWord_548105).sum := by decide
  have hdescent : baseEnd_548105 < baseStart_548105 := by decide
  rcases family_descends (prefixWord ++ tailWord_548105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548125 : List Nat := [1, 4, 2, 3, 1, 1, 1, 3, 1, 1, 5]
def baseStart_548125 : Nat := 118140960795 + 548125 * 2 ^ 59
def prefixEnd_548125 : Nat := 4983230072969 + 3 ^ 40 * 548125 * 2
def baseEnd_548125 : Nat := 281451583745773192116725

theorem tailTrace_548125 : CollatzResearch.WordTrace tailWord_548125 prefixEnd_548125 281451583745773192116725 := by
  unfold tailWord_548125
  simp only [CollatzResearch.WordTrace]
  refine ⟨19991761139244212142253829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13327840759496141428169219 19991761139244212142253829)
  ·
    refine ⟨3748455213608289776672593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19991761139244212142253829 3748455213608289776672593)
    ·
      refine ⟨2811341410206217332504445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3748455213608289776672593 2811341410206217332504445)
      ·
        refine ⟨1054253028827331499689167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2811341410206217332504445 1054253028827331499689167)
        ·
          refine ⟨1581379543240997249533751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1054253028827331499689167 1581379543240997249533751)
          ·
            refine ⟨2372069314861495874300627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1581379543240997249533751 2372069314861495874300627)
            ·
              refine ⟨3558103972292243811450941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2372069314861495874300627 3558103972292243811450941)
              ·
                refine ⟨1334288989609591429294103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3558103972292243811450941 1334288989609591429294103)
                ·
                  refine ⟨2001433484414387143941155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1334288989609591429294103 2001433484414387143941155)
                  ·
                    refine ⟨3002150226621580715911733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2001433484414387143941155 3002150226621580715911733)
                    ·
                      refine ⟨281451583745773192116725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3002150226621580715911733 281451583745773192116725)
                      ·
                        rfl

theorem cell23_548125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_548125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548125 prefixEnd_548125 := by exact prefixLift 548125
  have htrace : WordTrace (prefixWord ++ tailWord_548125) baseStart_548125 baseEnd_548125 := by
    simpa [prefixWord, tailWord_548125, baseEnd_548125] using wordTrace_append hprefix tailTrace_548125
  have hstable : (prefixWord ++ tailWord_548125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548125).length < 2 ^ (prefixWord ++ tailWord_548125).sum := by decide
  have hdescent : baseEnd_548125 < baseStart_548125 := by decide
  rcases family_descends (prefixWord ++ tailWord_548125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548126 : List Nat := [4, 3, 2, 1, 2, 1, 1, 2, 2, 3, 2]
def baseStart_548126 : Nat := 118140960795 + 548126 * 2 ^ 59
def prefixEnd_548126 : Nat := 4983230072969 + 3 ^ 40 * 548126 * 2
def baseEnd_548126 : Nat := 281452097226427688204221

theorem tailTrace_548126 : CollatzResearch.WordTrace tailWord_548126 prefixEnd_548126 281452097226427688204221 := by
  unfold tailWord_548126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2498974701530073664130029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13327865074827059542026821 2498974701530073664130029)
  ·
    refine ⟨937115513073777624048761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2498974701530073664130029 937115513073777624048761)
    ·
      refine ⟨702836634805333218036571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 937115513073777624048761 702836634805333218036571)
      ·
        refine ⟨1054254952207999827054857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 702836634805333218036571 1054254952207999827054857)
        ·
          refine ⟨790691214155999870291143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1054254952207999827054857 790691214155999870291143)
          ·
            refine ⟨1186036821233999805436715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 790691214155999870291143 1186036821233999805436715)
            ·
              refine ⟨1779055231850999708155073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1186036821233999805436715 1779055231850999708155073)
              ·
                refine ⟨1334291423888249781116305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1779055231850999708155073 1334291423888249781116305)
                ·
                  refine ⟨1000718567916187335837229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1334291423888249781116305 1000718567916187335837229)
                  ·
                    refine ⟨375269462968570250938961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1000718567916187335837229 375269462968570250938961)
                    ·
                      refine ⟨281452097226427688204221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 375269462968570250938961 281452097226427688204221)
                      ·
                        rfl

theorem cell23_548126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_548126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548126 prefixEnd_548126 := by exact prefixLift 548126
  have htrace : WordTrace (prefixWord ++ tailWord_548126) baseStart_548126 baseEnd_548126 := by
    simpa [prefixWord, tailWord_548126, baseEnd_548126] using wordTrace_append hprefix tailTrace_548126
  have hstable : (prefixWord ++ tailWord_548126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548126).length < 2 ^ (prefixWord ++ tailWord_548126).sum := by decide
  have hdescent : baseEnd_548126 < baseStart_548126 := by decide
  rcases family_descends (prefixWord ++ tailWord_548126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548149 : List Nat := [1, 3, 3, 1, 2, 4, 2, 1, 2, 4]
def baseStart_548149 : Nat := 118140960795 + 548149 * 2 ^ 59
def prefixEnd_548149 : Nat := 4983230072969 + 3 ^ 40 * 548149 * 2
def baseEnd_548149 : Nat := 93821302427160366072205

theorem tailTrace_548149 : CollatzResearch.WordTrace tailWord_548149 prefixEnd_548149 93821302427160366072205 := by
  unfold tailWord_548149
  simp only [CollatzResearch.WordTrace]
  refine ⟨19992636491157264241127501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13328424327438176160751667 19992636491157264241127501)
  ·
    refine ⟨7497238684183974090422813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19992636491157264241127501 7497238684183974090422813)
    ·
      refine ⟨2811464506568990283908555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7497238684183974090422813 2811464506568990283908555)
      ·
        refine ⟨4217196759853485425862833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2811464506568990283908555 4217196759853485425862833)
        ·
          refine ⟨3162897569890114069397125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4217196759853485425862833 3162897569890114069397125)
          ·
            refine ⟨593043294354396388011961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3162897569890114069397125 593043294354396388011961)
            ·
              refine ⟨444782470765797291008971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 593043294354396388011961 444782470765797291008971)
              ·
                refine ⟨667173706148695936513457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 444782470765797291008971 667173706148695936513457)
                ·
                  refine ⟨500380279611521952385093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 667173706148695936513457 500380279611521952385093)
                  ·
                    refine ⟨93821302427160366072205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 500380279611521952385093 93821302427160366072205)
                    ·
                      rfl

theorem cell23_548149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_548149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548149 prefixEnd_548149 := by exact prefixLift 548149
  have htrace : WordTrace (prefixWord ++ tailWord_548149) baseStart_548149 baseEnd_548149 := by
    simpa [prefixWord, tailWord_548149, baseEnd_548149] using wordTrace_append hprefix tailTrace_548149
  have hstable : (prefixWord ++ tailWord_548149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548149).length < 2 ^ (prefixWord ++ tailWord_548149).sum := by decide
  have hdescent : baseEnd_548149 < baseStart_548149 := by decide
  rcases family_descends (prefixWord ++ tailWord_548149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548205 : List Nat := [1, 5, 1, 1, 1, 4, 1, 1, 2, 6]
def baseStart_548205 : Nat := 118140960795 + 548205 * 2 ^ 59
def prefixEnd_548205 : Nat := 4983230072969 + 3 ^ 40 * 548205 * 2
def baseEnd_548205 : Nat := 93830887399377626372119

theorem tailTrace_548205 : CollatzResearch.WordTrace tailWord_548205 prefixEnd_548205 93830887399377626372119 := by
  unfold tailWord_548205
  simp only [CollatzResearch.WordTrace]
  refine ⟨19994678978954385805166069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13329785985969590536777379 19994678978954385805166069)
  ·
    refine ⟨1874501154276973669234319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19994678978954385805166069 1874501154276973669234319)
    ·
      refine ⟨2811751731415460503851479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1874501154276973669234319 2811751731415460503851479)
      ·
        refine ⟨4217627597123190755777219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2811751731415460503851479 4217627597123190755777219)
        ·
          refine ⟨6326441395684786133665829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4217627597123190755777219 6326441395684786133665829)
          ·
            refine ⟨1186207761690897400062343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6326441395684786133665829 1186207761690897400062343)
            ·
              refine ⟨1779311642536346100093515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1186207761690897400062343 1779311642536346100093515)
              ·
                refine ⟨2668967463804519150140273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1779311642536346100093515 2668967463804519150140273)
                ·
                  refine ⟨2001725597853389362605205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2668967463804519150140273 2001725597853389362605205)
                  ·
                    refine ⟨93830887399377626372119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2001725597853389362605205 93830887399377626372119)
                    ·
                      rfl

theorem cell23_548205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_548205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548205 prefixEnd_548205 := by exact prefixLift 548205
  have htrace : WordTrace (prefixWord ++ tailWord_548205) baseStart_548205 baseEnd_548205 := by
    simpa [prefixWord, tailWord_548205, baseEnd_548205] using wordTrace_append hprefix tailTrace_548205
  have hstable : (prefixWord ++ tailWord_548205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548205).length < 2 ^ (prefixWord ++ tailWord_548205).sum := by decide
  have hdescent : baseEnd_548205 < baseStart_548205 := by decide
  rcases family_descends (prefixWord ++ tailWord_548205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548218 : List Nat := [3, 1, 1, 1, 1, 1, 2, 6, 7]
def baseStart_548218 : Nat := 118140960795 + 548218 * 2 ^ 59
def prefixEnd_548218 : Nat := 4983230072969 + 3 ^ 40 * 548218 * 2
def baseEnd_548218 : Nat := 31277704160737925361533

theorem tailTrace_548218 : CollatzResearch.WordTrace tailWord_548218 prefixEnd_548218 31277704160737925361533 := by
  unfold tailWord_548218
  simp only [CollatzResearch.WordTrace]
  refine ⟨4998788281976822256347327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13330102085271526016926205 4998788281976822256347327)
  ·
    refine ⟨7498182422965233384520991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4998788281976822256347327 7498182422965233384520991)
    ·
      refine ⟨11247273634447850076781487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7498182422965233384520991 11247273634447850076781487)
      ·
        refine ⟨16870910451671775115172231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11247273634447850076781487 16870910451671775115172231)
        ·
          refine ⟨25306365677507662672758347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16870910451671775115172231 25306365677507662672758347)
          ·
            refine ⟨37959548516261494009137521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25306365677507662672758347 37959548516261494009137521)
            ·
              refine ⟨28469661387196120506853141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37959548516261494009137521 28469661387196120506853141)
              ·
                refine ⟨1334515377524818148758741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28469661387196120506853141 1334515377524818148758741)
                ·
                  refine ⟨31277704160737925361533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1334515377524818148758741 31277704160737925361533)
                  ·
                    rfl

theorem cell23_548218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 7].length) (baseStart_548218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548218 prefixEnd_548218 := by exact prefixLift 548218
  have htrace : WordTrace (prefixWord ++ tailWord_548218) baseStart_548218 baseEnd_548218 := by
    simpa [prefixWord, tailWord_548218, baseEnd_548218] using wordTrace_append hprefix tailTrace_548218
  have hstable : (prefixWord ++ tailWord_548218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548218).length < 2 ^ (prefixWord ++ tailWord_548218).sum := by decide
  have hdescent : baseEnd_548218 < baseStart_548218 := by decide
  rcases family_descends (prefixWord ++ tailWord_548218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548233 : List Nat := [1, 2, 1, 1, 8, 1, 2, 1, 1, 3, 2]
def baseStart_548233 : Nat := 118140960795 + 548233 * 2 ^ 59
def prefixEnd_548233 : Nat := 4983230072969 + 3 ^ 40 * 548233 * 2
def baseEnd_548233 : Nat := 281507039656458769566229

theorem tailTrace_548233 : CollatzResearch.WordTrace tailWord_548233 prefixEnd_548233 281507039656458769566229 := by
  unfold tailWord_548233
  simp only [CollatzResearch.WordTrace]
  refine ⟨19995700222852946587185353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13330466815235297724790235 19995700222852946587185353)
  ·
    refine ⟨14996775167139709940389015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19995700222852946587185353 14996775167139709940389015)
    ·
      refine ⟨22495162750709564910583523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14996775167139709940389015 22495162750709564910583523)
      ·
        refine ⟨33742744126064347365875285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22495162750709564910583523 33742744126064347365875285)
        ·
          refine ⟨395422782727316570693851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 33742744126064347365875285 395422782727316570693851)
          ·
            refine ⟨593134174090974856040777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395422782727316570693851 593134174090974856040777)
            ·
              refine ⟨444850630568231142030583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 593134174090974856040777 444850630568231142030583)
              ·
                refine ⟨667275945852346713045875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 444850630568231142030583 667275945852346713045875)
                ·
                  refine ⟨1000913918778520069568813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 667275945852346713045875 1000913918778520069568813)
                  ·
                    refine ⟨375342719541945026088305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1000913918778520069568813 375342719541945026088305)
                    ·
                      refine ⟨281507039656458769566229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 375342719541945026088305 281507039656458769566229)
                      ·
                        rfl

theorem cell23_548233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 1, 3, 2].length) (baseStart_548233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548233 prefixEnd_548233 := by exact prefixLift 548233
  have htrace : WordTrace (prefixWord ++ tailWord_548233) baseStart_548233 baseEnd_548233 := by
    simpa [prefixWord, tailWord_548233, baseEnd_548233] using wordTrace_append hprefix tailTrace_548233
  have hstable : (prefixWord ++ tailWord_548233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548233).length < 2 ^ (prefixWord ++ tailWord_548233).sum := by decide
  have hdescent : baseEnd_548233 < baseStart_548233 := by decide
  rcases family_descends (prefixWord ++ tailWord_548233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548245 : List Nat := [1, 3, 2, 1, 1, 2, 3, 2, 2, 3, 3]
def baseStart_548245 : Nat := 118140960795 + 548245 * 2 ^ 59
def prefixEnd_548245 : Nat := 4983230072969 + 3 ^ 40 * 548245 * 2
def baseEnd_548245 : Nat := 281513201424312722616173

theorem tailTrace_548245 : CollatzResearch.WordTrace tailWord_548245 prefixEnd_548245 281513201424312722616173 := by
  unfold tailWord_548245
  simp only [CollatzResearch.WordTrace]
  refine ⟨19996137898809472636622189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13330758599206315091081459 19996137898809472636622189)
  ·
    refine ⟨7498551712053552238733321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19996137898809472636622189 7498551712053552238733321)
    ·
      refine ⟨5623913784040164179049991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7498551712053552238733321 5623913784040164179049991)
      ·
        refine ⟨8435870676060246268574987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5623913784040164179049991 8435870676060246268574987)
        ·
          refine ⟨12653806014090369402862481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8435870676060246268574987 12653806014090369402862481)
          ·
            refine ⟨9490354510567777052146861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12653806014090369402862481 9490354510567777052146861)
            ·
              refine ⟨3558882941462916394555073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9490354510567777052146861 3558882941462916394555073)
              ·
                refine ⟨2669162206097187295916305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3558882941462916394555073 2669162206097187295916305)
                ·
                  refine ⟨2001871654572890471937229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2669162206097187295916305 2001871654572890471937229)
                  ·
                    refine ⟨750701870464833926976461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2001871654572890471937229 750701870464833926976461)
                    ·
                      refine ⟨281513201424312722616173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 750701870464833926976461 281513201424312722616173)
                      ·
                        rfl

theorem cell23_548245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_548245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548245 prefixEnd_548245 := by exact prefixLift 548245
  have htrace : WordTrace (prefixWord ++ tailWord_548245) baseStart_548245 baseEnd_548245 := by
    simpa [prefixWord, tailWord_548245, baseEnd_548245] using wordTrace_append hprefix tailTrace_548245
  have hstable : (prefixWord ++ tailWord_548245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548245).length < 2 ^ (prefixWord ++ tailWord_548245).sum := by decide
  have hdescent : baseEnd_548245 < baseStart_548245 := by decide
  rcases family_descends (prefixWord ++ tailWord_548245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548285 : List Nat := [1, 4, 1, 2, 2, 1, 1, 3, 1, 3, 4]
def baseStart_548285 : Nat := 118140960795 + 548285 * 2 ^ 59
def prefixEnd_548285 : Nat := 4983230072969 + 3 ^ 40 * 548285 * 2
def baseEnd_548285 : Nat := 281533740650492566115989

theorem tailTrace_548285 : CollatzResearch.WordTrace tailWord_548285 prefixEnd_548285 281533740650492566115989 := by
  unfold tailWord_548285
  simp only [CollatzResearch.WordTrace]
  refine ⟨19997596818664559468078309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13331731212443039645385539 19997596818664559468078309)
  ·
    refine ⟨3749549403499604900264683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19997596818664559468078309 3749549403499604900264683)
    ·
      refine ⟨5624324105249407350397025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3749549403499604900264683 5624324105249407350397025)
      ·
        refine ⟨4218243078937055512797769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5624324105249407350397025 4218243078937055512797769)
        ·
          refine ⟨3163682309202791634598327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4218243078937055512797769 3163682309202791634598327)
          ·
            refine ⟨4745523463804187451897491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3163682309202791634598327 4745523463804187451897491)
            ·
              refine ⟨7118285195706281177846237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4745523463804187451897491 7118285195706281177846237)
              ·
                refine ⟨2669356948389855441692339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7118285195706281177846237 2669356948389855441692339)
                ·
                  refine ⟨4004035422584783162538509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2669356948389855441692339 4004035422584783162538509)
                  ·
                    refine ⟨1501513283469293685951941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4004035422584783162538509 1501513283469293685951941)
                    ·
                      refine ⟨281533740650492566115989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1501513283469293685951941 281533740650492566115989)
                      ·
                        rfl

theorem cell23_548285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_548285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548285 prefixEnd_548285 := by exact prefixLift 548285
  have htrace : WordTrace (prefixWord ++ tailWord_548285) baseStart_548285 baseEnd_548285 := by
    simpa [prefixWord, tailWord_548285, baseEnd_548285] using wordTrace_append hprefix tailTrace_548285
  have hstable : (prefixWord ++ tailWord_548285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548285).length < 2 ^ (prefixWord ++ tailWord_548285).sum := by decide
  have hdescent : baseEnd_548285 < baseStart_548285 := by decide
  rcases family_descends (prefixWord ++ tailWord_548285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548302 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2]
def baseStart_548302 : Nat := 118140960795 + 548302 * 2 ^ 59
def prefixEnd_548302 : Nat := 4983230072969 + 3 ^ 40 * 548302 * 2
def baseEnd_548302 : Nat := 281542469821618999603411

theorem tailTrace_548302 : CollatzResearch.WordTrace tailWord_548302 prefixEnd_548302 281542469821618999603411 := by
  unfold tailWord_548302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2499777107450371421430895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13332144573068647580964773 2499777107450371421430895)
  ·
    refine ⟨3749665661175557132146343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2499777107450371421430895 3749665661175557132146343)
    ·
      refine ⟨5624498491763335698219515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3749665661175557132146343 5624498491763335698219515)
      ·
        refine ⟨8436747737645003547329273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5624498491763335698219515 8436747737645003547329273)
        ·
          refine ⟨6327560803233752660496955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8436747737645003547329273 6327560803233752660496955)
          ·
            refine ⟨9491341204850628990745433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6327560803233752660496955 9491341204850628990745433)
            ·
              refine ⟨7118505903637971743059075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9491341204850628990745433 7118505903637971743059075)
              ·
                refine ⟨10677758855456957614588613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7118505903637971743059075 10677758855456957614588613)
                ·
                  refine ⟨2002079785398179552735365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10677758855456957614588613 2002079785398179552735365)
                  ·
                    refine ⟨375389959762158666137881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2002079785398179552735365 375389959762158666137881)
                    ·
                      refine ⟨281542469821618999603411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 375389959762158666137881 281542469821618999603411)
                      ·
                        rfl

theorem cell23_548302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2].length) (baseStart_548302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548302 prefixEnd_548302 := by exact prefixLift 548302
  have htrace : WordTrace (prefixWord ++ tailWord_548302) baseStart_548302 baseEnd_548302 := by
    simpa [prefixWord, tailWord_548302, baseEnd_548302] using wordTrace_append hprefix tailTrace_548302
  have hstable : (prefixWord ++ tailWord_548302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548302).length < 2 ^ (prefixWord ++ tailWord_548302).sum := by decide
  have hdescent : baseEnd_548302 < baseStart_548302 := by decide
  rcases family_descends (prefixWord ++ tailWord_548302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548312 : List Nat := [2, 1, 2, 2, 2, 1, 5, 1, 3, 4]
def baseStart_548312 : Nat := 118140960795 + 548312 * 2 ^ 59
def prefixEnd_548312 : Nat := 4983230072969 + 3 ^ 40 * 548312 * 2
def baseEnd_548312 : Nat := 93849201542721320159455

theorem tailTrace_548312 : CollatzResearch.WordTrace tailWord_548312 prefixEnd_548312 93849201542721320159455 := by
  unfold tailWord_548312
  simp only [CollatzResearch.WordTrace]
  refine ⟨9999290794783371539655595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13332387726377828719540793 9999290794783371539655595)
  ·
    refine ⟨14998936192175057309483393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9999290794783371539655595 14998936192175057309483393)
    ·
      refine ⟨11249202144131292982112545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14998936192175057309483393 11249202144131292982112545)
      ·
        refine ⟨8436901608098469736584409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11249202144131292982112545 8436901608098469736584409)
        ·
          refine ⟨6327676206073852302438307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8436901608098469736584409 6327676206073852302438307)
          ·
            refine ⟨9491514309110778453657461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6327676206073852302438307 9491514309110778453657461)
            ·
              refine ⟨889829466479135480030387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9491514309110778453657461 889829466479135480030387)
              ·
                refine ⟨1334744199718703220045581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 889829466479135480030387 1334744199718703220045581)
                ·
                  refine ⟨500529074894513707517093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1334744199718703220045581 500529074894513707517093)
                  ·
                    refine ⟨93849201542721320159455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 500529074894513707517093 93849201542721320159455)
                    ·
                      rfl

theorem cell23_548312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 3, 4].length) (baseStart_548312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548312 prefixEnd_548312 := by exact prefixLift 548312
  have htrace : WordTrace (prefixWord ++ tailWord_548312) baseStart_548312 baseEnd_548312 := by
    simpa [prefixWord, tailWord_548312, baseEnd_548312] using wordTrace_append hprefix tailTrace_548312
  have hstable : (prefixWord ++ tailWord_548312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548312).length < 2 ^ (prefixWord ++ tailWord_548312).sum := by decide
  have hdescent : baseEnd_548312 < baseStart_548312 := by decide
  rcases family_descends (prefixWord ++ tailWord_548312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548335 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 2, 5, 3]
def baseStart_548335 : Nat := 118140960795 + 548335 * 2 ^ 59
def prefixEnd_548335 : Nat := 4983230072969 + 3 ^ 40 * 548335 * 2
def baseEnd_548335 : Nat := 281559414683217370490759

theorem tailTrace_548335 : CollatzResearch.WordTrace tailWord_548335 prefixEnd_548335 281559414683217370490759 := by
  unfold tailWord_548335
  simp only [CollatzResearch.WordTrace]
  refine ⟨19999420468483418007398459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13332946978988945338265639 19999420468483418007398459)
  ·
    refine ⟨29999130702725127011097689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19999420468483418007398459 29999130702725127011097689)
    ·
      refine ⟨22499348027043845258323267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29999130702725127011097689 22499348027043845258323267)
      ·
        refine ⟨33749022040565767887484901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22499348027043845258323267 33749022040565767887484901)
        ·
          refine ⟨6327941632606081478903419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33749022040565767887484901 6327941632606081478903419)
          ·
            refine ⟨9491912448909122218355129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6327941632606081478903419 9491912448909122218355129)
            ·
              refine ⟨7118934336681841663766347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9491912448909122218355129 7118934336681841663766347)
              ·
                refine ⟨10678401505022762495649521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7118934336681841663766347 10678401505022762495649521)
                ·
                  refine ⟨8008801128767071871737141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10678401505022762495649521 8008801128767071871737141)
                  ·
                    refine ⟨750825105821912987975357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8008801128767071871737141 750825105821912987975357)
                    ·
                      refine ⟨281559414683217370490759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 750825105821912987975357 281559414683217370490759)
                      ·
                        rfl

theorem cell23_548335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 5, 3].length) (baseStart_548335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548335 prefixEnd_548335 := by exact prefixLift 548335
  have htrace : WordTrace (prefixWord ++ tailWord_548335) baseStart_548335 baseEnd_548335 := by
    simpa [prefixWord, tailWord_548335, baseEnd_548335] using wordTrace_append hprefix tailTrace_548335
  have hstable : (prefixWord ++ tailWord_548335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548335).length < 2 ^ (prefixWord ++ tailWord_548335).sum := by decide
  have hdescent : baseEnd_548335 < baseStart_548335 := by decide
  rcases family_descends (prefixWord ++ tailWord_548335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548363 : List Nat := [1, 1, 1, 1, 8, 2, 2, 2, 1, 4]
def baseStart_548363 : Nat := 118140960795 + 548363 * 2 ^ 59
def prefixEnd_548363 : Nat := 4983230072969 + 3 ^ 40 * 548363 * 2
def baseEnd_548363 : Nat := 93857930713847753646877

theorem tailTrace_548363 : CollatzResearch.WordTrace tailWord_548363 prefixEnd_548363 93857930713847753646877 := by
  unfold tailWord_548363
  simp only [CollatzResearch.WordTrace]
  refine ⟨20000441712381978789417743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13333627808254652526278495 20000441712381978789417743)
  ·
    refine ⟨30000662568572968184126615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20000441712381978789417743 30000662568572968184126615)
    ·
      refine ⟨45000993852859452276189923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30000662568572968184126615 45000993852859452276189923)
      ·
        refine ⟨67501490779289178414284885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45000993852859452276189923 67501490779289178414284885)
        ·
          refine ⟨791033095069795059542401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 67501490779289178414284885 791033095069795059542401)
          ·
            refine ⟨593274821302346294656801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 791033095069795059542401 593274821302346294656801)
            ·
              refine ⟨444956115976759720992601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 593274821302346294656801 444956115976759720992601)
              ·
                refine ⟨333717086982569790744451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 444956115976759720992601 333717086982569790744451)
                ·
                  refine ⟨500575630473854686116677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 333717086982569790744451 500575630473854686116677)
                  ·
                    refine ⟨93857930713847753646877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 500575630473854686116677 93857930713847753646877)
                    ·
                      rfl

theorem cell23_548363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 2, 1, 4].length) (baseStart_548363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548363 prefixEnd_548363 := by exact prefixLift 548363
  have htrace : WordTrace (prefixWord ++ tailWord_548363) baseStart_548363 baseEnd_548363 := by
    simpa [prefixWord, tailWord_548363, baseEnd_548363] using wordTrace_append hprefix tailTrace_548363
  have hstable : (prefixWord ++ tailWord_548363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548363).length < 2 ^ (prefixWord ++ tailWord_548363).sum := by decide
  have hdescent : baseEnd_548363 < baseStart_548363 := by decide
  rcases family_descends (prefixWord ++ tailWord_548363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548402 : List Nat := [3, 2, 1, 1, 2, 1, 1, 4, 4, 4]
def baseStart_548402 : Nat := 118140960795 + 548402 * 2 ^ 59
def prefixEnd_548402 : Nat := 4983230072969 + 3 ^ 40 * 548402 * 2
def baseEnd_548402 : Nat := 93864605962356202784317

theorem tailTrace_548402 : CollatzResearch.WordTrace tailWord_548402 prefixEnd_548402 93864605962356202784317 := by
  unfold tailWord_548402
  simp only [CollatzResearch.WordTrace]
  refine ⟨5000466039810172112521865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13334576106160458966724973 5000466039810172112521865)
  ·
    refine ⟨3750349529857629084391399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5000466039810172112521865 3750349529857629084391399)
    ·
      refine ⟨5625524294786443626587099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3750349529857629084391399 5625524294786443626587099)
      ·
        refine ⟨8438286442179665439880649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5625524294786443626587099 8438286442179665439880649)
        ·
          refine ⟨6328714831634749079910487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8438286442179665439880649 6328714831634749079910487)
          ·
            refine ⟨9493072247452123619865731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6328714831634749079910487 9493072247452123619865731)
            ·
              refine ⟨14239608371178185429798597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9493072247452123619865731 14239608371178185429798597)
              ·
                refine ⟨2669926569595909768087237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14239608371178185429798597 2669926569595909768087237)
                ·
                  refine ⟨500611231799233081516357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2669926569595909768087237 500611231799233081516357)
                  ·
                    refine ⟨93864605962356202784317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 500611231799233081516357 93864605962356202784317)
                    ·
                      rfl

theorem cell23_548402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_548402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548402 prefixEnd_548402 := by exact prefixLift 548402
  have htrace : WordTrace (prefixWord ++ tailWord_548402) baseStart_548402 baseEnd_548402 := by
    simpa [prefixWord, tailWord_548402, baseEnd_548402] using wordTrace_append hprefix tailTrace_548402
  have hstable : (prefixWord ++ tailWord_548402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548402).length < 2 ^ (prefixWord ++ tailWord_548402).sum := by decide
  have hdescent : baseEnd_548402 < baseStart_548402 := by decide
  rcases family_descends (prefixWord ++ tailWord_548402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548406 : List Nat := [5, 1, 2, 1, 3, 1, 1, 3, 1, 5]
def baseStart_548406 : Nat := 118140960795 + 548406 * 2 ^ 59
def prefixEnd_548406 : Nat := 4983230072969 + 3 ^ 40 * 548406 * 2
def baseEnd_548406 : Nat := 93865290603228864234311

theorem tailTrace_548406 : CollatzResearch.WordTrace tailWord_548406 prefixEnd_548406 93865290603228864234311 := by
  unfold tailWord_548406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1250125628201637320827067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13334673367484131422155381 1250125628201637320827067)
  ·
    refine ⟨1875188442302455981240601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1250125628201637320827067 1875188442302455981240601)
    ·
      refine ⟨1406391331726841985930451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1875188442302455981240601 1406391331726841985930451)
      ·
        refine ⟨2109586997590262978895677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1406391331726841985930451 2109586997590262978895677)
        ·
          refine ⟨791095124096348617085879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2109586997590262978895677 791095124096348617085879)
          ·
            refine ⟨1186642686144522925628819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 791095124096348617085879 1186642686144522925628819)
            ·
              refine ⟨1779964029216784388443229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1186642686144522925628819 1779964029216784388443229)
              ·
                refine ⟨667486510956294145666211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1779964029216784388443229 667486510956294145666211)
                ·
                  refine ⟨1001229766434441218499317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 667486510956294145666211 1001229766434441218499317)
                  ·
                    refine ⟨93865290603228864234311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1001229766434441218499317 93865290603228864234311)
                    ·
                      rfl

theorem cell23_548406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_548406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548406 prefixEnd_548406 := by exact prefixLift 548406
  have htrace : WordTrace (prefixWord ++ tailWord_548406) baseStart_548406 baseEnd_548406 := by
    simpa [prefixWord, tailWord_548406, baseEnd_548406] using wordTrace_append hprefix tailTrace_548406
  have hstable : (prefixWord ++ tailWord_548406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548406).length < 2 ^ (prefixWord ++ tailWord_548406).sum := by decide
  have hdescent : baseEnd_548406 < baseStart_548406 := by decide
  rcases family_descends (prefixWord ++ tailWord_548406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548409 : List Nat := [1, 2, 1, 5, 1, 3, 1, 3, 1, 1, 4]
def baseStart_548409 : Nat := 118140960795 + 548409 * 2 ^ 59
def prefixEnd_548409 : Nat := 4983230072969 + 3 ^ 40 * 548409 * 2
def baseEnd_548409 : Nat := 281597412251650080965419

theorem tailTrace_548409 : CollatzResearch.WordTrace tailWord_548409 prefixEnd_548409 281597412251650080965419 := by
  unfold tailWord_548409
  simp only [CollatzResearch.WordTrace]
  refine ⟨20002119470215328645592281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13334746313476885763728187 20002119470215328645592281)
  ·
    refine ⟨15001589602661496484194211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20002119470215328645592281 15001589602661496484194211)
    ·
      refine ⟨22502384403992244726291317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15001589602661496484194211 22502384403992244726291317)
      ·
        refine ⟨2109598537874272943089811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22502384403992244726291317 2109598537874272943089811)
        ·
          refine ⟨3164397806811409414634717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2109598537874272943089811 3164397806811409414634717)
          ·
            refine ⟨1186649177554278530488019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3164397806811409414634717 1186649177554278530488019)
            ·
              refine ⟨1779973766331417795732029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1186649177554278530488019 1779973766331417795732029)
              ·
                refine ⟨667490162374281673399511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1779973766331417795732029 667490162374281673399511)
                ·
                  refine ⟨1001235243561422510099267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 667490162374281673399511 1001235243561422510099267)
                  ·
                    refine ⟨1501852865342133765148901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1001235243561422510099267 1501852865342133765148901)
                    ·
                      refine ⟨281597412251650080965419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1501852865342133765148901 281597412251650080965419)
                      ·
                        rfl

theorem cell23_548409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_548409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548409 prefixEnd_548409 := by exact prefixLift 548409
  have htrace : WordTrace (prefixWord ++ tailWord_548409) baseStart_548409 baseEnd_548409 := by
    simpa [prefixWord, tailWord_548409, baseEnd_548409] using wordTrace_append hprefix tailTrace_548409
  have hstable : (prefixWord ++ tailWord_548409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548409).length < 2 ^ (prefixWord ++ tailWord_548409).sum := by decide
  have hdescent : baseEnd_548409 < baseStart_548409 := by decide
  rcases family_descends (prefixWord ++ tailWord_548409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548415 : List Nat := [1, 1, 2, 2, 3, 4, 10]
def baseStart_548415 : Nat := 118140960795 + 548415 * 2 ^ 59
def prefixEnd_548415 : Nat := 4983230072969 + 3 ^ 40 * 548415 * 2
def baseEnd_548415 : Nat := 3476549297970087129511

theorem tailTrace_548415 : CollatzResearch.WordTrace tailWord_548415 prefixEnd_548415 3476549297970087129511 := by
  unfold tailWord_548415
  simp only [CollatzResearch.WordTrace]
  refine ⟨20002338308193591670310699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13334892205462394446873799 20002338308193591670310699)
  ·
    refine ⟨30003507462290387505466049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20002338308193591670310699 30003507462290387505466049)
    ·
      refine ⟨22502630596717790629099537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30003507462290387505466049 22502630596717790629099537)
      ·
        refine ⟨16876972947538342971824653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22502630596717790629099537 16876972947538342971824653)
        ·
          refine ⟨6328864855326878614434245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16876972947538342971824653 6328864855326878614434245)
          ·
            refine ⟨1186662160373789740206421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6328864855326878614434245 1186662160373789740206421)
            ·
              refine ⟨3476549297970087129511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1186662160373789740206421 3476549297970087129511)
              ·
                rfl

theorem cell23_548415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 10].length) (baseStart_548415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548415 prefixEnd_548415 := by exact prefixLift 548415
  have htrace : WordTrace (prefixWord ++ tailWord_548415) baseStart_548415 baseEnd_548415 := by
    simpa [prefixWord, tailWord_548415, baseEnd_548415] using wordTrace_append hprefix tailTrace_548415
  have hstable : (prefixWord ++ tailWord_548415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548415).length < 2 ^ (prefixWord ++ tailWord_548415).sum := by decide
  have hdescent : baseEnd_548415 < baseStart_548415 := by decide
  rcases family_descends (prefixWord ++ tailWord_548415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548426 : List Nat := [3, 1, 2, 1, 1, 3, 4, 1, 3, 2, 2]
def baseStart_548426 : Nat := 118140960795 + 548426 * 2 ^ 59
def prefixEnd_548426 : Nat := 4983230072969 + 3 ^ 40 * 548426 * 2
def baseEnd_548426 : Nat := 281606141422776514452841

theorem tailTrace_548426 : CollatzResearch.WordTrace tailWord_548426 prefixEnd_548426 281606141422776514452841 := by
  unfold tailWord_548426
  simp only [CollatzResearch.WordTrace]
  refine ⟨5000684877788435137240283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13335159674102493699307421 5000684877788435137240283)
  ·
    refine ⟨7501027316682652705860425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5000684877788435137240283 7501027316682652705860425)
    ·
      refine ⟨5625770487511989529395319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7501027316682652705860425 5625770487511989529395319)
      ·
        refine ⟨8438655731267984294092979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5625770487511989529395319 8438655731267984294092979)
        ·
          refine ⟨12657983596901976441139469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8438655731267984294092979 12657983596901976441139469)
          ·
            refine ⟨4746743848838241165427301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12657983596901976441139469 4746743848838241165427301)
            ·
              refine ⟨890014471657170218517619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4746743848838241165427301 890014471657170218517619)
              ·
                refine ⟨1335021707485755327776429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 890014471657170218517619 1335021707485755327776429)
                ·
                  refine ⟨500633140307158247916161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1335021707485755327776429 500633140307158247916161)
                  ·
                    refine ⟨375474855230368685937121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 500633140307158247916161 375474855230368685937121)
                    ·
                      refine ⟨281606141422776514452841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 375474855230368685937121 281606141422776514452841)
                      ·
                        rfl

theorem cell23_548426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 3, 2, 2].length) (baseStart_548426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548426 prefixEnd_548426 := by exact prefixLift 548426
  have htrace : WordTrace (prefixWord ++ tailWord_548426) baseStart_548426 baseEnd_548426 := by
    simpa [prefixWord, tailWord_548426, baseEnd_548426] using wordTrace_append hprefix tailTrace_548426
  have hstable : (prefixWord ++ tailWord_548426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548426).length < 2 ^ (prefixWord ++ tailWord_548426).sum := by decide
  have hdescent : baseEnd_548426 < baseStart_548426 := by decide
  rcases family_descends (prefixWord ++ tailWord_548426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548436 : List Nat := [2, 4, 1, 1, 1, 2, 5, 1, 2, 4]
def baseStart_548436 : Nat := 118140960795 + 548436 * 2 ^ 59
def prefixEnd_548436 : Nat := 4983230072969 + 3 ^ 40 * 548436 * 2
def baseEnd_548436 : Nat := 93870425409773825109265

theorem tailTrace_548436 : CollatzResearch.WordTrace tailWord_548436 prefixEnd_548436 93870425409773825109265 := by
  unfold tailWord_548436
  simp only [CollatzResearch.WordTrace]
  refine ⟨10001552120558756128412581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13335402827411674837883441 10001552120558756128412581)
  ·
    refine ⟨1875291022604766774077359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10001552120558756128412581 1875291022604766774077359)
    ·
      refine ⟨2812936533907150161116039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1875291022604766774077359 2812936533907150161116039)
      ·
        refine ⟨4219404800860725241674059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2812936533907150161116039 4219404800860725241674059)
        ·
          refine ⟨6329107201291087862511089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4219404800860725241674059 6329107201291087862511089)
          ·
            refine ⟨4746830400968315896883317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6329107201291087862511089 4746830400968315896883317)
            ·
              refine ⟨445015350090779615332811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4746830400968315896883317 445015350090779615332811)
              ·
                refine ⟨667523025136169422999217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 445015350090779615332811 667523025136169422999217)
                ·
                  refine ⟨500642268852127067249413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 667523025136169422999217 500642268852127067249413)
                  ·
                    refine ⟨93870425409773825109265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 500642268852127067249413 93870425409773825109265)
                    ·
                      rfl

theorem cell23_548436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_548436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548436 prefixEnd_548436 := by exact prefixLift 548436
  have htrace : WordTrace (prefixWord ++ tailWord_548436) baseStart_548436 baseEnd_548436 := by
    simpa [prefixWord, tailWord_548436, baseEnd_548436] using wordTrace_append hprefix tailTrace_548436
  have hstable : (prefixWord ++ tailWord_548436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548436).length < 2 ^ (prefixWord ++ tailWord_548436).sum := by decide
  have hdescent : baseEnd_548436 < baseStart_548436 := by decide
  rcases family_descends (prefixWord ++ tailWord_548436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548439 : List Nat := [1, 1, 3, 2, 2, 5, 1, 1, 1, 2, 4]
def baseStart_548439 : Nat := 118140960795 + 548439 * 2 ^ 59
def prefixEnd_548439 : Nat := 4983230072969 + 3 ^ 40 * 548439 * 2
def baseEnd_548439 : Nat := 281612816671284963590281

theorem tailTrace_548439 : CollatzResearch.WordTrace tailWord_548439 prefixEnd_548439 281612816671284963590281 := by
  unfold tailWord_548439
  simp only [CollatzResearch.WordTrace]
  refine ⟨20003213660106643769184371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13335475773404429179456247 20003213660106643769184371)
  ·
    refine ⟨30004820490159965653776557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20003213660106643769184371 30004820490159965653776557)
    ·
      refine ⟨11251807683809987120166209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30004820490159965653776557 11251807683809987120166209)
      ·
        refine ⟨8438855762857490340124657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11251807683809987120166209 8438855762857490340124657)
        ·
          refine ⟨6329141822143117755093493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8438855762857490340124657 6329141822143117755093493)
          ·
            refine ⟨593357045825917289540015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6329141822143117755093493 593357045825917289540015)
            ·
              refine ⟨890035568738875934310023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 593357045825917289540015 890035568738875934310023)
              ·
                refine ⟨1335053353108313901465035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 890035568738875934310023 1335053353108313901465035)
                ·
                  refine ⟨2002580029662470852197553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1335053353108313901465035 2002580029662470852197553)
                  ·
                    refine ⟨1501935022246853139148165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2002580029662470852197553 1501935022246853139148165)
                    ·
                      refine ⟨281612816671284963590281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1501935022246853139148165 281612816671284963590281)
                      ·
                        rfl

theorem cell23_548439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_548439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548439 prefixEnd_548439 := by exact prefixLift 548439
  have htrace : WordTrace (prefixWord ++ tailWord_548439) baseStart_548439 baseEnd_548439 := by
    simpa [prefixWord, tailWord_548439, baseEnd_548439] using wordTrace_append hprefix tailTrace_548439
  have hstable : (prefixWord ++ tailWord_548439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548439).length < 2 ^ (prefixWord ++ tailWord_548439).sum := by decide
  have hdescent : baseEnd_548439 < baseStart_548439 := by decide
  rcases family_descends (prefixWord ++ tailWord_548439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548465 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 1, 2, 8]
def baseStart_548465 : Nat := 118140960795 + 548465 * 2 ^ 59
def prefixEnd_548465 : Nat := 4983230072969 + 3 ^ 40 * 548465 * 2
def baseEnd_548465 : Nat := 281626167168301861865161

theorem tailTrace_548465 : CollatzResearch.WordTrace tailWord_548465 prefixEnd_548465 281626167168301861865161 := by
  unfold tailWord_548465
  simp only [CollatzResearch.WordTrace]
  refine ⟨20004161958012450209630849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13336107972008300139753899 20004161958012450209630849)
  ·
    refine ⟨15003121468509337657223137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20004161958012450209630849 15003121468509337657223137)
    ·
      refine ⟨11252341101382003242917353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15003121468509337657223137 11252341101382003242917353)
      ·
        refine ⟨8439255826036502432188015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11252341101382003242917353 8439255826036502432188015)
        ·
          refine ⟨12658883739054753648282023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8439255826036502432188015 12658883739054753648282023)
          ·
            refine ⟨18988325608582130472423035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12658883739054753648282023 18988325608582130472423035)
            ·
              refine ⟨28482488412873195708634553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18988325608582130472423035 28482488412873195708634553)
              ·
                refine ⟨21361866309654896781475915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28482488412873195708634553 21361866309654896781475915)
                ·
                  refine ⟨32042799464482345172213873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21361866309654896781475915 32042799464482345172213873)
                  ·
                    refine ⟨24032099598361758879160405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32042799464482345172213873 24032099598361758879160405)
                    ·
                      refine ⟨281626167168301861865161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 24032099598361758879160405 281626167168301861865161)
                      ·
                        rfl

theorem cell23_548465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_548465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548465 prefixEnd_548465 := by exact prefixLift 548465
  have htrace : WordTrace (prefixWord ++ tailWord_548465) baseStart_548465 baseEnd_548465 := by
    simpa [prefixWord, tailWord_548465, baseEnd_548465] using wordTrace_append hprefix tailTrace_548465
  have hstable : (prefixWord ++ tailWord_548465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548465).length < 2 ^ (prefixWord ++ tailWord_548465).sum := by decide
  have hdescent : baseEnd_548465 < baseStart_548465 := by decide
  rcases family_descends (prefixWord ++ tailWord_548465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548503 : List Nat := [1, 1, 3, 3, 2, 4, 1, 2, 1, 3, 2]
def baseStart_548503 : Nat := 118140960795 + 548503 * 2 ^ 59
def prefixEnd_548503 : Nat := 4983230072969 + 3 ^ 40 * 548503 * 2
def baseEnd_548503 : Nat := 281645679433172713189987

theorem tailTrace_548503 : CollatzResearch.WordTrace tailWord_548503 prefixEnd_548503 281645679433172713189987 := by
  unfold tailWord_548503
  simp only [CollatzResearch.WordTrace]
  refine ⟨20005547931874782699514163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13337031954583188466342775 20005547931874782699514163)
  ·
    refine ⟨30008321897812174049271245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20005547931874782699514163 30008321897812174049271245)
    ·
      refine ⟨11253120711679565268476717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30008321897812174049271245 11253120711679565268476717)
      ·
        refine ⟨4219920266879836975678769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11253120711679565268476717 4219920266879836975678769)
        ·
          refine ⟨3164940200159877731759077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4219920266879836975678769 3164940200159877731759077)
          ·
            refine ⟨593426287529977074704827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3164940200159877731759077 593426287529977074704827)
            ·
              refine ⟨890139431294965612057241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 593426287529977074704827 890139431294965612057241)
              ·
                refine ⟨667604573471224209042931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 890139431294965612057241 667604573471224209042931)
                ·
                  refine ⟨1001406860206836313564397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 667604573471224209042931 1001406860206836313564397)
                  ·
                    refine ⟨375527572577563617586649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1001406860206836313564397 375527572577563617586649)
                    ·
                      refine ⟨281645679433172713189987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 375527572577563617586649 281645679433172713189987)
                      ·
                        rfl

theorem cell23_548503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_548503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548503 prefixEnd_548503 := by exact prefixLift 548503
  have htrace : WordTrace (prefixWord ++ tailWord_548503) baseStart_548503 baseEnd_548503 := by
    simpa [prefixWord, tailWord_548503, baseEnd_548503] using wordTrace_append hprefix tailTrace_548503
  have hstable : (prefixWord ++ tailWord_548503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548503).length < 2 ^ (prefixWord ++ tailWord_548503).sum := by decide
  have hdescent : baseEnd_548503 < baseStart_548503 := by decide
  rcases family_descends (prefixWord ++ tailWord_548503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548516 : List Nat := [2, 3, 1, 2, 2, 3, 1, 2, 1, 4, 2]
def baseStart_548516 : Nat := 118140960795 + 548516 * 2 ^ 59
def prefixEnd_548516 : Nat := 4983230072969 + 3 ^ 40 * 548516 * 2
def baseEnd_548516 : Nat := 281652354681681162327427

theorem tailTrace_548516 : CollatzResearch.WordTrace tailWord_548516 prefixEnd_548516 281652354681681162327427 := by
  unfold tailWord_548516
  simp only [CollatzResearch.WordTrace]
  refine ⟨10003011040413842959868701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13337348053885123946491601 10003011040413842959868701)
  ·
    refine ⟨3751129140155191109950763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10003011040413842959868701 3751129140155191109950763)
    ·
      refine ⟨5626693710232786664926145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3751129140155191109950763 5626693710232786664926145)
      ·
        refine ⟨4220020282674589998694609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5626693710232786664926145 4220020282674589998694609)
        ·
          refine ⟨3165015212005942499020957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4220020282674589998694609 3165015212005942499020957)
          ·
            refine ⟨1186880704502228437132859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3165015212005942499020957 1186880704502228437132859)
            ·
              refine ⟨1780321056753342655699289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1186880704502228437132859 1780321056753342655699289)
              ·
                refine ⟨1335240792565006991774467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1780321056753342655699289 1335240792565006991774467)
                ·
                  refine ⟨2002861188847510487661701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1335240792565006991774467 2002861188847510487661701)
                  ·
                    refine ⟨375536472908908216436569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2002861188847510487661701 375536472908908216436569)
                    ·
                      refine ⟨281652354681681162327427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 375536472908908216436569 281652354681681162327427)
                      ·
                        rfl

theorem cell23_548516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_548516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548516 prefixEnd_548516 := by exact prefixLift 548516
  have htrace : WordTrace (prefixWord ++ tailWord_548516) baseStart_548516 baseEnd_548516 := by
    simpa [prefixWord, tailWord_548516, baseEnd_548516] using wordTrace_append hprefix tailTrace_548516
  have hstable : (prefixWord ++ tailWord_548516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548516).length < 2 ^ (prefixWord ++ tailWord_548516).sum := by decide
  have hdescent : baseEnd_548516 < baseStart_548516 := by decide
  rcases family_descends (prefixWord ++ tailWord_548516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548550 : List Nat := [6, 1, 2, 1, 1, 1, 1, 3, 1, 4, 2]
def baseStart_548550 : Nat := 118140960795 + 548550 * 2 ^ 59
def prefixEnd_548550 : Nat := 4983230072969 + 3 ^ 40 * 548550 * 2
def baseEnd_548550 : Nat := 281669813023934029302271

theorem tailTrace_548550 : CollatzResearch.WordTrace tailWord_548550 prefixEnd_548550 281669813023934029302271 := by
  unfold tailWord_548550
  simp only [CollatzResearch.WordTrace]
  refine ⟨625226942584515928952347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13338174775136339817650069 625226942584515928952347)
  ·
    refine ⟨937840413876773893428521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 625226942584515928952347 937840413876773893428521)
    ·
      refine ⟨703380310407580420071391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 937840413876773893428521 703380310407580420071391)
      ·
        refine ⟨1055070465611370630107087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 703380310407580420071391 1055070465611370630107087)
        ·
          refine ⟨1582605698417055945160631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1055070465611370630107087 1582605698417055945160631)
          ·
            refine ⟨2373908547625583917740947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1582605698417055945160631 2373908547625583917740947)
            ·
              refine ⟨3560862821438375876611421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2373908547625583917740947 3560862821438375876611421)
              ·
                refine ⟨1335323558039390953729283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3560862821438375876611421 1335323558039390953729283)
                ·
                  refine ⟨2002985337059086430593925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1335323558039390953729283 2002985337059086430593925)
                  ·
                    refine ⟨375559750698578705736361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2002985337059086430593925 375559750698578705736361)
                    ·
                      refine ⟨281669813023934029302271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 375559750698578705736361 281669813023934029302271)
                      ·
                        rfl

theorem cell23_548550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_548550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548550 prefixEnd_548550 := by exact prefixLift 548550
  have htrace : WordTrace (prefixWord ++ tailWord_548550) baseStart_548550 baseEnd_548550 := by
    simpa [prefixWord, tailWord_548550, baseEnd_548550] using wordTrace_append hprefix tailTrace_548550
  have hstable : (prefixWord ++ tailWord_548550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548550).length < 2 ^ (prefixWord ++ tailWord_548550).sum := by decide
  have hdescent : baseEnd_548550 < baseStart_548550 := by decide
  rcases family_descends (prefixWord ++ tailWord_548550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548552 : List Nat := [2, 1, 3, 1, 2, 2, 2, 2, 1, 7]
def baseStart_548552 : Nat := 118140960795 + 548552 * 2 ^ 59
def prefixEnd_548552 : Nat := 4983230072969 + 3 ^ 40 * 548552 * 2
def baseEnd_548552 : Nat := 93890279995081007159087

theorem tailTrace_548552 : CollatzResearch.WordTrace tailWord_548552 prefixEnd_548552 93890279995081007159087 := by
  unfold tailWord_548552
  simp only [CollatzResearch.WordTrace]
  refine ⟨10003667554348632034023955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13338223405798176045365273 10003667554348632034023955)
  ·
    refine ⟨15005501331522948051035933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10003667554348632034023955 15005501331522948051035933)
    ·
      refine ⟨5627062999321105519138475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15005501331522948051035933 5627062999321105519138475)
      ·
        refine ⟨8440594498981658278707713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5627062999321105519138475 8440594498981658278707713)
        ·
          refine ⟨6330445874236243709030785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8440594498981658278707713 6330445874236243709030785)
          ·
            refine ⟨4747834405677182781773089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6330445874236243709030785 4747834405677182781773089)
            ·
              refine ⟨3560875804257887086329817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4747834405677182781773089 3560875804257887086329817)
              ·
                refine ⟨2670656853193415314747363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3560875804257887086329817 2670656853193415314747363)
                ·
                  refine ⟨4005985279790122972121045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2670656853193415314747363 4005985279790122972121045)
                  ·
                    refine ⟨93890279995081007159087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4005985279790122972121045 93890279995081007159087)
                    ·
                      rfl

theorem cell23_548552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_548552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548552 prefixEnd_548552 := by exact prefixLift 548552
  have htrace : WordTrace (prefixWord ++ tailWord_548552) baseStart_548552 baseEnd_548552 := by
    simpa [prefixWord, tailWord_548552, baseEnd_548552] using wordTrace_append hprefix tailTrace_548552
  have hstable : (prefixWord ++ tailWord_548552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548552).length < 2 ^ (prefixWord ++ tailWord_548552).sum := by decide
  have hdescent : baseEnd_548552 < baseStart_548552 := by decide
  rcases family_descends (prefixWord ++ tailWord_548552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548569 : List Nat := [1, 2, 1, 2, 3, 3, 3, 1, 2, 5]
def baseStart_548569 : Nat := 118140960795 + 548569 * 2 ^ 59
def prefixEnd_548569 : Nat := 4983230072969 + 3 ^ 40 * 548569 * 2
def baseEnd_548569 : Nat := 93893189718789818321561

theorem tailTrace_548569 : CollatzResearch.WordTrace tailWord_548569 prefixEnd_548569 93893189718789818321561 := by
  unfold tailWord_548569
  simp only [CollatzResearch.WordTrace]
  refine ⟨20007955149635675971416761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13338636766423783980944507 20007955149635675971416761)
  ·
    refine ⟨15005966362226756978562571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20007955149635675971416761 15005966362226756978562571)
    ·
      refine ⟨22508949543340135467843857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15005966362226756978562571 22508949543340135467843857)
      ·
        refine ⟨16881712157505101600882893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22508949543340135467843857 16881712157505101600882893)
        ·
          refine ⟨6330642059064413100331085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16881712157505101600882893 6330642059064413100331085)
          ·
            refine ⟨2373990772149154912624157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6330642059064413100331085 2373990772149154912624157)
            ·
              refine ⟨890246539555933092234059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2373990772149154912624157 890246539555933092234059)
              ·
                refine ⟨1335369809333899638351089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 890246539555933092234059 1335369809333899638351089)
                ·
                  refine ⟨1001527357000424728763317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1335369809333899638351089 1001527357000424728763317)
                  ·
                    refine ⟨93893189718789818321561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1001527357000424728763317 93893189718789818321561)
                    ·
                      rfl

theorem cell23_548569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 5].length) (baseStart_548569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548569 prefixEnd_548569 := by exact prefixLift 548569
  have htrace : WordTrace (prefixWord ++ tailWord_548569) baseStart_548569 baseEnd_548569 := by
    simpa [prefixWord, tailWord_548569, baseEnd_548569] using wordTrace_append hprefix tailTrace_548569
  have hstable : (prefixWord ++ tailWord_548569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548569).length < 2 ^ (prefixWord ++ tailWord_548569).sum := by decide
  have hdescent : baseEnd_548569 < baseStart_548569 := by decide
  rcases family_descends (prefixWord ++ tailWord_548569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548599 : List Nat := [1, 1, 3, 1, 1, 1, 5, 3, 3, 4]
def baseStart_548599 : Nat := 118140960795 + 548599 * 2 ^ 59
def prefixEnd_548599 : Nat := 4983230072969 + 3 ^ 40 * 548599 * 2
def baseEnd_548599 : Nat := 93898324525334779196515

theorem tailTrace_548599 : CollatzResearch.WordTrace tailWord_548599 prefixEnd_548599 93898324525334779196515 := by
  unfold tailWord_548599
  simp only [CollatzResearch.WordTrace]
  refine ⟨20009049339526991095008851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13339366226351327396672567 20009049339526991095008851)
  ·
    refine ⟨30013574009290486642513277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20009049339526991095008851 30013574009290486642513277)
    ·
      refine ⟨11255090253483932490942479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30013574009290486642513277 11255090253483932490942479)
      ·
        refine ⟨16882635380225898736413719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11255090253483932490942479 16882635380225898736413719)
        ·
          refine ⟨25323953070338848104620579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16882635380225898736413719 25323953070338848104620579)
          ·
            refine ⟨37985929605508272156930869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25323953070338848104620579 37985929605508272156930869)
            ·
              refine ⟨3561180900516400514712269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37985929605508272156930869 3561180900516400514712269)
              ·
                refine ⟨1335442837693650193017101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3561180900516400514712269 1335442837693650193017101)
                ·
                  refine ⟨500791064135118822381413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1335442837693650193017101 500791064135118822381413)
                  ·
                    refine ⟨93898324525334779196515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 500791064135118822381413 93898324525334779196515)
                    ·
                      rfl

theorem cell23_548599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 3, 4].length) (baseStart_548599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548599 prefixEnd_548599 := by exact prefixLift 548599
  have htrace : WordTrace (prefixWord ++ tailWord_548599) baseStart_548599 baseEnd_548599 := by
    simpa [prefixWord, tailWord_548599, baseEnd_548599] using wordTrace_append hprefix tailTrace_548599
  have hstable : (prefixWord ++ tailWord_548599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548599).length < 2 ^ (prefixWord ++ tailWord_548599).sum := by decide
  have hdescent : baseEnd_548599 < baseStart_548599 := by decide
  rcases family_descends (prefixWord ++ tailWord_548599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548602 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 4, 1, 6]
def baseStart_548602 : Nat := 118140960795 + 548602 * 2 ^ 59
def prefixEnd_548602 : Nat := 4983230072969 + 3 ^ 40 * 548602 * 2
def baseEnd_548602 : Nat := 281696514017967825852031

theorem tailTrace_548602 : CollatzResearch.WordTrace tailWord_548602 prefixEnd_548602 281696514017967825852031 := by
  unfold tailWord_548602
  simp only [CollatzResearch.WordTrace]
  refine ⟨5002289689629030651842015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13339439172344081738245373 5002289689629030651842015)
  ·
    refine ⟨7503434534443545977763023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5002289689629030651842015 7503434534443545977763023)
    ·
      refine ⟨11255151801665318966644535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7503434534443545977763023 11255151801665318966644535)
      ·
        refine ⟨16882727702497978449966803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11255151801665318966644535 16882727702497978449966803)
        ·
          refine ⟨25324091553746967674950205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16882727702497978449966803 25324091553746967674950205)
          ·
            refine ⟨9496534332655112878106327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25324091553746967674950205 9496534332655112878106327)
            ·
              refine ⟨14244801498982669317159491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9496534332655112878106327 14244801498982669317159491)
              ·
                refine ⟨21367202248474003975739237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14244801498982669317159491 21367202248474003975739237)
                ·
                  refine ⟨4006350421588875745451107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21367202248474003975739237 4006350421588875745451107)
                  ·
                    refine ⟨6009525632383313618176661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4006350421588875745451107 6009525632383313618176661)
                    ·
                      refine ⟨281696514017967825852031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6009525632383313618176661 281696514017967825852031)
                      ·
                        rfl

theorem cell23_548602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_548602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548602 prefixEnd_548602 := by exact prefixLift 548602
  have htrace : WordTrace (prefixWord ++ tailWord_548602) baseStart_548602 baseEnd_548602 := by
    simpa [prefixWord, tailWord_548602, baseEnd_548602] using wordTrace_append hprefix tailTrace_548602
  have hstable : (prefixWord ++ tailWord_548602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548602).length < 2 ^ (prefixWord ++ tailWord_548602).sum := by decide
  have hdescent : baseEnd_548602 < baseStart_548602 := by decide
  rcases family_descends (prefixWord ++ tailWord_548602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548609 : List Nat := [1, 2, 4, 1, 1, 1, 3, 2, 1, 4, 3]
def baseStart_548609 : Nat := 118140960795 + 548609 * 2 ^ 59
def prefixEnd_548609 : Nat := 4983230072969 + 3 ^ 40 * 548609 * 2
def baseEnd_548609 : Nat := 281700108382549298464499

theorem tailTrace_548609 : CollatzResearch.WordTrace tailWord_548609 prefixEnd_548609 281700108382549298464499 := by
  unfold tailWord_548609
  simp only [CollatzResearch.WordTrace]
  refine ⟨20009414069490762802872881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13339609379660508535248587 20009414069490762802872881)
  ·
    refine ⟨15007060552118072102154661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20009414069490762802872881 15007060552118072102154661)
    ·
      refine ⟨2813823853522138519153999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15007060552118072102154661 2813823853522138519153999)
      ·
        refine ⟨4220735780283207778730999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2813823853522138519153999 4220735780283207778730999)
        ·
          refine ⟨6331103670424811668096499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4220735780283207778730999 6331103670424811668096499)
          ·
            refine ⟨9496655505637217502144749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6331103670424811668096499 9496655505637217502144749)
            ·
              refine ⟨3561245814613956563304281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9496655505637217502144749 3561245814613956563304281)
              ·
                refine ⟨2670934360960467422478211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3561245814613956563304281 2670934360960467422478211)
                ·
                  refine ⟨4006401541440701133717317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2670934360960467422478211 4006401541440701133717317)
                  ·
                    refine ⟨751200289020131462571997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4006401541440701133717317 751200289020131462571997)
                    ·
                      refine ⟨281700108382549298464499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 751200289020131462571997 281700108382549298464499)
                      ·
                        rfl

theorem cell23_548609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_548609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548609 prefixEnd_548609 := by exact prefixLift 548609
  have htrace : WordTrace (prefixWord ++ tailWord_548609) baseStart_548609 baseEnd_548609 := by
    simpa [prefixWord, tailWord_548609, baseEnd_548609] using wordTrace_append hprefix tailTrace_548609
  have hstable : (prefixWord ++ tailWord_548609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548609).length < 2 ^ (prefixWord ++ tailWord_548609).sum := by decide
  have hdescent : baseEnd_548609 < baseStart_548609 := by decide
  rcases family_descends (prefixWord ++ tailWord_548609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548689 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 3, 6]
def baseStart_548689 : Nat := 118140960795 + 548689 * 2 ^ 59
def prefixEnd_548689 : Nat := 4983230072969 + 3 ^ 40 * 548689 * 2
def baseEnd_548689 : Nat := 93913728944969661821377

theorem tailTrace_548689 : CollatzResearch.WordTrace tailWord_548689 prefixEnd_548689 93913728944969661821377 := by
  unfold tailWord_548689
  simp only [CollatzResearch.WordTrace]
  refine ⟨20012331909200936465785121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13341554606133957643856747 20012331909200936465785121)
  ·
    refine ⟨15009248931900702349338841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20012331909200936465785121 15009248931900702349338841)
    ·
      refine ⟨11256936698925526762004131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15009248931900702349338841 11256936698925526762004131)
      ·
        refine ⟨16885405048388290143006197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11256936698925526762004131 16885405048388290143006197)
        ·
          refine ⟨1583006723286402200906831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16885405048388290143006197 1583006723286402200906831)
          ·
            refine ⟨2374510084929603301360247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1583006723286402200906831 2374510084929603301360247)
            ·
              refine ⟨3561765127394404952040371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2374510084929603301360247 3561765127394404952040371)
              ·
                refine ⟨5342647691091607428060557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3561765127394404952040371 5342647691091607428060557)
                ·
                  refine ⟨2003492884159352785522709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5342647691091607428060557 2003492884159352785522709)
                  ·
                    refine ⟨93913728944969661821377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2003492884159352785522709 93913728944969661821377)
                    ·
                      rfl

theorem cell23_548689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 6].length) (baseStart_548689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548689 prefixEnd_548689 := by exact prefixLift 548689
  have htrace : WordTrace (prefixWord ++ tailWord_548689) baseStart_548689 baseEnd_548689 := by
    simpa [prefixWord, tailWord_548689, baseEnd_548689] using wordTrace_append hprefix tailTrace_548689
  have hstable : (prefixWord ++ tailWord_548689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548689).length < 2 ^ (prefixWord ++ tailWord_548689).sum := by decide
  have hdescent : baseEnd_548689 < baseStart_548689 := by decide
  rcases family_descends (prefixWord ++ tailWord_548689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548693 : List Nat := [1, 3, 2, 2, 2, 3, 3, 1, 1, 5]
def baseStart_548693 : Nat := 118140960795 + 548693 * 2 ^ 59
def prefixEnd_548693 : Nat := 4983230072969 + 3 ^ 40 * 548693 * 2
def baseEnd_548693 : Nat := 93914413585842323271371

theorem tailTrace_548693 : CollatzResearch.WordTrace tailWord_548693 prefixEnd_548693 93914413585842323271371 := by
  unfold tailWord_548693
  simp only [CollatzResearch.WordTrace]
  refine ⟨20012477801186445148930733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13341651867457630099287155 20012477801186445148930733)
  ·
    refine ⟨7504679175444916930849025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20012477801186445148930733 7504679175444916930849025)
    ·
      refine ⟨5628509381583687698136769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7504679175444916930849025 5628509381583687698136769)
      ·
        refine ⟨4221382036187765773602577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5628509381583687698136769 4221382036187765773602577)
        ·
          refine ⟨3166036527140824330201933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4221382036187765773602577 3166036527140824330201933)
          ·
            refine ⟨1187263697677809123825725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3166036527140824330201933 1187263697677809123825725)
            ·
              refine ⟨445223886629178421434647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1187263697677809123825725 445223886629178421434647)
              ·
                refine ⟨667835829943767632151971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 445223886629178421434647 667835829943767632151971)
                ·
                  refine ⟨1001753744915651448227957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 667835829943767632151971 1001753744915651448227957)
                  ·
                    refine ⟨93914413585842323271371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1001753744915651448227957 93914413585842323271371)
                    ·
                      rfl

theorem cell23_548693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_548693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548693 prefixEnd_548693 := by exact prefixLift 548693
  have htrace : WordTrace (prefixWord ++ tailWord_548693) baseStart_548693 baseEnd_548693 := by
    simpa [prefixWord, tailWord_548693, baseEnd_548693] using wordTrace_append hprefix tailTrace_548693
  have hstable : (prefixWord ++ tailWord_548693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548693).length < 2 ^ (prefixWord ++ tailWord_548693).sum := by decide
  have hdescent : baseEnd_548693 < baseStart_548693 := by decide
  rcases family_descends (prefixWord ++ tailWord_548693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548709 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 5, 2, 4]
def baseStart_548709 : Nat := 118140960795 + 548709 * 2 ^ 59
def prefixEnd_548709 : Nat := 4983230072969 + 3 ^ 40 * 548709 * 2
def baseEnd_548709 : Nat := 281751456447998907214039

theorem tailTrace_548709 : CollatzResearch.WordTrace tailWord_548709 prefixEnd_548709 281751456447998907214039 := by
  unfold tailWord_548709
  simp only [CollatzResearch.WordTrace]
  refine ⟨20013061369128479881513181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13342040912752319921008787 20013061369128479881513181)
  ·
    refine ⟨7504898013423179955567443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20013061369128479881513181 7504898013423179955567443)
    ·
      refine ⟨11257347020134769933351165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7504898013423179955567443 11257347020134769933351165)
      ·
        refine ⟨4221505132550538725006687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11257347020134769933351165 4221505132550538725006687)
        ·
          refine ⟨6332257698825808087510031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4221505132550538725006687 6332257698825808087510031)
          ·
            refine ⟨9498386548238712131265047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6332257698825808087510031 9498386548238712131265047)
            ·
              refine ⟨14247579822358068196897571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9498386548238712131265047 14247579822358068196897571)
              ·
                refine ⟨21371369733537102295346357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14247579822358068196897571 21371369733537102295346357)
                ·
                  refine ⟨2003565912519103340188721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21371369733537102295346357 2003565912519103340188721)
                  ·
                    refine ⟨1502674434389327505141541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2003565912519103340188721 1502674434389327505141541)
                    ·
                      refine ⟨281751456447998907214039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1502674434389327505141541 281751456447998907214039)
                      ·
                        rfl

theorem cell23_548709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_548709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548709 prefixEnd_548709 := by exact prefixLift 548709
  have htrace : WordTrace (prefixWord ++ tailWord_548709) baseStart_548709 baseEnd_548709 := by
    simpa [prefixWord, tailWord_548709, baseEnd_548709] using wordTrace_append hprefix tailTrace_548709
  have hstable : (prefixWord ++ tailWord_548709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548709).length < 2 ^ (prefixWord ++ tailWord_548709).sum := by decide
  have hdescent : baseEnd_548709 < baseStart_548709 := by decide
  rcases family_descends (prefixWord ++ tailWord_548709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548716 : List Nat := [2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 3]
def baseStart_548716 : Nat := 118140960795 + 548716 * 2 ^ 59
def prefixEnd_548716 : Nat := 4983230072969 + 3 ^ 40 * 548716 * 2
def baseEnd_548716 : Nat := 281755050812580379826507

theorem tailTrace_548716 : CollatzResearch.WordTrace tailWord_548716 prefixEnd_548716 281755050812580379826507 := by
  unfold tailWord_548716
  simp only [CollatzResearch.WordTrace]
  refine ⟨10006658340051560038509001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13342211120068746718012001 10006658340051560038509001)
  ·
    refine ⟨7504993755038670028881751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10006658340051560038509001 7504993755038670028881751)
    ·
      refine ⟨11257490632558005043322627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7504993755038670028881751 11257490632558005043322627)
      ·
        refine ⟨16886235948837007564983941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11257490632558005043322627 16886235948837007564983941)
        ·
          refine ⟨3166169240406938918434489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16886235948837007564983941 3166169240406938918434489)
          ·
            refine ⟨2374626930305204188825867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3166169240406938918434489 2374626930305204188825867)
            ·
              refine ⟨3561940395457806283238801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2374626930305204188825867 3561940395457806283238801)
              ·
                refine ⟨2671455296593354712429101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3561940395457806283238801 2671455296593354712429101)
                ·
                  refine ⟨1001795736222508017160913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2671455296593354712429101 1001795736222508017160913)
                  ·
                    refine ⟨751346802166881012870685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1001795736222508017160913 751346802166881012870685)
                    ·
                      refine ⟨281755050812580379826507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 751346802166881012870685 281755050812580379826507)
                      ·
                        rfl

theorem cell23_548716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 3].length) (baseStart_548716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548716 prefixEnd_548716 := by exact prefixLift 548716
  have htrace : WordTrace (prefixWord ++ tailWord_548716) baseStart_548716 baseEnd_548716 := by
    simpa [prefixWord, tailWord_548716, baseEnd_548716] using wordTrace_append hprefix tailTrace_548716
  have hstable : (prefixWord ++ tailWord_548716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548716).length < 2 ^ (prefixWord ++ tailWord_548716).sum := by decide
  have hdescent : baseEnd_548716 < baseStart_548716 := by decide
  rcases family_descends (prefixWord ++ tailWord_548716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548820 : List Nat := [2, 4, 1, 2, 1, 1, 1, 3, 4, 2, 2]
def baseStart_548820 : Nat := 118140960795 + 548820 * 2 ^ 59
def prefixEnd_548820 : Nat := 4983230072969 + 3 ^ 40 * 548820 * 2
def baseEnd_548820 : Nat := 281808452800647972926029

theorem tailTrace_548820 : CollatzResearch.WordTrace tailWord_548820 prefixEnd_548820 281808452800647972926029 := by
  unfold tailWord_548820
  simp only [CollatzResearch.WordTrace]
  refine ⟨10008554935863172919401957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13344739914484230559202609 10008554935863172919401957)
  ·
    refine ⟨1876604050474344922387867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10008554935863172919401957 1876604050474344922387867)
    ·
      refine ⟨2814906075711517383581801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1876604050474344922387867 2814906075711517383581801)
      ·
        refine ⟨2111179556783638037686351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2814906075711517383581801 2111179556783638037686351)
        ·
          refine ⟨3166769335175457056529527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2111179556783638037686351 3166769335175457056529527)
          ·
            refine ⟨4750154002763185584794291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3166769335175457056529527 4750154002763185584794291)
            ·
              refine ⟨7125231004144778377191437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4750154002763185584794291 7125231004144778377191437)
              ·
                refine ⟨2671961626554291891446789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7125231004144778377191437 2671961626554291891446789)
                ·
                  refine ⟨500992804978929729646273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2671961626554291891446789 500992804978929729646273)
                  ·
                    refine ⟨375744603734197297234705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 500992804978929729646273 375744603734197297234705)
                    ·
                      refine ⟨281808452800647972926029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 375744603734197297234705 281808452800647972926029)
                      ·
                        rfl

theorem cell23_548820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_548820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548820 prefixEnd_548820 := by exact prefixLift 548820
  have htrace : WordTrace (prefixWord ++ tailWord_548820) baseStart_548820 baseEnd_548820 := by
    simpa [prefixWord, tailWord_548820, baseEnd_548820] using wordTrace_append hprefix tailTrace_548820
  have hstable : (prefixWord ++ tailWord_548820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548820).length < 2 ^ (prefixWord ++ tailWord_548820).sum := by decide
  have hdescent : baseEnd_548820 < baseStart_548820 := by decide
  rcases family_descends (prefixWord ++ tailWord_548820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548836 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 1, 5, 3]
def baseStart_548836 : Nat := 118140960795 + 548836 * 2 ^ 59
def prefixEnd_548836 : Nat := 4983230072969 + 3 ^ 40 * 548836 * 2
def baseEnd_548836 : Nat := 281816668491119910325955

theorem tailTrace_548836 : CollatzResearch.WordTrace tailWord_548836 prefixEnd_548836 281816668491119910325955 := by
  unfold tailWord_548836
  simp only [CollatzResearch.WordTrace]
  refine ⟨10008846719834190285693181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13345128959778920380924241 10008846719834190285693181)
  ·
    refine ⟨3753317519937821357134943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10008846719834190285693181 3753317519937821357134943)
    ·
      refine ⟨5629976279906732035702415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3753317519937821357134943 5629976279906732035702415)
      ·
        refine ⟨8444964419860098053553623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5629976279906732035702415 8444964419860098053553623)
        ·
          refine ⟨12667446629790147080330435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8444964419860098053553623 12667446629790147080330435)
          ·
            refine ⟨19001169944685220620495653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12667446629790147080330435 19001169944685220620495653)
            ·
              refine ⟨3562719364628478866342935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19001169944685220620495653 3562719364628478866342935)
              ·
                refine ⟨5344079046942718299514403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3562719364628478866342935 5344079046942718299514403)
                ·
                  refine ⟨8016118570414077449271605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5344079046942718299514403 8016118570414077449271605)
                  ·
                    refine ⟨751511115976319760869213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8016118570414077449271605 751511115976319760869213)
                    ·
                      refine ⟨281816668491119910325955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 751511115976319760869213 281816668491119910325955)
                      ·
                        rfl

theorem cell23_548836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_548836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548836 prefixEnd_548836 := by exact prefixLift 548836
  have htrace : WordTrace (prefixWord ++ tailWord_548836) baseStart_548836 baseEnd_548836 := by
    simpa [prefixWord, tailWord_548836, baseEnd_548836] using wordTrace_append hprefix tailTrace_548836
  have hstable : (prefixWord ++ tailWord_548836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548836).length < 2 ^ (prefixWord ++ tailWord_548836).sum := by decide
  have hdescent : baseEnd_548836 < baseStart_548836 := by decide
  rcases family_descends (prefixWord ++ tailWord_548836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548856 : List Nat := [2, 1, 2, 1, 1, 3, 3, 3, 2, 5]
def baseStart_548856 : Nat := 118140960795 + 548856 * 2 ^ 59
def prefixEnd_548856 : Nat := 4983230072969 + 3 ^ 40 * 548856 * 2
def baseEnd_548856 : Nat := 93942312701403277358621

theorem tailTrace_548856 : CollatzResearch.WordTrace tailWord_548856 prefixEnd_548856 93942312701403277358621 := by
  unfold tailWord_548856
  simp only [CollatzResearch.WordTrace]
  refine ⟨10009211449797961993557211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13345615266397282658076281 10009211449797961993557211)
  ·
    refine ⟨15013817174696942990335817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10009211449797961993557211 15013817174696942990335817)
    ·
      refine ⟨11260362881022707242751863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15013817174696942990335817 11260362881022707242751863)
      ·
        refine ⟨16890544321534060864127795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11260362881022707242751863 16890544321534060864127795)
        ·
          refine ⟨25335816482301091296191693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16890544321534060864127795 25335816482301091296191693)
          ·
            refine ⟨9500931180862909236071885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25335816482301091296191693 9500931180862909236071885)
            ·
              refine ⟨3562849192823590963526957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9500931180862909236071885 3562849192823590963526957)
              ·
                refine ⟨1336068447308846611322609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3562849192823590963526957 1336068447308846611322609)
                ·
                  refine ⟨1002051335481634958491957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1336068447308846611322609 1002051335481634958491957)
                  ·
                    refine ⟨93942312701403277358621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1002051335481634958491957 93942312701403277358621)
                    ·
                      rfl

theorem cell23_548856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 2, 5].length) (baseStart_548856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548856 prefixEnd_548856 := by exact prefixLift 548856
  have htrace : WordTrace (prefixWord ++ tailWord_548856) baseStart_548856 baseEnd_548856 := by
    simpa [prefixWord, tailWord_548856, baseEnd_548856] using wordTrace_append hprefix tailTrace_548856
  have hstable : (prefixWord ++ tailWord_548856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548856).length < 2 ^ (prefixWord ++ tailWord_548856).sum := by decide
  have hdescent : baseEnd_548856 < baseStart_548856 := by decide
  rcases family_descends (prefixWord ++ tailWord_548856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548910 : List Nat := [4, 1, 3, 1, 1, 2, 3, 1, 2, 1, 4]
def baseStart_548910 : Nat := 118140960795 + 548910 * 2 ^ 59
def prefixEnd_548910 : Nat := 4983230072969 + 3 ^ 40 * 548910 * 2
def baseEnd_548910 : Nat := 281854666059552620800615

theorem tailTrace_548910 : CollatzResearch.WordTrace tailWord_548910 prefixEnd_548910 281854666059552620800615 := by
  unfold tailWord_548910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2502549055175036401197523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13346928294266860806386789 2502549055175036401197523)
  ·
    refine ⟨3753823582762554601796285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2502549055175036401197523 3753823582762554601796285)
    ·
      refine ⟨1407683843535957975673607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3753823582762554601796285 1407683843535957975673607)
      ·
        refine ⟨2111525765303936963510411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1407683843535957975673607 2111525765303936963510411)
        ·
          refine ⟨3167288647955905445265617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2111525765303936963510411 3167288647955905445265617)
          ·
            refine ⟨2375466485966929083949213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3167288647955905445265617 2375466485966929083949213)
            ·
              refine ⟨890799932237598406480955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2375466485966929083949213 890799932237598406480955)
              ·
                refine ⟨1336199898356397609721433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 890799932237598406480955 1336199898356397609721433)
                ·
                  refine ⟨1002149923767298207291075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1336199898356397609721433 1002149923767298207291075)
                  ·
                    refine ⟨1503224885650947310936613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1002149923767298207291075 1503224885650947310936613)
                    ·
                      refine ⟨281854666059552620800615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1503224885650947310936613 281854666059552620800615)
                      ·
                        rfl

theorem cell23_548910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_548910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548910 prefixEnd_548910 := by exact prefixLift 548910
  have htrace : WordTrace (prefixWord ++ tailWord_548910) baseStart_548910 baseEnd_548910 := by
    simpa [prefixWord, tailWord_548910, baseEnd_548910] using wordTrace_append hprefix tailTrace_548910
  have hstable : (prefixWord ++ tailWord_548910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548910).length < 2 ^ (prefixWord ++ tailWord_548910).sum := by decide
  have hdescent : baseEnd_548910 < baseStart_548910 := by decide
  rcases family_descends (prefixWord ++ tailWord_548910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548913 : List Nat := [1, 2, 2, 3, 1, 4, 1, 1, 1, 4, 3]
def baseStart_548913 : Nat := 118140960795 + 548913 * 2 ^ 59
def prefixEnd_548913 : Nat := 4983230072969 + 3 ^ 40 * 548913 * 2
def baseEnd_548913 : Nat := 281856206501516109063101

theorem tailTrace_548913 : CollatzResearch.WordTrace tailWord_548913 prefixEnd_548913 281856206501516109063101 := by
  unfold tailWord_548913
  simp only [CollatzResearch.WordTrace]
  refine ⟨20020501860389422721939393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13347001240259615147959595 20020501860389422721939393)
  ·
    refine ⟨15015376395292067041454545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20020501860389422721939393 15015376395292067041454545)
    ·
      refine ⟨11261532296469050281090909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15015376395292067041454545 11261532296469050281090909)
      ·
        refine ⟨4223074611175893855409091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11261532296469050281090909 4223074611175893855409091)
        ·
          refine ⟨6334611916763840783113637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4223074611175893855409091 6334611916763840783113637)
          ·
            refine ⟨1187739734393220146833807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6334611916763840783113637 1187739734393220146833807)
            ·
              refine ⟨1781609601589830220250711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1187739734393220146833807 1781609601589830220250711)
              ·
                refine ⟨2672414402384745330376067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1781609601589830220250711 2672414402384745330376067)
                ·
                  refine ⟨4008621603577117995564101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2672414402384745330376067 4008621603577117995564101)
                  ·
                    refine ⟨751616550670709624168269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4008621603577117995564101 751616550670709624168269)
                    ·
                      refine ⟨281856206501516109063101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 751616550670709624168269 281856206501516109063101)
                      ·
                        rfl

theorem cell23_548913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_548913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548913 prefixEnd_548913 := by exact prefixLift 548913
  have htrace : WordTrace (prefixWord ++ tailWord_548913) baseStart_548913 baseEnd_548913 := by
    simpa [prefixWord, tailWord_548913, baseEnd_548913] using wordTrace_append hprefix tailTrace_548913
  have hstable : (prefixWord ++ tailWord_548913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548913).length < 2 ^ (prefixWord ++ tailWord_548913).sum := by decide
  have hdescent : baseEnd_548913 < baseStart_548913 := by decide
  rcases family_descends (prefixWord ++ tailWord_548913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548943 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 7, 1, 3]
def baseStart_548943 : Nat := 118140960795 + 548943 * 2 ^ 59
def prefixEnd_548943 : Nat := 4983230072969 + 3 ^ 40 * 548943 * 2
def baseEnd_548943 : Nat := 281871610921150991687963

theorem tailTrace_548943 : CollatzResearch.WordTrace tailWord_548943 prefixEnd_548943 281871610921150991687963 := by
  unfold tailWord_548943
  simp only [CollatzResearch.WordTrace]
  refine ⟨20021596050280737845531483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13347730700187158563687655 20021596050280737845531483)
  ·
    refine ⟨30032394075421106768297225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20021596050280737845531483 30032394075421106768297225)
    ·
      refine ⟨22524295556565830076222919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30032394075421106768297225 22524295556565830076222919)
      ·
        refine ⟨33786443334848745114334379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22524295556565830076222919 33786443334848745114334379)
        ·
          refine ⟨50679665002273117671501569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33786443334848745114334379 50679665002273117671501569)
          ·
            refine ⟨38009748751704838253626177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50679665002273117671501569 38009748751704838253626177)
            ·
              refine ⟨28507311563778628690219633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38009748751704838253626177 28507311563778628690219633)
              ·
                refine ⟨21380483672833971517664725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28507311563778628690219633 21380483672833971517664725)
                ·
                  refine ⟨501105086082046207445267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 21380483672833971517664725 501105086082046207445267)
                  ·
                    refine ⟨751657629123069311167901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 501105086082046207445267 751657629123069311167901)
                    ·
                      refine ⟨281871610921150991687963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 751657629123069311167901 281871610921150991687963)
                      ·
                        rfl

theorem cell23_548943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 7, 1, 3].length) (baseStart_548943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548943 prefixEnd_548943 := by exact prefixLift 548943
  have htrace : WordTrace (prefixWord ++ tailWord_548943) baseStart_548943 baseEnd_548943 := by
    simpa [prefixWord, tailWord_548943, baseEnd_548943] using wordTrace_append hprefix tailTrace_548943
  have hstable : (prefixWord ++ tailWord_548943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548943).length < 2 ^ (prefixWord ++ tailWord_548943).sum := by decide
  have hdescent : baseEnd_548943 < baseStart_548943 := by decide
  rcases family_descends (prefixWord ++ tailWord_548943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548953 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 3, 5, 2]
def baseStart_548953 : Nat := 118140960795 + 548953 * 2 ^ 59
def prefixEnd_548953 : Nat := 4983230072969 + 3 ^ 40 * 548953 * 2
def baseEnd_548953 : Nat := 281876745727695952562917

theorem tailTrace_548953 : CollatzResearch.WordTrace tailWord_548953 prefixEnd_548953 281876745727695952562917 := by
  unfold tailWord_548953
  simp only [CollatzResearch.WordTrace]
  refine ⟨20021960780244509553395513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13347973853496339702263675 20021960780244509553395513)
  ·
    refine ⟨15016470585183382165046635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20021960780244509553395513 15016470585183382165046635)
    ·
      refine ⟨22524705877775073247569953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15016470585183382165046635 22524705877775073247569953)
      ·
        refine ⟨16893529408331304935677465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22524705877775073247569953 16893529408331304935677465)
        ·
          refine ⟨12670147056248478701758099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16893529408331304935677465 12670147056248478701758099)
          ·
            refine ⟨19005220584372718052637149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12670147056248478701758099 19005220584372718052637149)
            ·
              refine ⟨7126957719139769269738931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19005220584372718052637149 7126957719139769269738931)
              ·
                refine ⟨10690436578709653904608397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7126957719139769269738931 10690436578709653904608397)
                ·
                  refine ⟨4008913717016120214228149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10690436578709653904608397 4008913717016120214228149)
                  ·
                    refine ⟨375835660970261270083889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4008913717016120214228149 375835660970261270083889)
                    ·
                      refine ⟨281876745727695952562917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 375835660970261270083889 281876745727695952562917)
                      ·
                        rfl

theorem cell23_548953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 5, 2].length) (baseStart_548953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548953 prefixEnd_548953 := by exact prefixLift 548953
  have htrace : WordTrace (prefixWord ++ tailWord_548953) baseStart_548953 baseEnd_548953 := by
    simpa [prefixWord, tailWord_548953, baseEnd_548953] using wordTrace_append hprefix tailTrace_548953
  have hstable : (prefixWord ++ tailWord_548953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548953).length < 2 ^ (prefixWord ++ tailWord_548953).sum := by decide
  have hdescent : baseEnd_548953 < baseStart_548953 := by decide
  rcases family_descends (prefixWord ++ tailWord_548953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548960 : List Nat := [2, 1, 1, 3, 2, 3, 2, 2, 3, 1, 3]
def baseStart_548960 : Nat := 118140960795 + 548960 * 2 ^ 59
def prefixEnd_548960 : Nat := 4983230072969 + 3 ^ 40 * 548960 * 2
def baseEnd_548960 : Nat := 281880340092277425175385

theorem tailTrace_548960 : CollatzResearch.WordTrace tailWord_548960 prefixEnd_548960 281880340092277425175385 := by
  unfold tailWord_548960
  simp only [CollatzResearch.WordTrace]
  refine ⟨10011108045609574874450167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13348144060812766499266889 10011108045609574874450167)
  ·
    refine ⟨15016662068414362311675251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10011108045609574874450167 15016662068414362311675251)
    ·
      refine ⟨22524993102621543467512877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15016662068414362311675251 22524993102621543467512877)
      ·
        refine ⟨8446872413483078800317329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22524993102621543467512877 8446872413483078800317329)
        ·
          refine ⟨6335154310112309100237997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8446872413483078800317329 6335154310112309100237997)
          ·
            refine ⟨2375682866292115912589249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6335154310112309100237997 2375682866292115912589249)
            ·
              refine ⟨1781762149719086934441937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2375682866292115912589249 1781762149719086934441937)
              ·
                refine ⟨1336321612289315200831453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1781762149719086934441937 1336321612289315200831453)
                ·
                  refine ⟨501120604608493200311795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1336321612289315200831453 501120604608493200311795)
                  ·
                    refine ⟨751680906912739800467693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 501120604608493200311795 751680906912739800467693)
                    ·
                      refine ⟨281880340092277425175385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 751680906912739800467693 281880340092277425175385)
                      ·
                        rfl

theorem cell23_548960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_548960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548960 prefixEnd_548960 := by exact prefixLift 548960
  have htrace : WordTrace (prefixWord ++ tailWord_548960) baseStart_548960 baseEnd_548960 := by
    simpa [prefixWord, tailWord_548960, baseEnd_548960] using wordTrace_append hprefix tailTrace_548960
  have hstable : (prefixWord ++ tailWord_548960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548960).length < 2 ^ (prefixWord ++ tailWord_548960).sum := by decide
  have hdescent : baseEnd_548960 < baseStart_548960 := by decide
  rcases family_descends (prefixWord ++ tailWord_548960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548963 : List Nat := [1, 1, 1, 5, 1, 1, 3, 4, 1, 5]
def baseStart_548963 : Nat := 118140960795 + 548963 * 2 ^ 59
def prefixEnd_548963 : Nat := 4983230072969 + 3 ^ 40 * 548963 * 2
def baseEnd_548963 : Nat := 93960626844746971145957

theorem tailTrace_548963 : CollatzResearch.WordTrace tailWord_548963 prefixEnd_548963 93960626844746971145957 := by
  unfold tailWord_548963
  simp only [CollatzResearch.WordTrace]
  refine ⟨20022325510208281261259543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13348217006805520840839695 20022325510208281261259543)
  ·
    refine ⟨30033488265312421891889315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20022325510208281261259543 30033488265312421891889315)
    ·
      refine ⟨45050232397968632837833973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30033488265312421891889315 45050232397968632837833973)
      ·
        refine ⟨4223459287309559328546935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45050232397968632837833973 4223459287309559328546935)
        ·
          refine ⟨6335188930964338992820403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4223459287309559328546935 6335188930964338992820403)
          ·
            refine ⟨9502783396446508489230605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6335188930964338992820403 9502783396446508489230605)
            ·
              refine ⟨3563543773667440683461477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9502783396446508489230605 3563543773667440683461477)
              ·
                refine ⟨668164457562645128149027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3563543773667440683461477 668164457562645128149027)
                ·
                  refine ⟨1002246686343967692223541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 668164457562645128149027 1002246686343967692223541)
                  ·
                    refine ⟨93960626844746971145957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1002246686343967692223541 93960626844746971145957)
                    ·
                      rfl

theorem cell23_548963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 5].length) (baseStart_548963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_548963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_548963 prefixEnd_548963 := by exact prefixLift 548963
  have htrace : WordTrace (prefixWord ++ tailWord_548963) baseStart_548963 baseEnd_548963 := by
    simpa [prefixWord, tailWord_548963, baseEnd_548963] using wordTrace_append hprefix tailTrace_548963
  have hstable : (prefixWord ++ tailWord_548963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548963).length < 2 ^ (prefixWord ++ tailWord_548963).sum := by decide
  have hdescent : baseEnd_548963 < baseStart_548963 := by decide
  rcases family_descends (prefixWord ++ tailWord_548963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549013 : List Nat := [1, 3, 2, 1, 1, 1, 4, 3, 1, 2, 4]
def baseStart_549013 : Nat := 118140960795 + 549013 * 2 ^ 59
def prefixEnd_549013 : Nat := 4983230072969 + 3 ^ 40 * 549013 * 2
def baseEnd_549013 : Nat := 281907554566965717812641

theorem tailTrace_549013 : CollatzResearch.WordTrace tailWord_549013 prefixEnd_549013 281907554566965717812641 := by
  unfold tailWord_549013
  simp only [CollatzResearch.WordTrace]
  refine ⟨20024149160027139800579693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13349432773351426533719795 20024149160027139800579693)
  ·
    refine ⟨7509055935010177425217385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20024149160027139800579693 7509055935010177425217385)
    ·
      refine ⟨5631791951257633068913039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7509055935010177425217385 5631791951257633068913039)
      ·
        refine ⟨8447687926886449603369559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5631791951257633068913039 8447687926886449603369559)
        ·
          refine ⟨12671531890329674405054339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8447687926886449603369559 12671531890329674405054339)
          ·
            refine ⟨19007297835494511607581509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12671531890329674405054339 19007297835494511607581509)
            ·
              refine ⟨3563868344155220926421533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19007297835494511607581509 3563868344155220926421533)
              ·
                refine ⟨1336450629058207847408075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3563868344155220926421533 1336450629058207847408075)
                ·
                  refine ⟨2004675943587311771112113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1336450629058207847408075 2004675943587311771112113)
                  ·
                    refine ⟨1503506957690483828334085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2004675943587311771112113 1503506957690483828334085)
                    ·
                      refine ⟨281907554566965717812641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1503506957690483828334085 281907554566965717812641)
                      ·
                        rfl

theorem cell23_549013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_549013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549013 prefixEnd_549013 := by exact prefixLift 549013
  have htrace : WordTrace (prefixWord ++ tailWord_549013) baseStart_549013 baseEnd_549013 := by
    simpa [prefixWord, tailWord_549013, baseEnd_549013] using wordTrace_append hprefix tailTrace_549013
  have hstable : (prefixWord ++ tailWord_549013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549013).length < 2 ^ (prefixWord ++ tailWord_549013).sum := by decide
  have hdescent : baseEnd_549013 < baseStart_549013 := by decide
  rcases family_descends (prefixWord ++ tailWord_549013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549020 : List Nat := [2, 2, 3, 2, 1, 1, 3, 1, 3, 2, 3]
def baseStart_549020 : Nat := 118140960795 + 549020 * 2 ^ 59
def prefixEnd_549020 : Nat := 4983230072969 + 3 ^ 40 * 549020 * 2
def baseEnd_549020 : Nat := 281911148931547190425109

theorem tailTrace_549020 : CollatzResearch.WordTrace tailWord_549020 prefixEnd_549020 281911148931547190425109 := by
  unfold tailWord_549020
  simp only [CollatzResearch.WordTrace]
  refine ⟨10012202235500889998042257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13349602980667853330723009 10012202235500889998042257)
  ·
    refine ⟨7509151676625667498531693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10012202235500889998042257 7509151676625667498531693)
    ·
      refine ⟨2815931878734625311949385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7509151676625667498531693 2815931878734625311949385)
      ·
        refine ⟨2111948909050968983962039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2815931878734625311949385 2111948909050968983962039)
        ·
          refine ⟨3167923363576453475943059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2111948909050968983962039 3167923363576453475943059)
          ·
            refine ⟨4751885045364680213914589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3167923363576453475943059 4751885045364680213914589)
            ·
              refine ⟨1781956892011755080217971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4751885045364680213914589 1781956892011755080217971)
              ·
                refine ⟨2672935338017632620326957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1781956892011755080217971 2672935338017632620326957)
                ·
                  refine ⟨1002350751756612232622609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2672935338017632620326957 1002350751756612232622609)
                  ·
                    refine ⟨751763063817459174466957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1002350751756612232622609 751763063817459174466957)
                    ·
                      refine ⟨281911148931547190425109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 751763063817459174466957 281911148931547190425109)
                      ·
                        rfl

theorem cell23_549020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_549020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549020 prefixEnd_549020 := by exact prefixLift 549020
  have htrace : WordTrace (prefixWord ++ tailWord_549020) baseStart_549020 baseEnd_549020 := by
    simpa [prefixWord, tailWord_549020, baseEnd_549020] using wordTrace_append hprefix tailTrace_549020
  have hstable : (prefixWord ++ tailWord_549020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549020).length < 2 ^ (prefixWord ++ tailWord_549020).sum := by decide
  have hdescent : baseEnd_549020 < baseStart_549020 := by decide
  rcases family_descends (prefixWord ++ tailWord_549020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549023 : List Nat := [1, 1, 2, 6, 1, 1, 2, 9]
def baseStart_549023 : Nat := 118140960795 + 549023 * 2 ^ 59
def prefixEnd_549023 : Nat := 4983230072969 + 3 ^ 40 * 549023 * 2
def baseEnd_549023 : Nat := 10441210717537432543985

theorem tailTrace_549023 : CollatzResearch.WordTrace tailWord_549023 prefixEnd_549023 10441210717537432543985 := by
  unfold tailWord_549023
  simp only [CollatzResearch.WordTrace]
  refine ⟨20024513889990911508443723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13349675926660607672295815 20024513889990911508443723)
  ·
    refine ⟨30036770834986367262665585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20024513889990911508443723 30036770834986367262665585)
    ·
      refine ⟨22527578126239775446999189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30036770834986367262665585 22527578126239775446999189)
      ·
        refine ⟨1055980224667489474078087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22527578126239775446999189 1055980224667489474078087)
        ·
          refine ⟨1583970337001234211117131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1055980224667489474078087 1583970337001234211117131)
          ·
            refine ⟨2375955505501851316675697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1583970337001234211117131 2375955505501851316675697)
            ·
              refine ⟨1781966629126388487506773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2375955505501851316675697 1781966629126388487506773)
              ·
                refine ⟨10441210717537432543985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1781966629126388487506773 10441210717537432543985)
                ·
                  rfl

theorem cell23_549023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 9].length) (baseStart_549023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549023 prefixEnd_549023 := by exact prefixLift 549023
  have htrace : WordTrace (prefixWord ++ tailWord_549023) baseStart_549023 baseEnd_549023 := by
    simpa [prefixWord, tailWord_549023, baseEnd_549023] using wordTrace_append hprefix tailTrace_549023
  have hstable : (prefixWord ++ tailWord_549023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549023).length < 2 ^ (prefixWord ++ tailWord_549023).sum := by decide
  have hdescent : baseEnd_549023 < baseStart_549023 := by decide
  rcases family_descends (prefixWord ++ tailWord_549023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549037 : List Nat := [1, 5, 2, 1, 2, 3, 1, 1, 1, 1, 5]
def baseStart_549037 : Nat := 118140960795 + 549037 * 2 ^ 59
def prefixEnd_549037 : Nat := 4983230072969 + 3 ^ 40 * 549037 * 2
def baseEnd_549037 : Nat := 281919878102673623912531

theorem tailTrace_549037 : CollatzResearch.WordTrace tailWord_549037 prefixEnd_549037 281919878102673623912531 := by
  unfold tailWord_549037
  simp only [CollatzResearch.WordTrace]
  refine ⟨20025024511940191899453365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13350016341293461266302243 20025024511940191899453365)
  ·
    refine ⟨1877346047994392990573753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20025024511940191899453365 1877346047994392990573753)
    ·
      refine ⟨1408009535995794742930315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1877346047994392990573753 1408009535995794742930315)
      ·
        refine ⟨2112014303993692114395473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1408009535995794742930315 2112014303993692114395473)
        ·
          refine ⟨1584010727995269085796605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2112014303993692114395473 1584010727995269085796605)
          ·
            refine ⟨594004022998225907173727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1584010727995269085796605 594004022998225907173727)
            ·
              refine ⟨891006034497338860760591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 594004022998225907173727 891006034497338860760591)
              ·
                refine ⟨1336509051746008291140887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 891006034497338860760591 1336509051746008291140887)
                ·
                  refine ⟨2004763577619012436711331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1336509051746008291140887 2004763577619012436711331)
                  ·
                    refine ⟨3007145366428518655066997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2004763577619012436711331 3007145366428518655066997)
                    ·
                      refine ⟨281919878102673623912531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3007145366428518655066997 281919878102673623912531)
                      ·
                        rfl

theorem cell23_549037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_549037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549037 prefixEnd_549037 := by exact prefixLift 549037
  have htrace : WordTrace (prefixWord ++ tailWord_549037) baseStart_549037 baseEnd_549037 := by
    simpa [prefixWord, tailWord_549037, baseEnd_549037] using wordTrace_append hprefix tailTrace_549037
  have hstable : (prefixWord ++ tailWord_549037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549037).length < 2 ^ (prefixWord ++ tailWord_549037).sum := by decide
  have hdescent : baseEnd_549037 < baseStart_549037 := by decide
  rcases family_descends (prefixWord ++ tailWord_549037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549045 : List Nat := [1, 3, 3, 4, 2, 1, 2, 2, 1, 1, 3]
def baseStart_549045 : Nat := 118140960795 + 549045 * 2 ^ 59
def prefixEnd_549045 : Nat := 4983230072969 + 3 ^ 40 * 549045 * 2
def baseEnd_549045 : Nat := 281923985947909592612495

theorem tailTrace_549045 : CollatzResearch.WordTrace tailWord_549045 prefixEnd_549045 281923985947909592612495 := by
  unfold tailWord_549045
  simp only [CollatzResearch.WordTrace]
  refine ⟨20025316295911209265744589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13350210863940806177163059 20025316295911209265744589)
  ·
    refine ⟨7509493610966703474654221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20025316295911209265744589 7509493610966703474654221)
    ·
      refine ⟨2816060104112513802995333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7509493610966703474654221 2816060104112513802995333)
      ·
        refine ⟨528011269521096338061625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2816060104112513802995333 528011269521096338061625)
        ·
          refine ⟨396008452140822253546219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 528011269521096338061625 396008452140822253546219)
          ·
            refine ⟨594012678211233380319329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396008452140822253546219 594012678211233380319329)
            ·
              refine ⟨445509508658425035239497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 594012678211233380319329 445509508658425035239497)
              ·
                refine ⟨334132131493818776429623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 445509508658425035239497 334132131493818776429623)
                ·
                  refine ⟨501198197240728164644435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 334132131493818776429623 501198197240728164644435)
                  ·
                    refine ⟨751797295861092246966653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 501198197240728164644435 751797295861092246966653)
                    ·
                      refine ⟨281923985947909592612495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 751797295861092246966653 281923985947909592612495)
                      ·
                        rfl

theorem cell23_549045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_549045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549045 prefixEnd_549045 := by exact prefixLift 549045
  have htrace : WordTrace (prefixWord ++ tailWord_549045) baseStart_549045 baseEnd_549045 := by
    simpa [prefixWord, tailWord_549045, baseEnd_549045] using wordTrace_append hprefix tailTrace_549045
  have hstable : (prefixWord ++ tailWord_549045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549045).length < 2 ^ (prefixWord ++ tailWord_549045).sum := by decide
  have hdescent : baseEnd_549045 < baseStart_549045 := by decide
  rcases family_descends (prefixWord ++ tailWord_549045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549050 : List Nat := [3, 1, 1, 1, 2, 2, 2, 3, 4, 1, 3]
def baseStart_549050 : Nat := 118140960795 + 549050 * 2 ^ 59
def prefixEnd_549050 : Nat := 4983230072969 + 3 ^ 40 * 549050 * 2
def baseEnd_549050 : Nat := 281926553351182073049971

theorem tailTrace_549050 : CollatzResearch.WordTrace tailWord_549050 prefixEnd_549050 281926553351182073049971 := by
  unfold tailWord_549050
  simp only [CollatzResearch.WordTrace]
  refine ⟨5006374665223273779919151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13350332440595396746451069 5006374665223273779919151)
  ·
    refine ⟨7509561997834910669878727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5006374665223273779919151 7509561997834910669878727)
    ·
      refine ⟨11264342996752366004818091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7509561997834910669878727 11264342996752366004818091)
      ·
        refine ⟨16896514495128549007227137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11264342996752366004818091 16896514495128549007227137)
        ·
          refine ⟨12672385871346411755420353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16896514495128549007227137 12672385871346411755420353)
          ·
            refine ⟨9504289403509808816565265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12672385871346411755420353 9504289403509808816565265)
            ·
              refine ⟨7128217052632356612423949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9504289403509808816565265 7128217052632356612423949)
              ·
                refine ⟨2673081394737133729658981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7128217052632356612423949 2673081394737133729658981)
                ·
                  refine ⟨501202761513212574311059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2673081394737133729658981 501202761513212574311059)
                  ·
                    refine ⟨751804142269818861466589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 501202761513212574311059 751804142269818861466589)
                    ·
                      refine ⟨281926553351182073049971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 751804142269818861466589 281926553351182073049971)
                      ·
                        rfl

theorem cell23_549050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 4, 1, 3].length) (baseStart_549050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549050 prefixEnd_549050 := by exact prefixLift 549050
  have htrace : WordTrace (prefixWord ++ tailWord_549050) baseStart_549050 baseEnd_549050 := by
    simpa [prefixWord, tailWord_549050, baseEnd_549050] using wordTrace_append hprefix tailTrace_549050
  have hstable : (prefixWord ++ tailWord_549050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549050).length < 2 ^ (prefixWord ++ tailWord_549050).sum := by decide
  have hdescent : baseEnd_549050 < baseStart_549050 := by decide
  rcases family_descends (prefixWord ++ tailWord_549050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549057 : List Nat := [1, 2, 6, 1, 2, 2, 1, 8]
def baseStart_549057 : Nat := 118140960795 + 549057 * 2 ^ 59
def prefixEnd_549057 : Nat := 4983230072969 + 3 ^ 40 * 549057 * 2
def baseEnd_549057 : Nat := 10441857322806057246757

theorem tailTrace_549057 : CollatzResearch.WordTrace tailWord_549057 prefixEnd_549057 10441857322806057246757 := by
  unfold tailWord_549057
  simp only [CollatzResearch.WordTrace]
  refine ⟨20025753971867735315181425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13350502647911823543454283 20025753971867735315181425)
  ·
    refine ⟨15019315478900801486386069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20025753971867735315181425 15019315478900801486386069)
    ·
      refine ⟨704030413073475069674347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15019315478900801486386069 704030413073475069674347)
      ·
        refine ⟨1056045619610212604511521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 704030413073475069674347 1056045619610212604511521)
        ·
          refine ⟨792034214707659453383641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1056045619610212604511521 792034214707659453383641)
          ·
            refine ⟨594025661030744590037731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 792034214707659453383641 594025661030744590037731)
            ·
              refine ⟨891038491546116885056597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 594025661030744590037731 891038491546116885056597)
              ·
                refine ⟨10441857322806057246757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 891038491546116885056597 10441857322806057246757)
                ·
                  rfl

theorem cell23_549057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 8].length) (baseStart_549057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549057 prefixEnd_549057 := by exact prefixLift 549057
  have htrace : WordTrace (prefixWord ++ tailWord_549057) baseStart_549057 baseEnd_549057 := by
    simpa [prefixWord, tailWord_549057, baseEnd_549057] using wordTrace_append hprefix tailTrace_549057
  have hstable : (prefixWord ++ tailWord_549057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549057).length < 2 ^ (prefixWord ++ tailWord_549057).sum := by decide
  have hdescent : baseEnd_549057 < baseStart_549057 := by decide
  rcases family_descends (prefixWord ++ tailWord_549057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549101 : List Nat := [1, 5, 1, 2, 3, 2, 1, 2, 2, 1, 3]
def baseStart_549101 : Nat := 118140960795 + 549101 * 2 ^ 59
def prefixEnd_549101 : Nat := 4983230072969 + 3 ^ 40 * 549101 * 2
def baseEnd_549101 : Nat := 281952740864561373512237

theorem tailTrace_549101 : CollatzResearch.WordTrace tailWord_549101 prefixEnd_549101 281952740864561373512237 := by
  unfold tailWord_549101
  simp only [CollatzResearch.WordTrace]
  refine ⟨20027358783708330829783157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13351572522472220553188771 20027358783708330829783157)
  ·
    refine ⟨1877564885972656015292171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20027358783708330829783157 1877564885972656015292171)
    ·
      refine ⟨2816347328958984022938257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1877564885972656015292171 2816347328958984022938257)
      ·
        refine ⟨2112260496719238017203693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2816347328958984022938257 2112260496719238017203693)
        ·
          refine ⟨792097686269714256451385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2112260496719238017203693 792097686269714256451385)
          ·
            refine ⟨594073264702285692338539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 792097686269714256451385 594073264702285692338539)
            ·
              refine ⟨891109897053428538507809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 594073264702285692338539 891109897053428538507809)
              ·
                refine ⟨668332422790071403880857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 891109897053428538507809 668332422790071403880857)
                ·
                  refine ⟨501249317092553552910643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 668332422790071403880857 501249317092553552910643)
                  ·
                    refine ⟨751873975638830329365965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 501249317092553552910643 751873975638830329365965)
                    ·
                      refine ⟨281952740864561373512237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 751873975638830329365965 281952740864561373512237)
                      ·
                        rfl

theorem cell23_549101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_549101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549101 prefixEnd_549101 := by exact prefixLift 549101
  have htrace : WordTrace (prefixWord ++ tailWord_549101) baseStart_549101 baseEnd_549101 := by
    simpa [prefixWord, tailWord_549101, baseEnd_549101] using wordTrace_append hprefix tailTrace_549101
  have hstable : (prefixWord ++ tailWord_549101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549101).length < 2 ^ (prefixWord ++ tailWord_549101).sum := by decide
  have hdescent : baseEnd_549101 < baseStart_549101 := by decide
  rcases family_descends (prefixWord ++ tailWord_549101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549107 : List Nat := [1, 1, 1, 2, 2, 4, 3, 1, 4, 2, 2]
def baseStart_549107 : Nat := 118140960795 + 549107 * 2 ^ 59
def prefixEnd_549107 : Nat := 4983230072969 + 3 ^ 40 * 549107 * 2
def baseEnd_549107 : Nat := 281955821748488350037209

theorem tailTrace_549107 : CollatzResearch.WordTrace tailWord_549107 prefixEnd_549107 281955821748488350037209 := by
  unfold tailWord_549107
  simp only [CollatzResearch.WordTrace]
  refine ⟨20027577621686593854501575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13351718414457729236334383 20027577621686593854501575)
  ·
    refine ⟨30041366432529890781752363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20027577621686593854501575 30041366432529890781752363)
    ·
      refine ⟨45062049648794836172628545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30041366432529890781752363 45062049648794836172628545)
      ·
        refine ⟨33796537236596127129471409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45062049648794836172628545 33796537236596127129471409)
        ·
          refine ⟨25347402927447095347103557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33796537236596127129471409 25347402927447095347103557)
          ·
            refine ⟨4752638048896330377581917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25347402927447095347103557 4752638048896330377581917)
            ·
              refine ⟨1782239268336123891593219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4752638048896330377581917 1782239268336123891593219)
              ·
                refine ⟨2673358902504185837389829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1782239268336123891593219 2673358902504185837389829)
                ·
                  refine ⟨501254794219534844510593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2673358902504185837389829 501254794219534844510593)
                  ·
                    refine ⟨375941095664651133382945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 501254794219534844510593 375941095664651133382945)
                    ·
                      refine ⟨281955821748488350037209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 375941095664651133382945 281955821748488350037209)
                      ·
                        rfl

theorem cell23_549107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 4, 2, 2].length) (baseStart_549107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549107 prefixEnd_549107 := by exact prefixLift 549107
  have htrace : WordTrace (prefixWord ++ tailWord_549107) baseStart_549107 baseEnd_549107 := by
    simpa [prefixWord, tailWord_549107, baseEnd_549107] using wordTrace_append hprefix tailTrace_549107
  have hstable : (prefixWord ++ tailWord_549107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549107).length < 2 ^ (prefixWord ++ tailWord_549107).sum := by decide
  have hdescent : baseEnd_549107 < baseStart_549107 := by decide
  rcases family_descends (prefixWord ++ tailWord_549107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549110 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3]
def baseStart_549110 : Nat := 118140960795 + 549110 * 2 ^ 59
def prefixEnd_549110 : Nat := 4983230072969 + 3 ^ 40 * 549110 * 2
def baseEnd_549110 : Nat := 281957362190451838299695

theorem tailTrace_549110 : CollatzResearch.WordTrace tailWord_549110 prefixEnd_549110 281957362190451838299695 := by
  unfold tailWord_549110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1251730440042232835428799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13351791360450483577907189 1251730440042232835428799)
  ·
    refine ⟨1877595660063349253143199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1251730440042232835428799 1877595660063349253143199)
    ·
      refine ⟨2816393490095023879714799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1877595660063349253143199 2816393490095023879714799)
      ·
        refine ⟨4224590235142535819572199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2816393490095023879714799 4224590235142535819572199)
        ·
          refine ⟨6336885352713803729358299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4224590235142535819572199 6336885352713803729358299)
          ·
            refine ⟨9505328029070705594037449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6336885352713803729358299 9505328029070705594037449)
            ·
              refine ⟨7128996021803029195528087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9505328029070705594037449 7128996021803029195528087)
              ·
                refine ⟨10693494032704543793292131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7128996021803029195528087 10693494032704543793292131)
                ·
                  refine ⟨16040241049056815689938197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10693494032704543793292131 16040241049056815689938197)
                  ·
                    refine ⟨751886299174538235465853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16040241049056815689938197 751886299174538235465853)
                    ·
                      refine ⟨281957362190451838299695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 751886299174538235465853 281957362190451838299695)
                      ·
                        rfl

theorem cell23_549110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_549110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549110 prefixEnd_549110 := by exact prefixLift 549110
  have htrace : WordTrace (prefixWord ++ tailWord_549110) baseStart_549110 baseEnd_549110 := by
    simpa [prefixWord, tailWord_549110, baseEnd_549110] using wordTrace_append hprefix tailTrace_549110
  have hstable : (prefixWord ++ tailWord_549110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549110).length < 2 ^ (prefixWord ++ tailWord_549110).sum := by decide
  have hdescent : baseEnd_549110 < baseStart_549110 := by decide
  rcases family_descends (prefixWord ++ tailWord_549110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549180 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 4, 1, 4]
def baseStart_549180 : Nat := 118140960795 + 549180 * 2 ^ 59
def prefixEnd_549180 : Nat := 4983230072969 + 3 ^ 40 * 549180 * 2
def baseEnd_549180 : Nat := 281993305836266564424373

theorem tailTrace_549180 : CollatzResearch.WordTrace tailWord_549180 prefixEnd_549180 281993305836266564424373 := by
  unfold tailWord_549180
  simp only [CollatzResearch.WordTrace]
  refine ⟨10015120075211063660954497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13353493433614751547939329 10015120075211063660954497)
  ·
    refine ⟨7511340056408297745715873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10015120075211063660954497 7511340056408297745715873)
    ·
      refine ⟨5633505042306223309286905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7511340056408297745715873 5633505042306223309286905)
      ·
        refine ⟨4225128781729667481965179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5633505042306223309286905 4225128781729667481965179)
        ·
          refine ⟨6337693172594501222947769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4225128781729667481965179 6337693172594501222947769)
          ·
            refine ⟨4753269879445875917210827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6337693172594501222947769 4753269879445875917210827)
            ·
              refine ⟨7129904819168813875816241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4753269879445875917210827 7129904819168813875816241)
              ·
                refine ⟨5347428614376610406862181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7129904819168813875816241 5347428614376610406862181)
                ·
                  refine ⟨1002642865195614451286659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5347428614376610406862181 1002642865195614451286659)
                  ·
                    refine ⟨1503964297793421676929989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1002642865195614451286659 1503964297793421676929989)
                    ·
                      refine ⟨281993305836266564424373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1503964297793421676929989 281993305836266564424373)
                      ·
                        rfl

theorem cell23_549180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_549180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549180 prefixEnd_549180 := by exact prefixLift 549180
  have htrace : WordTrace (prefixWord ++ tailWord_549180) baseStart_549180 baseEnd_549180 := by
    simpa [prefixWord, tailWord_549180, baseEnd_549180] using wordTrace_append hprefix tailTrace_549180
  have hstable : (prefixWord ++ tailWord_549180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549180).length < 2 ^ (prefixWord ++ tailWord_549180).sum := by decide
  have hdescent : baseEnd_549180 < baseStart_549180 := by decide
  rcases family_descends (prefixWord ++ tailWord_549180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549193 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 1, 3, 6]
def baseStart_549193 : Nat := 118140960795 + 549193 * 2 ^ 59
def prefixEnd_549193 : Nat := 4983230072969 + 3 ^ 40 * 549193 * 2
def baseEnd_549193 : Nat := 281999981084775013561813

theorem tailTrace_549193 : CollatzResearch.WordTrace tailWord_549193 prefixEnd_549193 281999981084775013561813 := by
  unfold tailWord_549193
  simp only [CollatzResearch.WordTrace]
  refine ⟨20030714299375030542132233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13353809532916687028088155 20030714299375030542132233)
  ·
    refine ⟨15023035724531272906599175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20030714299375030542132233 15023035724531272906599175)
    ·
      refine ⟨22534553586796909359898763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15023035724531272906599175 22534553586796909359898763)
      ·
        refine ⟨33801830380195364039848145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22534553586796909359898763 33801830380195364039848145)
        ·
          refine ⟨25351372785146523029886109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33801830380195364039848145 25351372785146523029886109)
          ·
            refine ⟨9506764794429946136207291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25351372785146523029886109 9506764794429946136207291)
            ·
              refine ⟨14260147191644919204310937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9506764794429946136207291 14260147191644919204310937)
              ·
                refine ⟨10695110393733689403233203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14260147191644919204310937 10695110393733689403233203)
                ·
                  refine ⟨16042665590600534104849805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10695110393733689403233203 16042665590600534104849805)
                  ·
                    refine ⟨6015999596475200289318677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16042665590600534104849805 6015999596475200289318677)
                    ·
                      refine ⟨281999981084775013561813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6015999596475200289318677 281999981084775013561813)
                      ·
                        rfl

theorem cell23_549193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 3, 6].length) (baseStart_549193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549193 prefixEnd_549193 := by exact prefixLift 549193
  have htrace : WordTrace (prefixWord ++ tailWord_549193) baseStart_549193 baseEnd_549193 := by
    simpa [prefixWord, tailWord_549193, baseEnd_549193] using wordTrace_append hprefix tailTrace_549193
  have hstable : (prefixWord ++ tailWord_549193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549193).length < 2 ^ (prefixWord ++ tailWord_549193).sum := by decide
  have hdescent : baseEnd_549193 < baseStart_549193 := by decide
  rcases family_descends (prefixWord ++ tailWord_549193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549203 : List Nat := [1, 1, 1, 2, 1, 1, 4, 4, 8]
def baseStart_549203 : Nat := 118140960795 + 549203 * 2 ^ 59
def prefixEnd_549203 : Nat := 4983230072969 + 3 ^ 40 * 549203 * 2
def baseEnd_549203 : Nat := 31333901765702219381863

theorem tailTrace_549203 : CollatzResearch.WordTrace tailWord_549203 prefixEnd_549203 31333901765702219381863 := by
  unfold tailWord_549203
  simp only [CollatzResearch.WordTrace]
  refine ⟨20031079029338802249996263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13354052686225868166664175 20031079029338802249996263)
  ·
    refine ⟨30046618544008203374994395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20031079029338802249996263 30046618544008203374994395)
    ·
      refine ⟨45069927816012305062491593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30046618544008203374994395 45069927816012305062491593)
      ·
        refine ⟨33802445862009228796868695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45069927816012305062491593 33802445862009228796868695)
        ·
          refine ⟨50703668793013843195303043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33802445862009228796868695 50703668793013843195303043)
          ·
            refine ⟨76055503189520764792954565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50703668793013843195303043 76055503189520764792954565)
            ·
              refine ⟨14260406848035143398678981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76055503189520764792954565 14260406848035143398678981)
              ·
                refine ⟨2673826284006589387252309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14260406848035143398678981 2673826284006589387252309)
                ·
                  refine ⟨31333901765702219381863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2673826284006589387252309 31333901765702219381863)
                  ·
                    rfl

theorem cell23_549203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 8].length) (baseStart_549203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549203 prefixEnd_549203 := by exact prefixLift 549203
  have htrace : WordTrace (prefixWord ++ tailWord_549203) baseStart_549203 baseEnd_549203 := by
    simpa [prefixWord, tailWord_549203, baseEnd_549203] using wordTrace_append hprefix tailTrace_549203
  have hstable : (prefixWord ++ tailWord_549203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549203).length < 2 ^ (prefixWord ++ tailWord_549203).sum := by decide
  have hdescent : baseEnd_549203 < baseStart_549203 := by decide
  rcases family_descends (prefixWord ++ tailWord_549203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549237 : List Nat := [1, 3, 4, 1, 2, 1, 2, 3, 6]
def baseStart_549237 : Nat := 118140960795 + 549237 * 2 ^ 59
def prefixEnd_549237 : Nat := 4983230072969 + 3 ^ 40 * 549237 * 2
def baseEnd_549237 : Nat := 31335841581508093490179

theorem tailTrace_549237 : CollatzResearch.WordTrace tailWord_549237 prefixEnd_549237 31335841581508093490179 := by
  unfold tailWord_549237
  simp only [CollatzResearch.WordTrace]
  refine ⟨20032319111215626056733965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13354879407477084037822643 20032319111215626056733965)
  ·
    refine ⟨7512119666705859771275237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20032319111215626056733965 7512119666705859771275237)
    ·
      refine ⟨1408522437507348707114107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7512119666705859771275237 1408522437507348707114107)
      ·
        refine ⟨2112783656261023060671161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1408522437507348707114107 2112783656261023060671161)
        ·
          refine ⟨1584587742195767295503371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2112783656261023060671161 1584587742195767295503371)
          ·
            refine ⟨2376881613293650943255057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1584587742195767295503371 2376881613293650943255057)
            ·
              refine ⟨1782661209970238207441293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2376881613293650943255057 1782661209970238207441293)
              ·
                refine ⟨668497953738839327790485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1782661209970238207441293 668497953738839327790485)
                ·
                  refine ⟨31335841581508093490179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 668497953738839327790485 31335841581508093490179)
                  ·
                    rfl

theorem cell23_549237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 6].length) (baseStart_549237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549237 prefixEnd_549237 := by exact prefixLift 549237
  have htrace : WordTrace (prefixWord ++ tailWord_549237) baseStart_549237 baseEnd_549237 := by
    simpa [prefixWord, tailWord_549237, baseEnd_549237] using wordTrace_append hprefix tailTrace_549237
  have hstable : (prefixWord ++ tailWord_549237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549237).length < 2 ^ (prefixWord ++ tailWord_549237).sum := by decide
  have hdescent : baseEnd_549237 < baseStart_549237 := by decide
  rcases family_descends (prefixWord ++ tailWord_549237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549247 : List Nat := [1, 1, 2, 2, 1, 1, 2, 6, 3, 1, 3]
def baseStart_549247 : Nat := 118140960795 + 549247 * 2 ^ 59
def prefixEnd_549247 : Nat := 4983230072969 + 3 ^ 40 * 549247 * 2
def baseEnd_549247 : Nat := 282027709040117802286565

theorem tailTrace_549247 : CollatzResearch.WordTrace tailWord_549247 prefixEnd_549247 282027709040117802286565 := by
  unfold tailWord_549247
  simp only [CollatzResearch.WordTrace]
  refine ⟨20032683841179397764597995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13355122560786265176398663 20032683841179397764597995)
  ·
    refine ⟨30049025761769096646896993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20032683841179397764597995 30049025761769096646896993)
    ·
      refine ⟨22536769321326822485172745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30049025761769096646896993 22536769321326822485172745)
      ·
        refine ⟨16902576990995116863879559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22536769321326822485172745 16902576990995116863879559)
        ·
          refine ⟨25353865486492675295819339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16902576990995116863879559 25353865486492675295819339)
          ·
            refine ⟨38030798229739012943729009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25353865486492675295819339 38030798229739012943729009)
            ·
              refine ⟨28523098672304259707796757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38030798229739012943729009 28523098672304259707796757)
              ·
                refine ⟨1337020250264262173802973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28523098672304259707796757 1337020250264262173802973)
                ·
                  refine ⟨501382593849098315176115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1337020250264262173802973 501382593849098315176115)
                  ·
                    refine ⟨752073890773647472764173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 501382593849098315176115 752073890773647472764173)
                    ·
                      refine ⟨282027709040117802286565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 752073890773647472764173 282027709040117802286565)
                      ·
                        rfl

theorem cell23_549247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 3, 1, 3].length) (baseStart_549247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549247 prefixEnd_549247 := by exact prefixLift 549247
  have htrace : WordTrace (prefixWord ++ tailWord_549247) baseStart_549247 baseEnd_549247 := by
    simpa [prefixWord, tailWord_549247, baseEnd_549247] using wordTrace_append hprefix tailTrace_549247
  have hstable : (prefixWord ++ tailWord_549247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549247).length < 2 ^ (prefixWord ++ tailWord_549247).sum := by decide
  have hdescent : baseEnd_549247 < baseStart_549247 := by decide
  rcases family_descends (prefixWord ++ tailWord_549247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549251 : List Nat := [1, 1, 1, 3, 7, 1, 1, 1, 2, 2, 3]
def baseStart_549251 : Nat := 118140960795 + 549251 * 2 ^ 59
def prefixEnd_549251 : Nat := 4983230072969 + 3 ^ 40 * 549251 * 2
def baseEnd_549251 : Nat := 282029762962735786636547

theorem tailTrace_549251 : CollatzResearch.WordTrace tailWord_549251 prefixEnd_549251 282029762962735786636547 := by
  unfold tailWord_549251
  simp only [CollatzResearch.WordTrace]
  refine ⟨20032829733164906447743607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13355219822109937631829071 20032829733164906447743607)
  ·
    refine ⟨30049244599747359671615411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20032829733164906447743607 30049244599747359671615411)
    ·
      refine ⟨45073866899621039507423117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30049244599747359671615411 45073866899621039507423117)
      ·
        refine ⟨16902700087357889815283669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45073866899621039507423117 16902700087357889815283669)
        ·
          refine ⟨396157033297450542545711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 16902700087357889815283669 396157033297450542545711)
          ·
            refine ⟨594235549946175813818567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396157033297450542545711 594235549946175813818567)
            ·
              refine ⟨891353324919263720727851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 594235549946175813818567 891353324919263720727851)
              ·
                refine ⟨1337029987378895581091777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 891353324919263720727851 1337029987378895581091777)
                ·
                  refine ⟨1002772490534171685818833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1337029987378895581091777 1002772490534171685818833)
                  ·
                    refine ⟨752079367900628764364125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1002772490534171685818833 752079367900628764364125)
                    ·
                      refine ⟨282029762962735786636547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 752079367900628764364125 282029762962735786636547)
                      ·
                        rfl

theorem cell23_549251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 2, 2, 3].length) (baseStart_549251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549251 prefixEnd_549251 := by exact prefixLift 549251
  have htrace : WordTrace (prefixWord ++ tailWord_549251) baseStart_549251 baseEnd_549251 := by
    simpa [prefixWord, tailWord_549251, baseEnd_549251] using wordTrace_append hprefix tailTrace_549251
  have hstable : (prefixWord ++ tailWord_549251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549251).length < 2 ^ (prefixWord ++ tailWord_549251).sum := by decide
  have hdescent : baseEnd_549251 < baseStart_549251 := by decide
  rcases family_descends (prefixWord ++ tailWord_549251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549258 : List Nat := [3, 1, 2, 5, 1, 1, 2, 3, 1, 4]
def baseStart_549258 : Nat := 118140960795 + 549258 * 2 ^ 59
def prefixEnd_549258 : Nat := 4983230072969 + 3 ^ 40 * 549258 * 2
def baseEnd_549258 : Nat := 94011119109105753083005

theorem tailTrace_549258 : CollatzResearch.WordTrace tailWord_549258 prefixEnd_549258 94011119109105753083005 := by
  unfold tailWord_549258
  simp only [CollatzResearch.WordTrace]
  refine ⟨5008271261034886660812107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13355390029426364428832285 5008271261034886660812107)
  ·
    refine ⟨7512406891552329991218161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5008271261034886660812107 7512406891552329991218161)
    ·
      refine ⟨5634305168664247493413621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7512406891552329991218161 5634305168664247493413621)
      ·
        refine ⟨528216109562273202507527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5634305168664247493413621 528216109562273202507527)
        ·
          refine ⟨792324164343409803761291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 528216109562273202507527 792324164343409803761291)
          ·
            refine ⟨1188486246515114705641937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 792324164343409803761291 1188486246515114705641937)
            ·
              refine ⟨891364684886336029231453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1188486246515114705641937 891364684886336029231453)
              ·
                refine ⟨334261756832376010961795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 891364684886336029231453 334261756832376010961795)
                ·
                  refine ⟨501392635248564016442693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 334261756832376010961795 501392635248564016442693)
                  ·
                    refine ⟨94011119109105753083005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 501392635248564016442693 94011119109105753083005)
                    ·
                      rfl

theorem cell23_549258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_549258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549258 prefixEnd_549258 := by exact prefixLift 549258
  have htrace : WordTrace (prefixWord ++ tailWord_549258) baseStart_549258 baseEnd_549258 := by
    simpa [prefixWord, tailWord_549258, baseEnd_549258] using wordTrace_append hprefix tailTrace_549258
  have hstable : (prefixWord ++ tailWord_549258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549258).length < 2 ^ (prefixWord ++ tailWord_549258).sum := by decide
  have hdescent : baseEnd_549258 < baseStart_549258 := by decide
  rcases family_descends (prefixWord ++ tailWord_549258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549297 : List Nat := [1, 2, 2, 4, 1, 2, 3, 1, 1, 6]
def baseStart_549297 : Nat := 118140960795 + 549297 * 2 ^ 59
def prefixEnd_549297 : Nat := 4983230072969 + 3 ^ 40 * 549297 * 2
def baseEnd_549297 : Nat := 94017794357614202220445

theorem tailTrace_549297 : CollatzResearch.WordTrace tailWord_549297 prefixEnd_549297 94017794357614202220445 := by
  unfold tailWord_549297
  simp only [CollatzResearch.WordTrace]
  refine ⟨20034507490998256303918145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13356338327332170869278763 20034507490998256303918145)
  ·
    refine ⟨15025880618248692227938609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20034507490998256303918145 15025880618248692227938609)
    ·
      refine ⟨11269410463686519170953957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15025880618248692227938609 11269410463686519170953957)
      ·
        refine ⟨2113014461941222344553867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11269410463686519170953957 2113014461941222344553867)
        ·
          refine ⟨3169521692911833516830801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2113014461941222344553867 3169521692911833516830801)
          ·
            refine ⟨2377141269683875137623101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3169521692911833516830801 2377141269683875137623101)
            ·
              refine ⟨891427976131453176608663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2377141269683875137623101 891427976131453176608663)
              ·
                refine ⟨1337141964197179764912995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 891427976131453176608663 1337141964197179764912995)
                ·
                  refine ⟨2005712946295769647369493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1337141964197179764912995 2005712946295769647369493)
                  ·
                    refine ⟨94017794357614202220445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2005712946295769647369493 94017794357614202220445)
                    ·
                      rfl

theorem cell23_549297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 6].length) (baseStart_549297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549297 prefixEnd_549297 := by exact prefixLift 549297
  have htrace : WordTrace (prefixWord ++ tailWord_549297) baseStart_549297 baseEnd_549297 := by
    simpa [prefixWord, tailWord_549297, baseEnd_549297] using wordTrace_append hprefix tailTrace_549297
  have hstable : (prefixWord ++ tailWord_549297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549297).length < 2 ^ (prefixWord ++ tailWord_549297).sum := by decide
  have hdescent : baseEnd_549297 < baseStart_549297 := by decide
  rcases family_descends (prefixWord ++ tailWord_549297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549324 : List Nat := [2, 2, 1, 4, 3, 1, 2, 1, 1, 1, 5]
def baseStart_549324 : Nat := 118140960795 + 549324 * 2 ^ 59
def prefixEnd_549324 : Nat := 4983230072969 + 3 ^ 40 * 549324 * 2
def baseEnd_549324 : Nat := 282067247050514001023711

theorem tailTrace_549324 : CollatzResearch.WordTrace tailWord_549324 prefixEnd_549324 282067247050514001023711 := by
  unfold tailWord_549324
  simp only [CollatzResearch.WordTrace]
  refine ⟨10017746130950219957575513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13356994841266959943434017 10017746130950219957575513)
  ·
    refine ⟨7513309598212664968181635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10017746130950219957575513 7513309598212664968181635)
    ·
      refine ⟨11269964397318997452272453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7513309598212664968181635 11269964397318997452272453)
      ·
        refine ⟨2113118324497312022301085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11269964397318997452272453 2113118324497312022301085)
        ·
          refine ⟨792419371686492008362907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2113118324497312022301085 792419371686492008362907)
          ·
            refine ⟨1188629057529738012544361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 792419371686492008362907 1188629057529738012544361)
            ·
              refine ⟨891471793147303509408271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1188629057529738012544361 891471793147303509408271)
              ·
                refine ⟨1337207689720955264112407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 891471793147303509408271 1337207689720955264112407)
                ·
                  refine ⟨2005811534581432896168611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1337207689720955264112407 2005811534581432896168611)
                  ·
                    refine ⟨3008717301872149344252917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2005811534581432896168611 3008717301872149344252917)
                    ·
                      refine ⟨282067247050514001023711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3008717301872149344252917 282067247050514001023711)
                      ·
                        rfl

theorem cell23_549324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_549324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549324 prefixEnd_549324 := by exact prefixLift 549324
  have htrace : WordTrace (prefixWord ++ tailWord_549324) baseStart_549324 baseEnd_549324 := by
    simpa [prefixWord, tailWord_549324, baseEnd_549324] using wordTrace_append hprefix tailTrace_549324
  have hstable : (prefixWord ++ tailWord_549324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549324).length < 2 ^ (prefixWord ++ tailWord_549324).sum := by decide
  have hdescent : baseEnd_549324 < baseStart_549324 := by decide
  rcases family_descends (prefixWord ++ tailWord_549324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549370 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 3, 8]
def baseStart_549370 : Nat := 118140960795 + 549370 * 2 ^ 59
def prefixEnd_549370 : Nat := 4983230072969 + 3 ^ 40 * 549370 * 2
def baseEnd_549370 : Nat := 94030289053540273682833

theorem tailTrace_549370 : CollatzResearch.WordTrace tailWord_549370 prefixEnd_549370 94030289053540273682833 := by
  unfold tailWord_549370
  simp only [CollatzResearch.WordTrace]
  refine ⟨5009292504933447442831391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13358113346489193180883709 5009292504933447442831391)
  ·
    refine ⟨7513938757400171164247087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5009292504933447442831391 7513938757400171164247087)
    ·
      refine ⟨11270908136100256746370631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7513938757400171164247087 11270908136100256746370631)
      ·
        refine ⟨16906362204150385119555947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11270908136100256746370631 16906362204150385119555947)
        ·
          refine ⟨25359543306225577679333921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16906362204150385119555947 25359543306225577679333921)
          ·
            refine ⟨19019657479669183259500441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25359543306225577679333921 19019657479669183259500441)
            ·
              refine ⟨14264743109751887444625331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19019657479669183259500441 14264743109751887444625331)
              ·
                refine ⟨21397114664627831166937997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14264743109751887444625331 21397114664627831166937997)
                ·
                  refine ⟨8023917999235436687601749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21397114664627831166937997 8023917999235436687601749)
                  ·
                    refine ⟨94030289053540273682833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8023917999235436687601749 94030289053540273682833)
                    ·
                      rfl

theorem cell23_549370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 3, 8].length) (baseStart_549370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549370 prefixEnd_549370 := by exact prefixLift 549370
  have htrace : WordTrace (prefixWord ++ tailWord_549370) baseStart_549370 baseEnd_549370 := by
    simpa [prefixWord, tailWord_549370, baseEnd_549370] using wordTrace_append hprefix tailTrace_549370
  have hstable : (prefixWord ++ tailWord_549370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549370).length < 2 ^ (prefixWord ++ tailWord_549370).sum := by decide
  have hdescent : baseEnd_549370 < baseStart_549370 := by decide
  rcases family_descends (prefixWord ++ tailWord_549370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549389 : List Nat := [1, 7, 1, 1, 1, 1, 4, 2, 1, 2, 2]
def baseStart_549389 : Nat := 118140960795 + 549389 * 2 ^ 59
def prefixEnd_549389 : Nat := 4983230072969 + 3 ^ 40 * 549389 * 2
def baseEnd_549389 : Nat := 282100623293056246710913

theorem tailTrace_549389 : CollatzResearch.WordTrace tailWord_549389 prefixEnd_549389 282100623293056246710913 := by
  unfold tailWord_549389
  simp only [CollatzResearch.WordTrace]
  refine ⟨20037863006664956016267221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13358575337776637344178147 20037863006664956016267221)
  ·
    refine ⟨469637414218709906631263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 20037863006664956016267221 469637414218709906631263)
    ·
      refine ⟨704456121328064859946895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 469637414218709906631263 704456121328064859946895)
      ·
        refine ⟨1056684181992097289920343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 704456121328064859946895 1056684181992097289920343)
        ·
          refine ⟨1585026272988145934880515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1056684181992097289920343 1585026272988145934880515)
          ·
            refine ⟨2377539409482218902320773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1585026272988145934880515 2377539409482218902320773)
            ·
              refine ⟨445788639277916044185145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2377539409482218902320773 445788639277916044185145)
              ·
                refine ⟨334341479458437033138859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 445788639277916044185145 334341479458437033138859)
                ·
                  refine ⟨501512219187655549708289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 334341479458437033138859 501512219187655549708289)
                  ·
                    refine ⟨376134164390741662281217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 501512219187655549708289 376134164390741662281217)
                    ·
                      refine ⟨282100623293056246710913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 376134164390741662281217 282100623293056246710913)
                      ·
                        rfl

theorem cell23_549389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_549389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549389 prefixEnd_549389 := by exact prefixLift 549389
  have htrace : WordTrace (prefixWord ++ tailWord_549389) baseStart_549389 baseEnd_549389 := by
    simpa [prefixWord, tailWord_549389, baseEnd_549389] using wordTrace_append hprefix tailTrace_549389
  have hstable : (prefixWord ++ tailWord_549389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549389).length < 2 ^ (prefixWord ++ tailWord_549389).sum := by decide
  have hdescent : baseEnd_549389 < baseStart_549389 := by decide
  rcases family_descends (prefixWord ++ tailWord_549389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549397 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 1, 6, 3]
def baseStart_549397 : Nat := 118140960795 + 549397 * 2 ^ 59
def prefixEnd_549397 : Nat := 4983230072969 + 3 ^ 40 * 549397 * 2
def baseEnd_549397 : Nat := 282104731138292215410875

theorem tailTrace_549397 : CollatzResearch.WordTrace tailWord_549397 prefixEnd_549397 282104731138292215410875 := by
  unfold tailWord_549397
  simp only [CollatzResearch.WordTrace]
  refine ⟨20038154790635973382558445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13358769860423982255038963 20038154790635973382558445)
  ·
    refine ⟨7514308046488490018459417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20038154790635973382558445 7514308046488490018459417)
    ·
      refine ⟨5635731034866367513844563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7514308046488490018459417 5635731034866367513844563)
      ·
        refine ⟨8453596552299551270766845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5635731034866367513844563 8453596552299551270766845)
        ·
          refine ⟨3170098707112331726537567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8453596552299551270766845 3170098707112331726537567)
          ·
            refine ⟨4755148060668497589806351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3170098707112331726537567 4755148060668497589806351)
            ·
              refine ⟨7132722091002746384709527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4755148060668497589806351 7132722091002746384709527)
              ·
                refine ⟨10699083136504119577064291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7132722091002746384709527 10699083136504119577064291)
                ·
                  refine ⟨16048624704756179365596437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10699083136504119577064291 16048624704756179365596437)
                  ·
                    refine ⟨752279283035445907762333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16048624704756179365596437 752279283035445907762333)
                    ·
                      refine ⟨282104731138292215410875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 752279283035445907762333 282104731138292215410875)
                      ·
                        rfl

theorem cell23_549397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_549397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549397 prefixEnd_549397 := by exact prefixLift 549397
  have htrace : WordTrace (prefixWord ++ tailWord_549397) baseStart_549397 baseEnd_549397 := by
    simpa [prefixWord, tailWord_549397, baseEnd_549397] using wordTrace_append hprefix tailTrace_549397
  have hstable : (prefixWord ++ tailWord_549397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549397).length < 2 ^ (prefixWord ++ tailWord_549397).sum := by decide
  have hdescent : baseEnd_549397 < baseStart_549397 := by decide
  rcases family_descends (prefixWord ++ tailWord_549397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549411 : List Nat := [1, 1, 1, 4, 4, 2, 2, 1, 1, 4, 2]
def baseStart_549411 : Nat := 118140960795 + 549411 * 2 ^ 59
def prefixEnd_549411 : Nat := 4983230072969 + 3 ^ 40 * 549411 * 2
def baseEnd_549411 : Nat := 282111919867455160635811

theorem tailTrace_549411 : CollatzResearch.WordTrace tailWord_549411 prefixEnd_549411 282111919867455160635811 := by
  unfold tailWord_549411
  simp only [CollatzResearch.WordTrace]
  refine ⟨20038665412585253773568087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13359110275056835849045391 20038665412585253773568087)
  ·
    refine ⟨30057998118877880660352131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20038665412585253773568087 30057998118877880660352131)
    ·
      refine ⟨45086997178316820990528197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30057998118877880660352131 45086997178316820990528197)
      ·
        refine ⟨8453811970934403935724037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45086997178316820990528197 8453811970934403935724037)
        ·
          refine ⟨1585089744550200737948257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8453811970934403935724037 1585089744550200737948257)
          ·
            refine ⟨1188817308412650553461193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1585089744550200737948257 1188817308412650553461193)
            ·
              refine ⟨891612981309487915095895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1188817308412650553461193 891612981309487915095895)
              ·
                refine ⟨1337419471964231872643843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 891612981309487915095895 1337419471964231872643843)
                ·
                  refine ⟨2006129207946347808965765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1337419471964231872643843 2006129207946347808965765)
                  ·
                    refine ⟨376149226489940214181081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2006129207946347808965765 376149226489940214181081)
                    ·
                      refine ⟨282111919867455160635811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 376149226489940214181081 282111919867455160635811)
                      ·
                        rfl

theorem cell23_549411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 4, 2].length) (baseStart_549411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549411 prefixEnd_549411 := by exact prefixLift 549411
  have htrace : WordTrace (prefixWord ++ tailWord_549411) baseStart_549411 baseEnd_549411 := by
    simpa [prefixWord, tailWord_549411, baseEnd_549411] using wordTrace_append hprefix tailTrace_549411
  have hstable : (prefixWord ++ tailWord_549411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549411).length < 2 ^ (prefixWord ++ tailWord_549411).sum := by decide
  have hdescent : baseEnd_549411 < baseStart_549411 := by decide
  rcases family_descends (prefixWord ++ tailWord_549411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549427 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 1, 5, 3]
def baseStart_549427 : Nat := 118140960795 + 549427 * 2 ^ 59
def prefixEnd_549427 : Nat := 4983230072969 + 3 ^ 40 * 549427 * 2
def baseEnd_549427 : Nat := 282120135557927098035737

theorem tailTrace_549427 : CollatzResearch.WordTrace tailWord_549427 prefixEnd_549427 282120135557927098035737 := by
  unfold tailWord_549427
  simp only [CollatzResearch.WordTrace]
  refine ⟨20039248980527288506150535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13359499320351525670767023 20039248980527288506150535)
  ·
    refine ⟨30058873470790932759225803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20039248980527288506150535 30058873470790932759225803)
    ·
      refine ⟨45088310206186399138838705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30058873470790932759225803 45088310206186399138838705)
      ·
        refine ⟨33816232654639799354129029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45088310206186399138838705 33816232654639799354129029)
        ·
          refine ⟨6340543622744962378899193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33816232654639799354129029 6340543622744962378899193)
          ·
            refine ⟨4755407717058721784174395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6340543622744962378899193 4755407717058721784174395)
            ·
              refine ⟨7133111575588082676261593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4755407717058721784174395 7133111575588082676261593)
              ·
                refine ⟨5349833681691062007196195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7133111575588082676261593 5349833681691062007196195)
                ·
                  refine ⟨8024750522536593010794293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5349833681691062007196195 8024750522536593010794293)
                  ·
                    refine ⟨752320361487805594761965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8024750522536593010794293 752320361487805594761965)
                    ·
                      refine ⟨282120135557927098035737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 752320361487805594761965 282120135557927098035737)
                      ·
                        rfl

theorem cell23_549427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 5, 3].length) (baseStart_549427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549427 prefixEnd_549427 := by exact prefixLift 549427
  have htrace : WordTrace (prefixWord ++ tailWord_549427) baseStart_549427 baseEnd_549427 := by
    simpa [prefixWord, tailWord_549427, baseEnd_549427] using wordTrace_append hprefix tailTrace_549427
  have hstable : (prefixWord ++ tailWord_549427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549427).length < 2 ^ (prefixWord ++ tailWord_549427).sum := by decide
  have hdescent : baseEnd_549427 < baseStart_549427 := by decide
  rcases family_descends (prefixWord ++ tailWord_549427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549434 : List Nat := [3, 1, 1, 1, 3, 3, 1, 5, 5]
def baseStart_549434 : Nat := 118140960795 + 549434 * 2 ^ 59
def prefixEnd_549434 : Nat := 4983230072969 + 3 ^ 40 * 549434 * 2
def baseEnd_549434 : Nat := 31347081102500952294245

theorem tailTrace_549434 : CollatzResearch.WordTrace tailWord_549434 prefixEnd_549434 31347081102500952294245 := by
  unfold tailWord_549434
  simp only [CollatzResearch.WordTrace]
  refine ⟨5009876072875482175413839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13359669527667952467770237 5009876072875482175413839)
  ·
    refine ⟨7514814109313223263120759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5009876072875482175413839 7514814109313223263120759)
    ·
      refine ⟨11272221163969834894681139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7514814109313223263120759 11272221163969834894681139)
      ·
        refine ⟨16908331745954752342021709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11272221163969834894681139 16908331745954752342021709)
        ·
          refine ⟨6340624404733032128258141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16908331745954752342021709 6340624404733032128258141)
          ·
            refine ⟨2377734151774887048096803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6340624404733032128258141 2377734151774887048096803)
            ·
              refine ⟨3566601227662330572145205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2377734151774887048096803 3566601227662330572145205)
              ·
                refine ⟨334368865093343491138613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3566601227662330572145205 334368865093343491138613)
                ·
                  refine ⟨31347081102500952294245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 334368865093343491138613 31347081102500952294245)
                  ·
                    rfl

theorem cell23_549434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 5, 5].length) (baseStart_549434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549434 prefixEnd_549434 := by exact prefixLift 549434
  have htrace : WordTrace (prefixWord ++ tailWord_549434) baseStart_549434 baseEnd_549434 := by
    simpa [prefixWord, tailWord_549434, baseEnd_549434] using wordTrace_append hprefix tailTrace_549434
  have hstable : (prefixWord ++ tailWord_549434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549434).length < 2 ^ (prefixWord ++ tailWord_549434).sum := by decide
  have hdescent : baseEnd_549434 < baseStart_549434 := by decide
  rcases family_descends (prefixWord ++ tailWord_549434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549454 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2]
def baseStart_549454 : Nat := 118140960795 + 549454 * 2 ^ 59
def prefixEnd_549454 : Nat := 4983230072969 + 3 ^ 40 * 549454 * 2
def baseEnd_549454 : Nat := 282133999535598492398113

theorem tailTrace_549454 : CollatzResearch.WordTrace tailWord_549454 prefixEnd_549454 282133999535598492398113 := by
  unfold tailWord_549454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2505029218928684014672927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13360155834286314744922277 2505029218928684014672927)
  ·
    refine ⟨3757543828393026022009391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2505029218928684014672927 3757543828393026022009391)
    ·
      refine ⟨5636315742589539033014087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3757543828393026022009391 5636315742589539033014087)
      ·
        refine ⟨8454473613884308549521131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5636315742589539033014087 8454473613884308549521131)
        ·
          refine ⟨12681710420826462824281697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8454473613884308549521131 12681710420826462824281697)
          ·
            refine ⟨9511282815619847118211273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12681710420826462824281697 9511282815619847118211273)
            ·
              refine ⟨7133462111714885338658455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9511282815619847118211273 7133462111714885338658455)
              ·
                refine ⟨10700193167572328007987683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7133462111714885338658455 10700193167572328007987683)
                ·
                  refine ⟨16050289751358492011981525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10700193167572328007987683 16050289751358492011981525)
                  ·
                    refine ⟨376178666047464656530817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16050289751358492011981525 376178666047464656530817)
                    ·
                      refine ⟨282133999535598492398113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 376178666047464656530817 282133999535598492398113)
                      ·
                        rfl

theorem cell23_549454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2].length) (baseStart_549454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549454 prefixEnd_549454 := by exact prefixLift 549454
  have htrace : WordTrace (prefixWord ++ tailWord_549454) baseStart_549454 baseEnd_549454 := by
    simpa [prefixWord, tailWord_549454, baseEnd_549454] using wordTrace_append hprefix tailTrace_549454
  have hstable : (prefixWord ++ tailWord_549454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549454).length < 2 ^ (prefixWord ++ tailWord_549454).sum := by decide
  have hdescent : baseEnd_549454 < baseStart_549454 := by decide
  rcases family_descends (prefixWord ++ tailWord_549454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549484 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 1, 6, 2]
def baseStart_549484 : Nat := 118140960795 + 549484 * 2 ^ 59
def prefixEnd_549484 : Nat := 4983230072969 + 3 ^ 40 * 549484 * 2
def baseEnd_549484 : Nat := 282149403955233375022975

theorem tailTrace_549484 : CollatzResearch.WordTrace tailWord_549484 prefixEnd_549484 282149403955233375022975 := by
  unfold tailWord_549484
  simp only [CollatzResearch.WordTrace]
  refine ⟨10020663970660393620487753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13360885294213858160650337 10020663970660393620487753)
  ·
    refine ⟨7515497977995295215365815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10020663970660393620487753 7515497977995295215365815)
    ·
      refine ⟨11273246966992942823048723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7515497977995295215365815 11273246966992942823048723)
      ·
        refine ⟨16909870450489414234573085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11273246966992942823048723 16909870450489414234573085)
        ·
          refine ⟨6341201418933530337964907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16909870450489414234573085 6341201418933530337964907)
          ·
            refine ⟨9511802128400295506947361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6341201418933530337964907 9511802128400295506947361)
            ·
              refine ⟨7133851596300221630210521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9511802128400295506947361 7133851596300221630210521)
              ·
                refine ⟨5350388697225166222657891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7133851596300221630210521 5350388697225166222657891)
                ·
                  refine ⟨8025583045837749333986837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5350388697225166222657891 8025583045837749333986837)
                  ·
                    refine ⟨376199205273644500030633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8025583045837749333986837 376199205273644500030633)
                    ·
                      refine ⟨282149403955233375022975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 376199205273644500030633 282149403955233375022975)
                      ·
                        rfl

theorem cell23_549484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 6, 2].length) (baseStart_549484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549484 prefixEnd_549484 := by exact prefixLift 549484
  have htrace : WordTrace (prefixWord ++ tailWord_549484) baseStart_549484 baseEnd_549484 := by
    simpa [prefixWord, tailWord_549484, baseEnd_549484] using wordTrace_append hprefix tailTrace_549484
  have hstable : (prefixWord ++ tailWord_549484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549484).length < 2 ^ (prefixWord ++ tailWord_549484).sum := by decide
  have hdescent : baseEnd_549484 < baseStart_549484 := by decide
  rcases family_descends (prefixWord ++ tailWord_549484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549501 : List Nat := [1, 4, 1, 1, 5, 1, 1, 2, 2, 1, 4]
def baseStart_549501 : Nat := 118140960795 + 549501 * 2 ^ 59
def prefixEnd_549501 : Nat := 4983230072969 + 3 ^ 40 * 549501 * 2
def baseEnd_549501 : Nat := 282158133126359808510397

theorem tailTrace_549501 : CollatzResearch.WordTrace tailWord_549501 prefixEnd_549501 282158133126359808510397 := by
  unfold tailWord_549501
  simp only [CollatzResearch.WordTrace]
  refine ⟨20041947982259199144344357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13361298654839466096229571 20041947982259199144344357)
  ·
    refine ⟨3757865246673599839564567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20041947982259199144344357 3757865246673599839564567)
    ·
      refine ⟨5636797870010399759346851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3757865246673599839564567 5636797870010399759346851)
      ·
        refine ⟨8455196805015599639020277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5636797870010399759346851 8455196805015599639020277)
        ·
          refine ⟨792674700470212466158151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8455196805015599639020277 792674700470212466158151)
          ·
            refine ⟨1189012050705318699237227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 792674700470212466158151 1189012050705318699237227)
            ·
              refine ⟨1783518076057978048855841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1189012050705318699237227 1783518076057978048855841)
              ·
                refine ⟨1337638557043483536641881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1783518076057978048855841 1337638557043483536641881)
                ·
                  refine ⟨1003228917782612652481411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1337638557043483536641881 1003228917782612652481411)
                  ·
                    refine ⟨1504843376673918978722117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1003228917782612652481411 1504843376673918978722117)
                    ·
                      refine ⟨282158133126359808510397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1504843376673918978722117 282158133126359808510397)
                      ·
                        rfl

theorem cell23_549501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_549501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549501 prefixEnd_549501 := by exact prefixLift 549501
  have htrace : WordTrace (prefixWord ++ tailWord_549501) baseStart_549501 baseEnd_549501 := by
    simpa [prefixWord, tailWord_549501, baseEnd_549501] using wordTrace_append hprefix tailTrace_549501
  have hstable : (prefixWord ++ tailWord_549501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549501).length < 2 ^ (prefixWord ++ tailWord_549501).sum := by decide
  have hdescent : baseEnd_549501 < baseStart_549501 := by decide
  rcases family_descends (prefixWord ++ tailWord_549501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549504 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 3]
def baseStart_549504 : Nat := 118140960795 + 549504 * 2 ^ 59
def prefixEnd_549504 : Nat := 4983230072969 + 3 ^ 40 * 549504 * 2
def baseEnd_549504 : Nat := 282159673568323296772883

theorem tailTrace_549504 : CollatzResearch.WordTrace tailWord_549504 prefixEnd_549504 282159673568323296772883 := by
  unfold tailWord_549504
  simp only [CollatzResearch.WordTrace]
  refine ⟨10021028700624165328351783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13361371600832220437802377 10021028700624165328351783)
  ·
    refine ⟨15031543050936247992527675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10021028700624165328351783 15031543050936247992527675)
    ·
      refine ⟨22547314576404371988791513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15031543050936247992527675 22547314576404371988791513)
      ·
        refine ⟨16910485932303278991593635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22547314576404371988791513 16910485932303278991593635)
        ·
          refine ⟨25365728898454918487390453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16910485932303278991593635 25365728898454918487390453)
          ·
            refine ⟨2378037084230148608192855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25365728898454918487390453 2378037084230148608192855)
            ·
              refine ⟨3567055626345222912289283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2378037084230148608192855 3567055626345222912289283)
              ·
                refine ⟨5350583439517834368433925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3567055626345222912289283 5350583439517834368433925)
                ·
                  refine ⟨1003234394909593944081361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5350583439517834368433925 1003234394909593944081361)
                  ·
                    refine ⟨752425796182195458061021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1003234394909593944081361 752425796182195458061021)
                    ·
                      refine ⟨282159673568323296772883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 752425796182195458061021 282159673568323296772883)
                      ·
                        rfl

theorem cell23_549504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 3].length) (baseStart_549504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549504 prefixEnd_549504 := by exact prefixLift 549504
  have htrace : WordTrace (prefixWord ++ tailWord_549504) baseStart_549504 baseEnd_549504 := by
    simpa [prefixWord, tailWord_549504, baseEnd_549504] using wordTrace_append hprefix tailTrace_549504
  have hstable : (prefixWord ++ tailWord_549504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549504).length < 2 ^ (prefixWord ++ tailWord_549504).sum := by decide
  have hdescent : baseEnd_549504 < baseStart_549504 := by decide
  rcases family_descends (prefixWord ++ tailWord_549504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549507 : List Nat := [1, 1, 1, 3, 3, 1, 4, 1, 8]
def baseStart_549507 : Nat := 118140960795 + 549507 * 2 ^ 59
def prefixEnd_549507 : Nat := 4983230072969 + 3 ^ 40 * 549507 * 2
def baseEnd_549507 : Nat := 31351246001142976115041

theorem tailTrace_549507 : CollatzResearch.WordTrace tailWord_549507 prefixEnd_549507 31351246001142976115041 := by
  unfold tailWord_549507
  simp only [CollatzResearch.WordTrace]
  refine ⟨20042166820237462169062775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13361444546824974779375183 20042166820237462169062775)
  ·
    refine ⟨30063250230356193253594163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20042166820237462169062775 30063250230356193253594163)
    ·
      refine ⟨45094875345534289880391245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30063250230356193253594163 45094875345534289880391245)
      ·
        refine ⟨16910578254575358705146717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45094875345534289880391245 16910578254575358705146717)
        ·
          refine ⟨6341466845465759514430019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16910578254575358705146717 6341466845465759514430019)
          ·
            refine ⟨9512200268198639271645029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6341466845465759514430019 9512200268198639271645029)
            ·
              refine ⟨1783537550287244863433443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9512200268198639271645029 1783537550287244863433443)
              ·
                refine ⟨2675306325430867295150165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1783537550287244863433443 2675306325430867295150165)
                ·
                  refine ⟨31351246001142976115041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2675306325430867295150165 31351246001142976115041)
                  ·
                    rfl

theorem cell23_549507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 8].length) (baseStart_549507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549507 prefixEnd_549507 := by exact prefixLift 549507
  have htrace : WordTrace (prefixWord ++ tailWord_549507) baseStart_549507 baseEnd_549507 := by
    simpa [prefixWord, tailWord_549507, baseEnd_549507] using wordTrace_append hprefix tailTrace_549507
  have hstable : (prefixWord ++ tailWord_549507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549507).length < 2 ^ (prefixWord ++ tailWord_549507).sum := by decide
  have hdescent : baseEnd_549507 < baseStart_549507 := by decide
  rcases family_descends (prefixWord ++ tailWord_549507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549608 : List Nat := [2, 1, 4, 1, 4, 1, 1, 3, 1, 1, 4]
def baseStart_549608 : Nat := 118140960795 + 549608 * 2 ^ 59
def prefixEnd_549608 : Nat := 4983230072969 + 3 ^ 40 * 549608 * 2
def baseEnd_549608 : Nat := 282213075556390889872405

theorem tailTrace_549608 : CollatzResearch.WordTrace tailWord_549608 prefixEnd_549608 282213075556390889872405 := by
  unfold tailWord_549608
  simp only [CollatzResearch.WordTrace]
  refine ⟨10022925296435778209244739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13363900395247704278992985 10022925296435778209244739)
  ·
    refine ⟨15034387944653667313867109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10022925296435778209244739 15034387944653667313867109)
    ·
      refine ⟨2818947739622562621350083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15034387944653667313867109 2818947739622562621350083)
      ·
        refine ⟨4228421609433843932025125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2818947739622562621350083 4228421609433843932025125)
        ·
          refine ⟨792829051768845737254711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4228421609433843932025125 792829051768845737254711)
          ·
            refine ⟨1189243577653268605882067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 792829051768845737254711 1189243577653268605882067)
            ·
              refine ⟨1783865366479902908823101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1189243577653268605882067 1783865366479902908823101)
              ·
                refine ⟨668949512429963590808663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1783865366479902908823101 668949512429963590808663)
                ·
                  refine ⟨1003424268644945386212995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 668949512429963590808663 1003424268644945386212995)
                  ·
                    refine ⟨1505136402967418079319493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1003424268644945386212995 1505136402967418079319493)
                    ·
                      refine ⟨282213075556390889872405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1505136402967418079319493 282213075556390889872405)
                      ·
                        rfl

theorem cell23_549608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_549608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549608 prefixEnd_549608 := by exact prefixLift 549608
  have htrace : WordTrace (prefixWord ++ tailWord_549608) baseStart_549608 baseEnd_549608 := by
    simpa [prefixWord, tailWord_549608, baseEnd_549608] using wordTrace_append hprefix tailTrace_549608
  have hstable : (prefixWord ++ tailWord_549608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549608).length < 2 ^ (prefixWord ++ tailWord_549608).sum := by decide
  have hdescent : baseEnd_549608 < baseStart_549608 := by decide
  rcases family_descends (prefixWord ++ tailWord_549608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549614 : List Nat := [4, 1, 2, 1, 1, 4, 10]
def baseStart_549614 : Nat := 118140960795 + 549614 * 2 ^ 59
def prefixEnd_549614 : Nat := 4983230072969 + 3 ^ 40 * 549614 * 2
def baseEnd_549614 : Nat := 3484150079510097116017

theorem tailTrace_549614 : CollatzResearch.WordTrace tailWord_549614 prefixEnd_549614 3484150079510097116017 := by
  unfold tailWord_549614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2505758678856227430400987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13364046287233212962138597 2505758678856227430400987)
  ·
    refine ⟨3758638018284341145601481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2505758678856227430400987 3758638018284341145601481)
    ·
      refine ⟨2818978513713255859201111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3758638018284341145601481 2818978513713255859201111)
      ·
        refine ⟨4228467770569883788801667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2818978513713255859201111 4228467770569883788801667)
        ·
          refine ⟨6342701655854825683202501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4228467770569883788801667 6342701655854825683202501)
          ·
            refine ⟨1189256560472779815600469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6342701655854825683202501 1189256560472779815600469)
            ·
              refine ⟨3484150079510097116017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1189256560472779815600469 3484150079510097116017)
              ·
                rfl

theorem cell23_549614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 10].length) (baseStart_549614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549614 prefixEnd_549614 := by exact prefixLift 549614
  have htrace : WordTrace (prefixWord ++ tailWord_549614) baseStart_549614 baseEnd_549614 := by
    simpa [prefixWord, tailWord_549614, baseEnd_549614] using wordTrace_append hprefix tailTrace_549614
  have hstable : (prefixWord ++ tailWord_549614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549614).length < 2 ^ (prefixWord ++ tailWord_549614).sum := by decide
  have hdescent : baseEnd_549614 < baseStart_549614 := by decide
  rcases family_descends (prefixWord ++ tailWord_549614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549618 : List Nat := [3, 2, 1, 3, 1, 2, 3, 2, 2, 4]
def baseStart_549618 : Nat := 118140960795 + 549618 * 2 ^ 59
def prefixEnd_549618 : Nat := 4983230072969 + 3 ^ 40 * 549618 * 2
def baseEnd_549618 : Nat := 94072736787645283582453

theorem tailTrace_549618 : CollatzResearch.WordTrace tailWord_549618 prefixEnd_549618 94072736787645283582453 := by
  unfold tailWord_549618
  simp only [CollatzResearch.WordTrace]
  refine ⟨5011553830708832031588377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13364143548556885417569005 5011553830708832031588377)
  ·
    refine ⟨3758665373031624023691283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5011553830708832031588377 3758665373031624023691283)
    ·
      refine ⟨5637998059547436035536925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3758665373031624023691283 5637998059547436035536925)
      ·
        refine ⟨2114249272330288513326347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5637998059547436035536925 2114249272330288513326347)
        ·
          refine ⟨3171373908495432769989521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2114249272330288513326347 3171373908495432769989521)
          ·
            refine ⟨2378530431371574577492141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3171373908495432769989521 2378530431371574577492141)
            ·
              refine ⟨891948911764340466559553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2378530431371574577492141 891948911764340466559553)
              ·
                refine ⟨668961683823255349919665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 891948911764340466559553 668961683823255349919665)
                ·
                  refine ⟨501721262867441512439749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 668961683823255349919665 501721262867441512439749)
                  ·
                    refine ⟨94072736787645283582453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 501721262867441512439749 94072736787645283582453)
                    ·
                      rfl

theorem cell23_549618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_549618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549618 prefixEnd_549618 := by exact prefixLift 549618
  have htrace : WordTrace (prefixWord ++ tailWord_549618) baseStart_549618 baseEnd_549618 := by
    simpa [prefixWord, tailWord_549618, baseEnd_549618] using wordTrace_append hprefix tailTrace_549618
  have hstable : (prefixWord ++ tailWord_549618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549618).length < 2 ^ (prefixWord ++ tailWord_549618).sum := by decide
  have hdescent : baseEnd_549618 < baseStart_549618 := by decide
  rcases family_descends (prefixWord ++ tailWord_549618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549641 : List Nat := [1, 2, 1, 1, 3, 2, 5, 1, 1, 3, 3]
def baseStart_549641 : Nat := 118140960795 + 549641 * 2 ^ 59
def prefixEnd_549641 : Nat := 4983230072969 + 3 ^ 40 * 549641 * 2
def baseEnd_549641 : Nat := 282230020417989260759753

theorem tailTrace_549641 : CollatzResearch.WordTrace tailWord_549641 prefixEnd_549641 282230020417989260759753 := by
  unfold tailWord_549641
  simp only [CollatzResearch.WordTrace]
  refine ⟨20047054201752003054440777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13364702801168002036293851 20047054201752003054440777)
  ·
    refine ⟨15035290651314002290830583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20047054201752003054440777 15035290651314002290830583)
    ·
      refine ⟨22552935976971003436245875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15035290651314002290830583 22552935976971003436245875)
      ·
        refine ⟨33829403965456505154368813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22552935976971003436245875 33829403965456505154368813)
        ·
          refine ⟨12686026487046189432888305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33829403965456505154368813 12686026487046189432888305)
          ·
            refine ⟨9514519865284642074666229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12686026487046189432888305 9514519865284642074666229)
            ·
              refine ⟨891986237370435194499959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9514519865284642074666229 891986237370435194499959)
              ·
                refine ⟨1337979356055652791749939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 891986237370435194499959 1337979356055652791749939)
                ·
                  refine ⟨2006969034083479187624909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1337979356055652791749939 2006969034083479187624909)
                  ·
                    refine ⟨752613387781304695359341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2006969034083479187624909 752613387781304695359341)
                    ·
                      refine ⟨282230020417989260759753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 752613387781304695359341 282230020417989260759753)
                      ·
                        rfl

theorem cell23_549641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 3, 3].length) (baseStart_549641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549641 prefixEnd_549641 := by exact prefixLift 549641
  have htrace : WordTrace (prefixWord ++ tailWord_549641) baseStart_549641 baseEnd_549641 := by
    simpa [prefixWord, tailWord_549641, baseEnd_549641] using wordTrace_append hprefix tailTrace_549641
  have hstable : (prefixWord ++ tailWord_549641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549641).length < 2 ^ (prefixWord ++ tailWord_549641).sum := by decide
  have hdescent : baseEnd_549641 < baseStart_549641 := by decide
  rcases family_descends (prefixWord ++ tailWord_549641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549704 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 9]
def baseStart_549704 : Nat := 118140960795 + 549704 * 2 ^ 59
def prefixEnd_549704 : Nat := 4983230072969 + 3 ^ 40 * 549704 * 2
def baseEnd_549704 : Nat := 31362485522135834919107

theorem tailTrace_549704 : CollatzResearch.WordTrace tailWord_549704 prefixEnd_549704 31362485522135834919107 := by
  unfold tailWord_549704
  simp only [CollatzResearch.WordTrace]
  refine ⟨10024676000261882406992083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13366234667015843209322777 10024676000261882406992083)
  ·
    refine ⟨15037014000392823610488125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10024676000261882406992083 15037014000392823610488125)
    ·
      refine ⟨5638880250147308853933047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15037014000392823610488125 5638880250147308853933047)
      ·
        refine ⟨8458320375220963280899571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5638880250147308853933047 8458320375220963280899571)
        ·
          refine ⟨12687480562831444921349357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8458320375220963280899571 12687480562831444921349357)
          ·
            refine ⟨4757805211061791845506009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12687480562831444921349357 4757805211061791845506009)
            ·
              refine ⟨3568353908296343884129507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4757805211061791845506009 3568353908296343884129507)
              ·
                refine ⟨5352530862444515826194261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3568353908296343884129507 5352530862444515826194261)
                ·
                  refine ⟨31362485522135834919107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5352530862444515826194261 31362485522135834919107)
                  ·
                    rfl

theorem cell23_549704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 9].length) (baseStart_549704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549704 prefixEnd_549704 := by exact prefixLift 549704
  have htrace : WordTrace (prefixWord ++ tailWord_549704) baseStart_549704 baseEnd_549704 := by
    simpa [prefixWord, tailWord_549704, baseEnd_549704] using wordTrace_append hprefix tailTrace_549704
  have hstable : (prefixWord ++ tailWord_549704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549704).length < 2 ^ (prefixWord ++ tailWord_549704).sum := by decide
  have hdescent : baseEnd_549704 < baseStart_549704 := by decide
  rcases family_descends (prefixWord ++ tailWord_549704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549732 : List Nat := [2, 3, 1, 1, 4, 2, 2, 2, 2, 2, 2]
def baseStart_549732 : Nat := 118140960795 + 549732 * 2 ^ 59
def prefixEnd_549732 : Nat := 4983230072969 + 3 ^ 40 * 549732 * 2
def baseEnd_549732 : Nat := 282276747157548404721835

theorem tailTrace_549732 : CollatzResearch.WordTrace tailWord_549732 prefixEnd_549732 282276747157548404721835 := by
  unfold tailWord_549732
  simp only [CollatzResearch.WordTrace]
  refine ⟨10025186622211162798001725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13366915496281550397335633 10025186622211162798001725)
  ·
    refine ⟨3759444983329186049250647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10025186622211162798001725 3759444983329186049250647)
    ·
      refine ⟨5639167474993779073875971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3759444983329186049250647 5639167474993779073875971)
      ·
        refine ⟨8458751212490668610813957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5639167474993779073875971 8458751212490668610813957)
        ·
          refine ⟨1586015852342000364527617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8458751212490668610813957 1586015852342000364527617)
          ·
            refine ⟨1189511889256500273395713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1586015852342000364527617 1189511889256500273395713)
            ·
              refine ⟨892133916942375205046785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1189511889256500273395713 892133916942375205046785)
              ·
                refine ⟨669100437706781403785089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 892133916942375205046785 669100437706781403785089)
                ·
                  refine ⟨501825328280086052838817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 669100437706781403785089 501825328280086052838817)
                  ·
                    refine ⟨376368996210064539629113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 501825328280086052838817 376368996210064539629113)
                    ·
                      refine ⟨282276747157548404721835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 376368996210064539629113 282276747157548404721835)
                      ·
                        rfl

theorem cell23_549732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 2, 2, 2].length) (baseStart_549732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549732 prefixEnd_549732 := by exact prefixLift 549732
  have htrace : WordTrace (prefixWord ++ tailWord_549732) baseStart_549732 baseEnd_549732 := by
    simpa [prefixWord, tailWord_549732, baseEnd_549732] using wordTrace_append hprefix tailTrace_549732
  have hstable : (prefixWord ++ tailWord_549732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549732).length < 2 ^ (prefixWord ++ tailWord_549732).sum := by decide
  have hdescent : baseEnd_549732 < baseStart_549732 := by decide
  rcases family_descends (prefixWord ++ tailWord_549732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549768 : List Nat := [2, 1, 3, 3, 2, 1, 3, 1, 2, 5]
def baseStart_549768 : Nat := 118140960795 + 549768 * 2 ^ 59
def prefixEnd_549768 : Nat := 4983230072969 + 3 ^ 40 * 549768 * 2
def baseEnd_549768 : Nat := 94098410820370087957223

theorem tailTrace_549768 : CollatzResearch.WordTrace tailWord_549768 prefixEnd_549768 94098410820370087957223 := by
  unfold tailWord_549768
  simp only [CollatzResearch.WordTrace]
  refine ⟨10025843136145951872156979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13367790848194602496209305 10025843136145951872156979)
  ·
    refine ⟨15038764704218927808235469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10025843136145951872156979 15038764704218927808235469)
    ·
      refine ⟨5639536764082097928088301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15038764704218927808235469 5639536764082097928088301)
      ·
        refine ⟨2114826286530786723033113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5639536764082097928088301 2114826286530786723033113)
        ·
          refine ⟨1586119714898090042274835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2114826286530786723033113 1586119714898090042274835)
          ·
            refine ⟨2379179572347135063412253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1586119714898090042274835 2379179572347135063412253)
            ·
              refine ⟨892192339630175648779595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2379179572347135063412253 892192339630175648779595)
              ·
                refine ⟨1338288509445263473169393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 892192339630175648779595 1338288509445263473169393)
                ·
                  refine ⟨1003716382083947604877045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1338288509445263473169393 1003716382083947604877045)
                  ·
                    refine ⟨94098410820370087957223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1003716382083947604877045 94098410820370087957223)
                    ·
                      rfl

theorem cell23_549768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_549768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549768 prefixEnd_549768 := by exact prefixLift 549768
  have htrace : WordTrace (prefixWord ++ tailWord_549768) baseStart_549768 baseEnd_549768 := by
    simpa [prefixWord, tailWord_549768, baseEnd_549768] using wordTrace_append hprefix tailTrace_549768
  have hstable : (prefixWord ++ tailWord_549768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549768).length < 2 ^ (prefixWord ++ tailWord_549768).sum := by decide
  have hdescent : baseEnd_549768 < baseStart_549768 := by decide
  rcases family_descends (prefixWord ++ tailWord_549768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549782 : List Nat := [5, 3, 1, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_549782 : Nat := 118140960795 + 549782 * 2 ^ 59
def prefixEnd_549782 : Nat := 4983230072969 + 3 ^ 40 * 549782 * 2
def baseEnd_549782 : Nat := 282302421190273209096605

theorem tailTrace_549782 : CollatzResearch.WordTrace tailWord_549782 prefixEnd_549782 282302421190273209096605 := by
  unfold tailWord_549782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1253262305890074008457725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13368131262827456090215733 1253262305890074008457725)
  ·
    refine ⟨469973364708777753171647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1253262305890074008457725 469973364708777753171647)
    ·
      refine ⟨704960047063166629757471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 469973364708777753171647 704960047063166629757471)
      ·
        refine ⟨1057440070594749944636207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 704960047063166629757471 1057440070594749944636207)
        ·
          refine ⟨1586160105892124916954311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1057440070594749944636207 1586160105892124916954311)
          ·
            refine ⟨2379240158838187375431467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1586160105892124916954311 2379240158838187375431467)
            ·
              refine ⟨3568860238257281063147201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2379240158838187375431467 3568860238257281063147201)
              ·
                refine ⟨2676645178692960797360401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3568860238257281063147201 2676645178692960797360401)
                ·
                  refine ⟨2007483884019720598020301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2676645178692960797360401 2007483884019720598020301)
                  ·
                    refine ⟨752806456507395224257613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2007483884019720598020301 752806456507395224257613)
                    ·
                      refine ⟨282302421190273209096605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 752806456507395224257613 282302421190273209096605)
                      ·
                        rfl

theorem cell23_549782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_549782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549782 prefixEnd_549782 := by exact prefixLift 549782
  have htrace : WordTrace (prefixWord ++ tailWord_549782) baseStart_549782 baseEnd_549782 := by
    simpa [prefixWord, tailWord_549782, baseEnd_549782] using wordTrace_append hprefix tailTrace_549782
  have hstable : (prefixWord ++ tailWord_549782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549782).length < 2 ^ (prefixWord ++ tailWord_549782).sum := by decide
  have hdescent : baseEnd_549782 < baseStart_549782 := by decide
  rcases family_descends (prefixWord ++ tailWord_549782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549931 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 2, 7]
def baseStart_549931 : Nat := 118140960795 + 549931 * 2 ^ 59
def prefixEnd_549931 : Nat := 4983230072969 + 3 ^ 40 * 549931 * 2
def baseEnd_549931 : Nat := 94126309935931042044473

theorem tailTrace_549931 : CollatzResearch.WordTrace tailWord_549931 prefixEnd_549931 94126309935931042044473 := by
  unfold tailWord_549931
  simp only [CollatzResearch.WordTrace]
  refine ⟨20057631370701382582497647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13371754247134255054998431 20057631370701382582497647)
  ·
    refine ⟨30086447056052073873746471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20057631370701382582497647 30086447056052073873746471)
    ·
      refine ⟨45129670584078110810619707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30086447056052073873746471 45129670584078110810619707)
      ·
        refine ⟨67694505876117166215929561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45129670584078110810619707 67694505876117166215929561)
        ·
          refine ⟨50770879407087874661947171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67694505876117166215929561 50770879407087874661947171)
          ·
            refine ⟨76156319110631811992920757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50770879407087874661947171 76156319110631811992920757)
            ·
              refine ⟨7139654916621732374336321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76156319110631811992920757 7139654916621732374336321)
              ·
                refine ⟨5354741187466299280752241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7139654916621732374336321 5354741187466299280752241)
                ·
                  refine ⟨4016055890599724460564181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5354741187466299280752241 4016055890599724460564181)
                  ·
                    refine ⟨94126309935931042044473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4016055890599724460564181 94126309935931042044473)
                    ·
                      rfl

theorem cell23_549931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 7].length) (baseStart_549931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549931 prefixEnd_549931 := by exact prefixLift 549931
  have htrace : WordTrace (prefixWord ++ tailWord_549931) baseStart_549931 baseEnd_549931 := by
    simpa [prefixWord, tailWord_549931, baseEnd_549931] using wordTrace_append hprefix tailTrace_549931
  have hstable : (prefixWord ++ tailWord_549931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549931).length < 2 ^ (prefixWord ++ tailWord_549931).sum := by decide
  have hdescent : baseEnd_549931 < baseStart_549931 := by decide
  rcases family_descends (prefixWord ++ tailWord_549931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549945 : List Nat := [1, 2, 1, 5, 2, 1, 2, 2, 1, 3, 3]
def baseStart_549945 : Nat := 118140960795 + 549945 * 2 ^ 59
def prefixEnd_549945 : Nat := 4983230072969 + 3 ^ 40 * 549945 * 2
def baseEnd_549945 : Nat := 282386118536956071358355

theorem tailTrace_549945 : CollatzResearch.WordTrace tailWord_549945 prefixEnd_549945 282386118536956071358355 := by
  unfold tailWord_549945
  simp only [CollatzResearch.WordTrace]
  refine ⟨20058141992650662973507289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13372094661767108649004859 20058141992650662973507289)
  ·
    refine ⟨15043606494487997230130467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20058141992650662973507289 15043606494487997230130467)
    ·
      refine ⟨22565409741731995845195701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15043606494487997230130467 22565409741731995845195701)
      ·
        refine ⟨2115507163287374610487097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22565409741731995845195701 2115507163287374610487097)
        ·
          refine ⟨1586630372465530957865323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2115507163287374610487097 1586630372465530957865323)
          ·
            refine ⟨2379945558698296436797985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1586630372465530957865323 2379945558698296436797985)
            ·
              refine ⟨1784959169023722327598489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2379945558698296436797985 1784959169023722327598489)
              ·
                refine ⟨1338719376767791745698867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1784959169023722327598489 1338719376767791745698867)
                ·
                  refine ⟨2008079065151687618548301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1338719376767791745698867 2008079065151687618548301)
                  ·
                    refine ⟨753029649431882856955613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2008079065151687618548301 753029649431882856955613)
                    ·
                      refine ⟨282386118536956071358355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 753029649431882856955613 282386118536956071358355)
                      ·
                        rfl

theorem cell23_549945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_549945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549945 prefixEnd_549945 := by exact prefixLift 549945
  have htrace : WordTrace (prefixWord ++ tailWord_549945) baseStart_549945 baseEnd_549945 := by
    simpa [prefixWord, tailWord_549945, baseEnd_549945] using wordTrace_append hprefix tailTrace_549945
  have hstable : (prefixWord ++ tailWord_549945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549945).length < 2 ^ (prefixWord ++ tailWord_549945).sum := by decide
  have hdescent : baseEnd_549945 < baseStart_549945 := by decide
  rcases family_descends (prefixWord ++ tailWord_549945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549949 : List Nat := [1, 4, 1, 3, 1, 4, 2, 1, 1, 2, 3]
def baseStart_549949 : Nat := 118140960795 + 549949 * 2 ^ 59
def prefixEnd_549949 : Nat := 4983230072969 + 3 ^ 40 * 549949 * 2
def baseEnd_549949 : Nat := 282388172459574055708337

theorem tailTrace_549949 : CollatzResearch.WordTrace tailWord_549949 prefixEnd_549949 282388172459574055708337 := by
  unfold tailWord_549949
  simp only [CollatzResearch.WordTrace]
  refine ⟨20058287884636171656652901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13372191923090781104435267 20058287884636171656652901)
  ·
    refine ⟨3760928978369282185622419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20058287884636171656652901 3760928978369282185622419)
    ·
      refine ⟨5641393467553923278433629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3760928978369282185622419 5641393467553923278433629)
      ·
        refine ⟨2115522550332721229412611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5641393467553923278433629 2115522550332721229412611)
        ·
          refine ⟨3173283825499081844118917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2115522550332721229412611 3173283825499081844118917)
          ·
            refine ⟨594990717281077845772297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3173283825499081844118917 594990717281077845772297)
            ·
              refine ⟨446243037960808384329223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 594990717281077845772297 446243037960808384329223)
              ·
                refine ⟨669364556941212576493835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 446243037960808384329223 669364556941212576493835)
                ·
                  refine ⟨1004046835411818864740753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 669364556941212576493835 1004046835411818864740753)
                  ·
                    refine ⟨753035126558864148555565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1004046835411818864740753 753035126558864148555565)
                    ·
                      refine ⟨282388172459574055708337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 753035126558864148555565 282388172459574055708337)
                      ·
                        rfl

theorem cell23_549949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_549949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549949 prefixEnd_549949 := by exact prefixLift 549949
  have htrace : WordTrace (prefixWord ++ tailWord_549949) baseStart_549949 baseEnd_549949 := by
    simpa [prefixWord, tailWord_549949, baseEnd_549949] using wordTrace_append hprefix tailTrace_549949
  have hstable : (prefixWord ++ tailWord_549949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549949).length < 2 ^ (prefixWord ++ tailWord_549949).sum := by decide
  have hdescent : baseEnd_549949 < baseStart_549949 := by decide
  rcases family_descends (prefixWord ++ tailWord_549949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549962 : List Nat := [3, 1, 2, 1, 1, 2, 5, 2, 2, 1, 3]
def baseStart_549962 : Nat := 118140960795 + 549962 * 2 ^ 59
def prefixEnd_549962 : Nat := 4983230072969 + 3 ^ 40 * 549962 * 2
def baseEnd_549962 : Nat := 282394847708082504845777

theorem tailTrace_549962 : CollatzResearch.WordTrace tailWord_549962 prefixEnd_549962 282394847708082504845777 := by
  unfold tailWord_549962
  simp only [CollatzResearch.WordTrace]
  refine ⟨5014690508397268719219035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13372508022392716584584093 5014690508397268719219035)
  ·
    refine ⟨7522035762595903078828553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5014690508397268719219035 7522035762595903078828553)
    ·
      refine ⟨5641526821946927309121415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7522035762595903078828553 5641526821946927309121415)
      ·
        refine ⟨8462290232920390963682123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5641526821946927309121415 8462290232920390963682123)
        ·
          refine ⟨12693435349380586445523185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8462290232920390963682123 12693435349380586445523185)
          ·
            refine ⟨9520076512035439834142389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12693435349380586445523185 9520076512035439834142389)
            ·
              refine ⟨892507173003322484450849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9520076512035439834142389 892507173003322484450849)
              ·
                refine ⟨669380379752491863338137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 892507173003322484450849 669380379752491863338137)
                ·
                  refine ⟨502035284814368897503603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 669380379752491863338137 502035284814368897503603)
                  ·
                    refine ⟨753052927221553346255405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 502035284814368897503603 753052927221553346255405)
                    ·
                      refine ⟨282394847708082504845777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 753052927221553346255405 282394847708082504845777)
                      ·
                        rfl

theorem cell23_549962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_549962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549962 prefixEnd_549962 := by exact prefixLift 549962
  have htrace : WordTrace (prefixWord ++ tailWord_549962) baseStart_549962 baseEnd_549962 := by
    simpa [prefixWord, tailWord_549962, baseEnd_549962] using wordTrace_append hprefix tailTrace_549962
  have hstable : (prefixWord ++ tailWord_549962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549962).length < 2 ^ (prefixWord ++ tailWord_549962).sum := by decide
  have hdescent : baseEnd_549962 < baseStart_549962 := by decide
  rcases family_descends (prefixWord ++ tailWord_549962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549988 : List Nat := [2, 3, 1, 1, 2, 1, 1, 4, 2, 1, 5]
def baseStart_549988 : Nat := 118140960795 + 549988 * 2 ^ 59
def prefixEnd_549988 : Nat := 4983230072969 + 3 ^ 40 * 549988 * 2
def baseEnd_549988 : Nat := 282408198205099403120657

theorem tailTrace_549988 : CollatzResearch.WordTrace tailWord_549988 prefixEnd_549988 282408198205099403120657 := by
  unfold tailWord_549988
  simp only [CollatzResearch.WordTrace]
  refine ⟨10029855165747440658661309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13373140220996587544881745 10029855165747440658661309)
  ·
    refine ⟨3761195687155290246997991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10029855165747440658661309 3761195687155290246997991)
    ·
      refine ⟨5641793530732935370496987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3761195687155290246997991 5641793530732935370496987)
      ·
        refine ⟨8462690296099403055745481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5641793530732935370496987 8462690296099403055745481)
        ·
          refine ⟨6347017722074552291809111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8462690296099403055745481 6347017722074552291809111)
          ·
            refine ⟨9520526583111828437713667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6347017722074552291809111 9520526583111828437713667)
            ·
              refine ⟨14280789874667742656570501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9520526583111828437713667 14280789874667742656570501)
              ·
                refine ⟨2677648101500201748106969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14280789874667742656570501 2677648101500201748106969)
                ·
                  refine ⟨2008236076125151311080227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2677648101500201748106969 2008236076125151311080227)
                  ·
                    refine ⟨3012354114187726966620341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2008236076125151311080227 3012354114187726966620341)
                    ·
                      refine ⟨282408198205099403120657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3012354114187726966620341 282408198205099403120657)
                      ·
                        rfl

theorem cell23_549988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_549988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_549988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_549988 prefixEnd_549988 := by exact prefixLift 549988
  have htrace : WordTrace (prefixWord ++ tailWord_549988) baseStart_549988 baseEnd_549988 := by
    simpa [prefixWord, tailWord_549988, baseEnd_549988] using wordTrace_append hprefix tailTrace_549988
  have hstable : (prefixWord ++ tailWord_549988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549988).length < 2 ^ (prefixWord ++ tailWord_549988).sum := by decide
  have hdescent : baseEnd_549988 < baseStart_549988 := by decide
  rcases family_descends (prefixWord ++ tailWord_549988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550002 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 6, 2, 2]
def baseStart_550002 : Nat := 118140960795 + 550002 * 2 ^ 59
def prefixEnd_550002 : Nat := 4983230072969 + 3 ^ 40 * 550002 * 2
def baseEnd_550002 : Nat := 282415386934262348345593

theorem tailTrace_550002 : CollatzResearch.WordTrace tailWord_550002 prefixEnd_550002 282415386934262348345593 := by
  unfold tailWord_550002
  simp only [CollatzResearch.WordTrace]
  refine ⟨5015055238361040427083065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13373480635629441138888173 5015055238361040427083065)
  ·
    refine ⟨3761291428770780320312299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5015055238361040427083065 3761291428770780320312299)
    ·
      refine ⟨5641937143156170480468449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3761291428770780320312299 5641937143156170480468449)
      ·
        refine ⟨4231452857367127860351337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5641937143156170480468449 4231452857367127860351337)
        ·
          refine ⟨3173589643025345895263503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4231452857367127860351337 3173589643025345895263503)
          ·
            refine ⟨4760384464538018842895255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3173589643025345895263503 4760384464538018842895255)
            ·
              refine ⟨7140576696807028264342883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4760384464538018842895255 7140576696807028264342883)
              ·
                refine ⟨10710865045210542396514325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7140576696807028264342883 10710865045210542396514325)
                ·
                  refine ⟨502071798994244174836609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10710865045210542396514325 502071798994244174836609)
                  ·
                    refine ⟨376553849245683131127457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 502071798994244174836609 376553849245683131127457)
                    ·
                      refine ⟨282415386934262348345593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 376553849245683131127457 282415386934262348345593)
                      ·
                        rfl

theorem cell23_550002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_550002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550002 prefixEnd_550002 := by exact prefixLift 550002
  have htrace : WordTrace (prefixWord ++ tailWord_550002) baseStart_550002 baseEnd_550002 := by
    simpa [prefixWord, tailWord_550002, baseEnd_550002] using wordTrace_append hprefix tailTrace_550002
  have hstable : (prefixWord ++ tailWord_550002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550002).length < 2 ^ (prefixWord ++ tailWord_550002).sum := by decide
  have hdescent : baseEnd_550002 < baseStart_550002 := by decide
  rcases family_descends (prefixWord ++ tailWord_550002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550025 : List Nat := [1, 2, 1, 1, 4, 5, 1, 1, 7]
def baseStart_550025 : Nat := 118140960795 + 550025 * 2 ^ 59
def prefixEnd_550025 : Nat := 4983230072969 + 3 ^ 40 * 550025 * 2
def baseEnd_550025 : Nat := 31380799665479528706443

theorem tailTrace_550025 : CollatzResearch.WordTrace tailWord_550025 prefixEnd_550025 31380799665479528706443 := by
  unfold tailWord_550025
  simp only [CollatzResearch.WordTrace]
  refine ⟨20061059832360836636419529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13374039888240557757613019 20061059832360836636419529)
  ·
    refine ⟨15045794874270627477314647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20061059832360836636419529 15045794874270627477314647)
    ·
      refine ⟨22568692311405941215971971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15045794874270627477314647 22568692311405941215971971)
      ·
        refine ⟨33853038467108911823957957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22568692311405941215971971 33853038467108911823957957)
        ·
          refine ⟨6347444712582920966992117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33853038467108911823957957 6347444712582920966992117)
          ·
            refine ⟨595072941804648840655511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6347444712582920966992117 595072941804648840655511)
            ·
              refine ⟨892609412706973260983267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595072941804648840655511 892609412706973260983267)
              ·
                refine ⟨1338914119060459891474901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 892609412706973260983267 1338914119060459891474901)
                ·
                  refine ⟨31380799665479528706443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1338914119060459891474901 31380799665479528706443)
                  ·
                    rfl

theorem cell23_550025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 7].length) (baseStart_550025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550025 prefixEnd_550025 := by exact prefixLift 550025
  have htrace : WordTrace (prefixWord ++ tailWord_550025) baseStart_550025 baseEnd_550025 := by
    simpa [prefixWord, tailWord_550025, baseEnd_550025] using wordTrace_append hprefix tailTrace_550025
  have hstable : (prefixWord ++ tailWord_550025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550025).length < 2 ^ (prefixWord ++ tailWord_550025).sum := by decide
  have hdescent : baseEnd_550025 < baseStart_550025 := by decide
  rcases family_descends (prefixWord ++ tailWord_550025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550048 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 7]
def baseStart_550048 : Nat := 118140960795 + 550048 * 2 ^ 59
def prefixEnd_550048 : Nat := 4983230072969 + 3 ^ 40 * 550048 * 2
def baseEnd_550048 : Nat := 282439007044369168370381

theorem tailTrace_550048 : CollatzResearch.WordTrace tailWord_550048 prefixEnd_550048 282439007044369168370381 := by
  unfold tailWord_550048
  simp only [CollatzResearch.WordTrace]
  refine ⟨10030949355638755782253399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13374599140851674376337865 10030949355638755782253399)
  ·
    refine ⟨15046424033458133673380099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10030949355638755782253399 15046424033458133673380099)
    ·
      refine ⟨22569636050187200510070149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15046424033458133673380099 22569636050187200510070149)
      ·
        refine ⟨4231806759410100095638153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22569636050187200510070149 4231806759410100095638153)
        ·
          refine ⟨3173855069557575071728615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4231806759410100095638153 3173855069557575071728615)
          ·
            refine ⟨4760782604336362607592923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3173855069557575071728615 4760782604336362607592923)
            ·
              refine ⟨7141173906504543911389385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4760782604336362607592923 7141173906504543911389385)
              ·
                refine ⟨5355880429878407933542039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7141173906504543911389385 5355880429878407933542039)
                ·
                  refine ⟨8033820644817611900313059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5355880429878407933542039 8033820644817611900313059)
                  ·
                    refine ⟨12050730967226417850469589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8033820644817611900313059 12050730967226417850469589)
                    ·
                      refine ⟨282439007044369168370381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 12050730967226417850469589 282439007044369168370381)
                      ·
                        rfl

theorem cell23_550048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_550048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550048 prefixEnd_550048 := by exact prefixLift 550048
  have htrace : WordTrace (prefixWord ++ tailWord_550048) baseStart_550048 baseEnd_550048 := by
    simpa [prefixWord, tailWord_550048, baseEnd_550048] using wordTrace_append hprefix tailTrace_550048
  have hstable : (prefixWord ++ tailWord_550048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550048).length < 2 ^ (prefixWord ++ tailWord_550048).sum := by decide
  have hdescent : baseEnd_550048 < baseStart_550048 := by decide
  rcases family_descends (prefixWord ++ tailWord_550048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550065 : List Nat := [1, 2, 2, 5, 1, 1, 1, 2, 1, 2, 5]
def baseStart_550065 : Nat := 118140960795 + 550065 * 2 ^ 59
def prefixEnd_550065 : Nat := 4983230072969 + 3 ^ 40 * 550065 * 2
def baseEnd_550065 : Nat := 282447736215495601857803

theorem tailTrace_550065 : CollatzResearch.WordTrace tailWord_550065 prefixEnd_550065 282447736215495601857803 := by
  unfold tailWord_550065
  simp only [CollatzResearch.WordTrace]
  refine ⟨20062518752215923467875649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13375012501477282311917099 20062518752215923467875649)
  ·
    refine ⟨15046889064161942600906737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20062518752215923467875649 15046889064161942600906737)
    ·
      refine ⟨11285166798121456950680053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15046889064161942600906737 11285166798121456950680053)
      ·
        refine ⟨1057984387323886589126255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11285166798121456950680053 1057984387323886589126255)
        ·
          refine ⟨1586976580985829883689383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1057984387323886589126255 1586976580985829883689383)
          ·
            refine ⟨2380464871478744825534075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1586976580985829883689383 2380464871478744825534075)
            ·
              refine ⟨3570697307218117238301113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2380464871478744825534075 3570697307218117238301113)
              ·
                refine ⟨2678022980413587928725835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3570697307218117238301113 2678022980413587928725835)
                ·
                  refine ⟨4017034470620381893088753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2678022980413587928725835 4017034470620381893088753)
                  ·
                    refine ⟨3012775852965286419816565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4017034470620381893088753 3012775852965286419816565)
                    ·
                      refine ⟨282447736215495601857803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3012775852965286419816565 282447736215495601857803)
                      ·
                        rfl

theorem cell23_550065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_550065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550065 prefixEnd_550065 := by exact prefixLift 550065
  have htrace : WordTrace (prefixWord ++ tailWord_550065) baseStart_550065 baseEnd_550065 := by
    simpa [prefixWord, tailWord_550065, baseEnd_550065] using wordTrace_append hprefix tailTrace_550065
  have hstable : (prefixWord ++ tailWord_550065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550065).length < 2 ^ (prefixWord ++ tailWord_550065).sum := by decide
  have hdescent : baseEnd_550065 < baseStart_550065 := by decide
  rcases family_descends (prefixWord ++ tailWord_550065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550070 : List Nat := [5, 1, 3, 2, 1, 1, 2, 2, 2, 2, 2]
def baseStart_550070 : Nat := 118140960795 + 550070 * 2 ^ 59
def prefixEnd_550070 : Nat := 4983230072969 + 3 ^ 40 * 550070 * 2
def baseEnd_550070 : Nat := 282450303618768082295281

theorem tailTrace_550070 : CollatzResearch.WordTrace tailWord_550070 prefixEnd_550070 282450303618768082295281 := by
  unfold tailWord_550070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1253918819824863082612979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13375134078131872881205109 1253918819824863082612979)
  ·
    refine ⟨1880878229737294623919469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1253918819824863082612979 1880878229737294623919469)
    ·
      refine ⟨705329336151485483969801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1880878229737294623919469 705329336151485483969801)
      ·
        refine ⟨528997002113614112977351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 705329336151485483969801 528997002113614112977351)
        ·
          refine ⟨793495503170421169466027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 528997002113614112977351 793495503170421169466027)
          ·
            refine ⟨1190243254755631754199041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 793495503170421169466027 1190243254755631754199041)
            ·
              refine ⟨892682441066723815649281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1190243254755631754199041 892682441066723815649281)
              ·
                refine ⟨669511830800042861736961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 892682441066723815649281 669511830800042861736961)
                ·
                  refine ⟨502133873100032146302721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 669511830800042861736961 502133873100032146302721)
                  ·
                    refine ⟨376600404825024109727041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 502133873100032146302721 376600404825024109727041)
                    ·
                      refine ⟨282450303618768082295281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 376600404825024109727041 282450303618768082295281)
                      ·
                        rfl

theorem cell23_550070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_550070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550070 prefixEnd_550070 := by exact prefixLift 550070
  have htrace : WordTrace (prefixWord ++ tailWord_550070) baseStart_550070 baseEnd_550070 := by
    simpa [prefixWord, tailWord_550070, baseEnd_550070] using wordTrace_append hprefix tailTrace_550070
  have hstable : (prefixWord ++ tailWord_550070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550070).length < 2 ^ (prefixWord ++ tailWord_550070).sum := by decide
  have hdescent : baseEnd_550070 < baseStart_550070 := by decide
  rcases family_descends (prefixWord ++ tailWord_550070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550085 : List Nat := [1, 3, 1, 1, 1, 1, 3, 5, 3, 4]
def baseStart_550085 : Nat := 118140960795 + 550085 * 2 ^ 59
def prefixEnd_550085 : Nat := 4983230072969 + 3 ^ 40 * 550085 * 2
def baseEnd_550085 : Nat := 94152668609528507869237

theorem tailTrace_550085 : CollatzResearch.WordTrace tailWord_550085 prefixEnd_550085 94152668609528507869237 := by
  unfold tailWord_550085
  simp only [CollatzResearch.WordTrace]
  refine ⟨20063248212143466883603709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13375498808095644589069139 20063248212143466883603709)
  ·
    refine ⟨7523718079553800081351391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20063248212143466883603709 7523718079553800081351391)
    ·
      refine ⟨11285577119330700122027087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7523718079553800081351391 11285577119330700122027087)
      ·
        refine ⟨16928365678996050183040631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11285577119330700122027087 16928365678996050183040631)
        ·
          refine ⟨25392548518494075274560947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16928365678996050183040631 25392548518494075274560947)
          ·
            refine ⟨38088822777741112911841421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25392548518494075274560947 38088822777741112911841421)
            ·
              refine ⟨14283308541652917341940533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38088822777741112911841421 14283308541652917341940533)
              ·
                refine ⟨1339060175779961000806925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14283308541652917341940533 1339060175779961000806925)
                ·
                  refine ⟨502147565917485375302597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1339060175779961000806925 502147565917485375302597)
                  ·
                    refine ⟨94152668609528507869237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 502147565917485375302597 94152668609528507869237)
                    ·
                      rfl

theorem cell23_550085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 3, 4].length) (baseStart_550085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550085 prefixEnd_550085 := by exact prefixLift 550085
  have htrace : WordTrace (prefixWord ++ tailWord_550085) baseStart_550085 baseEnd_550085 := by
    simpa [prefixWord, tailWord_550085, baseEnd_550085] using wordTrace_append hprefix tailTrace_550085
  have hstable : (prefixWord ++ tailWord_550085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550085).length < 2 ^ (prefixWord ++ tailWord_550085).sum := by decide
  have hdescent : baseEnd_550085 < baseStart_550085 := by decide
  rcases family_descends (prefixWord ++ tailWord_550085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550112 : List Nat := [2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 3]
def baseStart_550112 : Nat := 118140960795 + 550112 * 2 ^ 59
def prefixEnd_550112 : Nat := 4983230072969 + 3 ^ 40 * 550112 * 2
def baseEnd_550112 : Nat := 282471869806256917970087

theorem tailTrace_550112 : CollatzResearch.WordTrace tailWord_550112 prefixEnd_550112 282471869806256917970087 := by
  unfold tailWord_550112
  simp only [CollatzResearch.WordTrace]
  refine ⟨10032116491522825247418295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13376155322030433663224393 10032116491522825247418295)
  ·
    refine ⟨15048174737284237871127443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10032116491522825247418295 15048174737284237871127443)
    ·
      refine ⟨22572262105926356806691165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15048174737284237871127443 22572262105926356806691165)
      ·
        refine ⟨8464598289722383802509187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22572262105926356806691165 8464598289722383802509187)
        ·
          refine ⟨12696897434583575703763781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8464598289722383802509187 12696897434583575703763781)
          ·
            refine ⟨2380668268984420444455709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12696897434583575703763781 2380668268984420444455709)
            ·
              refine ⟨892750600869157666670891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2380668268984420444455709 892750600869157666670891)
              ·
                refine ⟨1339125901303736500006337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 892750600869157666670891 1339125901303736500006337)
                ·
                  refine ⟨1004344425977802375004753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1339125901303736500006337 1004344425977802375004753)
                  ·
                    refine ⟨753258319483351781253565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1004344425977802375004753 753258319483351781253565)
                    ·
                      refine ⟨282471869806256917970087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 753258319483351781253565 282471869806256917970087)
                      ·
                        rfl

theorem cell23_550112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_550112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550112 prefixEnd_550112 := by exact prefixLift 550112
  have htrace : WordTrace (prefixWord ++ tailWord_550112) baseStart_550112 baseEnd_550112 := by
    simpa [prefixWord, tailWord_550112, baseEnd_550112] using wordTrace_append hprefix tailTrace_550112
  have hstable : (prefixWord ++ tailWord_550112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550112).length < 2 ^ (prefixWord ++ tailWord_550112).sum := by decide
  have hdescent : baseEnd_550112 < baseStart_550112 := by decide
  rcases family_descends (prefixWord ++ tailWord_550112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550186 : List Nat := [3, 1, 4, 2, 1, 2, 1, 2, 2, 3, 2]
def baseStart_550186 : Nat := 118140960795 + 550186 * 2 ^ 59
def prefixEnd_550186 : Nat := 4983230072969 + 3 ^ 40 * 550186 * 2
def baseEnd_550186 : Nat := 282509867374689628444747

theorem tailTrace_550186 : CollatzResearch.WordTrace tailWord_550186 prefixEnd_550186 282509867374689628444747 := by
  unfold tailWord_550186
  simp only [CollatzResearch.WordTrace]
  refine ⟨5016732996194390283257603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13377954656518374088686941 5016732996194390283257603)
  ·
    refine ⟨7525099494291585424886405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5016732996194390283257603 7525099494291585424886405)
    ·
      refine ⟨1410956155179672267166201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7525099494291585424886405 1410956155179672267166201)
      ·
        refine ⟨1058217116384754200374651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1410956155179672267166201 1058217116384754200374651)
        ·
          refine ⟨1587325674577131300561977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1058217116384754200374651 1587325674577131300561977)
          ·
            refine ⟨1190494255932848475421483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1587325674577131300561977 1190494255932848475421483)
            ·
              refine ⟨1785741383899272713132225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1190494255932848475421483 1785741383899272713132225)
              ·
                refine ⟨1339306037924454534849169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1785741383899272713132225 1339306037924454534849169)
                ·
                  refine ⟨1004479528443340901136877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1339306037924454534849169 1004479528443340901136877)
                  ·
                    refine ⟨376679823166252837926329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1004479528443340901136877 376679823166252837926329)
                    ·
                      refine ⟨282509867374689628444747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 376679823166252837926329 282509867374689628444747)
                      ·
                        rfl

theorem cell23_550186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_550186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550186 prefixEnd_550186 := by exact prefixLift 550186
  have htrace : WordTrace (prefixWord ++ tailWord_550186) baseStart_550186 baseEnd_550186 := by
    simpa [prefixWord, tailWord_550186, baseEnd_550186] using wordTrace_append hprefix tailTrace_550186
  have hstable : (prefixWord ++ tailWord_550186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550186).length < 2 ^ (prefixWord ++ tailWord_550186).sum := by decide
  have hdescent : baseEnd_550186 < baseStart_550186 := by decide
  rcases family_descends (prefixWord ++ tailWord_550186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550192 : List Nat := [2, 1, 1, 1, 2, 2, 4, 4, 2, 4]
def baseStart_550192 : Nat := 118140960795 + 550192 * 2 ^ 59
def prefixEnd_550192 : Nat := 4983230072969 + 3 ^ 40 * 550192 * 2
def baseEnd_550192 : Nat := 94170982752872201656573

theorem tailTrace_550192 : CollatzResearch.WordTrace tailWord_550192 prefixEnd_550192 94170982752872201656573 := by
  unfold tailWord_550192
  simp only [CollatzResearch.WordTrace]
  refine ⟨10033575411377912078874415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13378100548503882771832553 10033575411377912078874415)
  ·
    refine ⟨15050363117066868118311623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10033575411377912078874415 15050363117066868118311623)
    ·
      refine ⟨22575544675600302177467435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15050363117066868118311623 22575544675600302177467435)
      ·
        refine ⟨33863317013400453266201153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22575544675600302177467435 33863317013400453266201153)
        ·
          refine ⟨25397487760050339949650865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33863317013400453266201153 25397487760050339949650865)
          ·
            refine ⟨19048115820037754962238149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25397487760050339949650865 19048115820037754962238149)
            ·
              refine ⟨3571521716257079055419653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19048115820037754962238149 3571521716257079055419653)
              ·
                refine ⟨669660321798202322891185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3571521716257079055419653 669660321798202322891185)
                ·
                  refine ⟨502245241348651742168389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 669660321798202322891185 502245241348651742168389)
                  ·
                    refine ⟨94170982752872201656573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 502245241348651742168389 94170982752872201656573)
                    ·
                      rfl

theorem cell23_550192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 2, 4].length) (baseStart_550192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550192 prefixEnd_550192 := by exact prefixLift 550192
  have htrace : WordTrace (prefixWord ++ tailWord_550192) baseStart_550192 baseEnd_550192 := by
    simpa [prefixWord, tailWord_550192, baseEnd_550192] using wordTrace_append hprefix tailTrace_550192
  have hstable : (prefixWord ++ tailWord_550192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550192).length < 2 ^ (prefixWord ++ tailWord_550192).sum := by decide
  have hdescent : baseEnd_550192 < baseStart_550192 := by decide
  rcases family_descends (prefixWord ++ tailWord_550192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550193 : List Nat := [1, 2, 2, 3, 3, 2, 3, 2, 1, 1, 3]
def baseStart_550193 : Nat := 118140960795 + 550193 * 2 ^ 59
def prefixEnd_550193 : Nat := 4983230072969 + 3 ^ 40 * 550193 * 2
def baseEnd_550193 : Nat := 282513461739271101057215

theorem tailTrace_550193 : CollatzResearch.WordTrace tailWord_550193 prefixEnd_550193 282513461739271101057215 := by
  unfold tailWord_550193
  simp only [CollatzResearch.WordTrace]
  refine ⟨20067187295752201328535233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13378124863834800885690155 20067187295752201328535233)
  ·
    refine ⟨15050390471814150996401425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20067187295752201328535233 15050390471814150996401425)
    ·
      refine ⟨11287792853860613247301069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15050390471814150996401425 11287792853860613247301069)
      ·
        refine ⟨4232922320197729967737901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11287792853860613247301069 4232922320197729967737901)
        ·
          refine ⟨1587345870074148737901713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4232922320197729967737901 1587345870074148737901713)
          ·
            refine ⟨1190509402555611553426285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1587345870074148737901713 1190509402555611553426285)
            ·
              refine ⟨446441025958354332534857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1190509402555611553426285 446441025958354332534857)
              ·
                refine ⟨334830769468765749401143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 446441025958354332534857 334830769468765749401143)
                ·
                  refine ⟨502246154203148624101715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 334830769468765749401143 502246154203148624101715)
                  ·
                    refine ⟨753369231304722936152573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 502246154203148624101715 753369231304722936152573)
                    ·
                      refine ⟨282513461739271101057215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 753369231304722936152573 282513461739271101057215)
                      ·
                        rfl

theorem cell23_550193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_550193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550193 prefixEnd_550193 := by exact prefixLift 550193
  have htrace : WordTrace (prefixWord ++ tailWord_550193) baseStart_550193 baseEnd_550193 := by
    simpa [prefixWord, tailWord_550193, baseEnd_550193] using wordTrace_append hprefix tailTrace_550193
  have hstable : (prefixWord ++ tailWord_550193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550193).length < 2 ^ (prefixWord ++ tailWord_550193).sum := by decide
  have hdescent : baseEnd_550193 < baseStart_550193 := by decide
  rcases family_descends (prefixWord ++ tailWord_550193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550195 : List Nat := [1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 6]
def baseStart_550195 : Nat := 118140960795 + 550195 * 2 ^ 59
def prefixEnd_550195 : Nat := 4983230072969 + 3 ^ 40 * 550195 * 2
def baseEnd_550195 : Nat := 282514488700580093232205

theorem tailTrace_550195 : CollatzResearch.WordTrace tailWord_550195 prefixEnd_550195 282514488700580093232205 := by
  unfold tailWord_550195
  simp only [CollatzResearch.WordTrace]
  refine ⟨20067260241744955670108039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13378173494496637113405359 20067260241744955670108039)
  ·
    refine ⟨30100890362617433505162059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20067260241744955670108039 30100890362617433505162059)
    ·
      refine ⟨45151335543926150257743089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30100890362617433505162059 45151335543926150257743089)
      ·
        refine ⟨33863501657944612693307317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45151335543926150257743089 33863501657944612693307317)
        ·
          refine ⟨3174703280432307439997561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33863501657944612693307317 3174703280432307439997561)
          ·
            refine ⟨2381027460324230579998171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3174703280432307439997561 2381027460324230579998171)
            ·
              refine ⟨3571541190486345869997257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2381027460324230579998171 3571541190486345869997257)
              ·
                refine ⟨2678655892864759402497943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3571541190486345869997257 2678655892864759402497943)
                ·
                  refine ⟨4017983839297139103746915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2678655892864759402497943 4017983839297139103746915)
                  ·
                    refine ⟨6026975758945708655620373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4017983839297139103746915 6026975758945708655620373)
                    ·
                      refine ⟨282514488700580093232205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6026975758945708655620373 282514488700580093232205)
                      ·
                        rfl

theorem cell23_550195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 6].length) (baseStart_550195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550195 prefixEnd_550195 := by exact prefixLift 550195
  have htrace : WordTrace (prefixWord ++ tailWord_550195) baseStart_550195 baseEnd_550195 := by
    simpa [prefixWord, tailWord_550195, baseEnd_550195] using wordTrace_append hprefix tailTrace_550195
  have hstable : (prefixWord ++ tailWord_550195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550195).length < 2 ^ (prefixWord ++ tailWord_550195).sum := by decide
  have hdescent : baseEnd_550195 < baseStart_550195 := by decide
  rcases family_descends (prefixWord ++ tailWord_550195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550202 : List Nat := [3, 1, 1, 1, 4, 1, 2, 2, 3, 2, 3]
def baseStart_550202 : Nat := 118140960795 + 550202 * 2 ^ 59
def prefixEnd_550202 : Nat := 4983230072969 + 3 ^ 40 * 550202 * 2
def baseEnd_550202 : Nat := 282518083065161565844673

theorem tailTrace_550202 : CollatzResearch.WordTrace tailWord_550202 prefixEnd_550202 282518083065161565844673 := by
  unfold tailWord_550202
  simp only [CollatzResearch.WordTrace]
  refine ⟨5016878888179898966403215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13378343701813063910408573 5016878888179898966403215)
  ·
    refine ⟨7525318332269848449604823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5016878888179898966403215 7525318332269848449604823)
    ·
      refine ⟨11287977498404772674407235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7525318332269848449604823 11287977498404772674407235)
      ·
        refine ⟨16931966247607159011610853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11287977498404772674407235 16931966247607159011610853)
        ·
          refine ⟨3174743671426342314677035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16931966247607159011610853 3174743671426342314677035)
          ·
            refine ⟨4762115507139513472015553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3174743671426342314677035 4762115507139513472015553)
            ·
              refine ⟨3571586630354635104011665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4762115507139513472015553 3571586630354635104011665)
              ·
                refine ⟨2678689972765976328008749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3571586630354635104011665 2678689972765976328008749)
                ·
                  refine ⟨1004508739787241123003281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2678689972765976328008749 1004508739787241123003281)
                  ·
                    refine ⟨753381554840430842252461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1004508739787241123003281 753381554840430842252461)
                    ·
                      refine ⟨282518083065161565844673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 753381554840430842252461 282518083065161565844673)
                      ·
                        rfl

theorem cell23_550202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 3, 2, 3].length) (baseStart_550202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550202 prefixEnd_550202 := by exact prefixLift 550202
  have htrace : WordTrace (prefixWord ++ tailWord_550202) baseStart_550202 baseEnd_550202 := by
    simpa [prefixWord, tailWord_550202, baseEnd_550202] using wordTrace_append hprefix tailTrace_550202
  have hstable : (prefixWord ++ tailWord_550202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550202).length < 2 ^ (prefixWord ++ tailWord_550202).sum := by decide
  have hdescent : baseEnd_550202 < baseStart_550202 := by decide
  rcases family_descends (prefixWord ++ tailWord_550202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550232 : List Nat := [2, 1, 2, 2, 1, 1, 5, 2, 1, 3, 3]
def baseStart_550232 : Nat := 118140960795 + 550232 * 2 ^ 59
def prefixEnd_550232 : Nat := 4983230072969 + 3 ^ 40 * 550232 * 2
def baseEnd_550232 : Nat := 282533487484796448469535

theorem tailTrace_550232 : CollatzResearch.WordTrace tailWord_550232 prefixEnd_550232 282533487484796448469535 := by
  unfold tailWord_550232
  simp only [CollatzResearch.WordTrace]
  refine ⟨10034304871305455494602475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13379073161740607326136633 10034304871305455494602475)
  ·
    refine ⟨15051457306958183241903713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10034304871305455494602475 15051457306958183241903713)
    ·
      refine ⟨11288592980218637431427785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15051457306958183241903713 11288592980218637431427785)
      ·
        refine ⟨8466444735163978073570839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11288592980218637431427785 8466444735163978073570839)
        ·
          refine ⟨12699667102745967110356259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8466444735163978073570839 12699667102745967110356259)
          ·
            refine ⟨19049500654118950665534389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12699667102745967110356259 19049500654118950665534389)
            ·
              refine ⟨1785890686323651624893849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19049500654118950665534389 1785890686323651624893849)
              ·
                refine ⟨1339418014742738718670387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1785890686323651624893849 1339418014742738718670387)
                ·
                  refine ⟨2009127022114108078005581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1339418014742738718670387 2009127022114108078005581)
                  ·
                    refine ⟨753422633292790529252093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2009127022114108078005581 753422633292790529252093)
                    ·
                      refine ⟨282533487484796448469535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 753422633292790529252093 282533487484796448469535)
                      ·
                        rfl

theorem cell23_550232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_550232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550232 prefixEnd_550232 := by exact prefixLift 550232
  have htrace : WordTrace (prefixWord ++ tailWord_550232) baseStart_550232 baseEnd_550232 := by
    simpa [prefixWord, tailWord_550232, baseEnd_550232] using wordTrace_append hprefix tailTrace_550232
  have hstable : (prefixWord ++ tailWord_550232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550232).length < 2 ^ (prefixWord ++ tailWord_550232).sum := by decide
  have hdescent : baseEnd_550232 < baseStart_550232 := by decide
  rcases family_descends (prefixWord ++ tailWord_550232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550250 : List Nat := [3, 1, 3, 3, 2, 1, 1, 4, 1, 2, 2]
def baseStart_550250 : Nat := 118140960795 + 550250 * 2 ^ 59
def prefixEnd_550250 : Nat := 4983230072969 + 3 ^ 40 * 550250 * 2
def baseEnd_550250 : Nat := 282542730136577378044453

theorem tailTrace_550250 : CollatzResearch.WordTrace tailWord_550250 prefixEnd_550250 282542730136577378044453 := by
  unfold tailWord_550250
  simp only [CollatzResearch.WordTrace]
  refine ⟨5017316564136425015840051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13379510837697133375573469 5017316564136425015840051)
  ·
    refine ⟨7525974846204637523760077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5017316564136425015840051 7525974846204637523760077)
    ·
      refine ⟨2822240567326739071410029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7525974846204637523760077 2822240567326739071410029)
      ·
        refine ⟨1058340212747527151778761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2822240567326739071410029 1058340212747527151778761)
        ·
          refine ⟨793755159560645363834071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1058340212747527151778761 793755159560645363834071)
          ·
            refine ⟨1190632739340968045751107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 793755159560645363834071 1190632739340968045751107)
            ·
              refine ⟨1785949109011452068626661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1190632739340968045751107 1785949109011452068626661)
              ·
                refine ⟨334865457939647262867499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1785949109011452068626661 334865457939647262867499)
                ·
                  refine ⟨502298186909470894301249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 334865457939647262867499 502298186909470894301249)
                  ·
                    refine ⟨376723640182103170725937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 502298186909470894301249 376723640182103170725937)
                    ·
                      refine ⟨282542730136577378044453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 376723640182103170725937 282542730136577378044453)
                      ·
                        rfl

theorem cell23_550250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_550250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550250 prefixEnd_550250 := by exact prefixLift 550250
  have htrace : WordTrace (prefixWord ++ tailWord_550250) baseStart_550250 baseEnd_550250 := by
    simpa [prefixWord, tailWord_550250, baseEnd_550250] using wordTrace_append hprefix tailTrace_550250
  have hstable : (prefixWord ++ tailWord_550250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550250).length < 2 ^ (prefixWord ++ tailWord_550250).sum := by decide
  have hdescent : baseEnd_550250 < baseStart_550250 := by decide
  rcases family_descends (prefixWord ++ tailWord_550250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550255 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 4]
def baseStart_550255 : Nat := 118140960795 + 550255 * 2 ^ 59
def prefixEnd_550255 : Nat := 4983230072969 + 3 ^ 40 * 550255 * 2
def baseEnd_550255 : Nat := 282545297539849858481929

theorem tailTrace_550255 : CollatzResearch.WordTrace tailWord_550255 prefixEnd_550255 282545297539849858481929 := by
  unfold tailWord_550255
  simp only [CollatzResearch.WordTrace]
  refine ⟨20069448621527585917292219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13379632414351723944861479 20069448621527585917292219)
  ·
    refine ⟨30104172932291378875938329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20069448621527585917292219 30104172932291378875938329)
    ·
      refine ⟨22578129699218534156953747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30104172932291378875938329 22578129699218534156953747)
      ·
        refine ⟨33867194548827801235430621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22578129699218534156953747 33867194548827801235430621)
        ·
          refine ⟨12700197955810425463286483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33867194548827801235430621 12700197955810425463286483)
          ·
            refine ⟨19050296933715638194929725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12700197955810425463286483 19050296933715638194929725)
            ·
              refine ⟨7143861350143364323098647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19050296933715638194929725 7143861350143364323098647)
              ·
                refine ⟨10715792025215046484647971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7143861350143364323098647 10715792025215046484647971)
                ·
                  refine ⟨16073688037822569726971957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10715792025215046484647971 16073688037822569726971957)
                  ·
                    refine ⟨1506908253545865911903621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16073688037822569726971957 1506908253545865911903621)
                    ·
                      refine ⟨282545297539849858481929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1506908253545865911903621 282545297539849858481929)
                      ·
                        rfl

theorem cell23_550255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 4].length) (baseStart_550255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550255 prefixEnd_550255 := by exact prefixLift 550255
  have htrace : WordTrace (prefixWord ++ tailWord_550255) baseStart_550255 baseEnd_550255 := by
    simpa [prefixWord, tailWord_550255, baseEnd_550255] using wordTrace_append hprefix tailTrace_550255
  have hstable : (prefixWord ++ tailWord_550255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550255).length < 2 ^ (prefixWord ++ tailWord_550255).sum := by decide
  have hdescent : baseEnd_550255 < baseStart_550255 := by decide
  rcases family_descends (prefixWord ++ tailWord_550255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550265 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 1, 8]
def baseStart_550265 : Nat := 118140960795 + 550265 * 2 ^ 59
def prefixEnd_550265 : Nat := 4983230072969 + 3 ^ 40 * 550265 * 2
def baseEnd_550265 : Nat := 94183477448798273118961

theorem tailTrace_550265 : CollatzResearch.WordTrace tailWord_550265 prefixEnd_550265 94183477448798273118961 := by
  unfold tailWord_550265
  simp only [CollatzResearch.WordTrace]
  refine ⟨20069813351491357625156249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13379875567660905083437499 20069813351491357625156249)
  ·
    refine ⟨15052360013618518218867187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20069813351491357625156249 15052360013618518218867187)
    ·
      refine ⟨22578540020427777328300781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15052360013618518218867187 22578540020427777328300781)
      ·
        refine ⟨8466952507660416498112793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22578540020427777328300781 8466952507660416498112793)
        ·
          refine ⟨6350214380745312373584595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8466952507660416498112793 6350214380745312373584595)
          ·
            refine ⟨9525321571117968560376893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6350214380745312373584595 9525321571117968560376893)
            ·
              refine ⟨3571995589169238210141335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9525321571117968560376893 3571995589169238210141335)
              ·
                refine ⟨5357993383753857315212003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3571995589169238210141335 5357993383753857315212003)
                ·
                  refine ⟨8036990075630785972818005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5357993383753857315212003 8036990075630785972818005)
                  ·
                    refine ⟨94183477448798273118961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8036990075630785972818005 94183477448798273118961)
                    ·
                      rfl

theorem cell23_550265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 8].length) (baseStart_550265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550265 prefixEnd_550265 := by exact prefixLift 550265
  have htrace : WordTrace (prefixWord ++ tailWord_550265) baseStart_550265 baseEnd_550265 := by
    simpa [prefixWord, tailWord_550265, baseEnd_550265] using wordTrace_append hprefix tailTrace_550265
  have hstable : (prefixWord ++ tailWord_550265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550265).length < 2 ^ (prefixWord ++ tailWord_550265).sum := by decide
  have hdescent : baseEnd_550265 < baseStart_550265 := by decide
  rcases family_descends (prefixWord ++ tailWord_550265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550289 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 6, 2, 2]
def baseStart_550289 : Nat := 118140960795 + 550289 * 2 ^ 59
def prefixEnd_550289 : Nat := 4983230072969 + 3 ^ 40 * 550289 * 2
def baseEnd_550289 : Nat := 282562755882102725456773

theorem tailTrace_550289 : CollatzResearch.WordTrace tailWord_550289 prefixEnd_550289 282562755882102725456773 := by
  unfold tailWord_550289
  simp only [CollatzResearch.WordTrace]
  refine ⟨20070688703404409724029921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13380459135602939816019947 20070688703404409724029921)
  ·
    refine ⟨15053016527553307293022441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20070688703404409724029921 15053016527553307293022441)
    ·
      refine ⟨11289762395664980469766831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15053016527553307293022441 11289762395664980469766831)
      ·
        refine ⟨16934643593497470704650247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11289762395664980469766831 16934643593497470704650247)
        ·
          refine ⟨25401965390246206056975371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16934643593497470704650247 25401965390246206056975371)
          ·
            refine ⟨38102948085369309085463057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25401965390246206056975371 38102948085369309085463057)
            ·
              refine ⟨28577211064026981814097293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38102948085369309085463057 28577211064026981814097293)
              ·
                refine ⟨10716454149010118180286485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28577211064026981814097293 10716454149010118180286485)
                ·
                  refine ⟨502333788234849289700929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10716454149010118180286485 502333788234849289700929)
                  ·
                    refine ⟨376750341176136967275697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 502333788234849289700929 376750341176136967275697)
                    ·
                      refine ⟨282562755882102725456773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 376750341176136967275697 282562755882102725456773)
                      ·
                        rfl

theorem cell23_550289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6, 2, 2].length) (baseStart_550289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550289 prefixEnd_550289 := by exact prefixLift 550289
  have htrace : WordTrace (prefixWord ++ tailWord_550289) baseStart_550289 baseEnd_550289 := by
    simpa [prefixWord, tailWord_550289, baseEnd_550289] using wordTrace_append hprefix tailTrace_550289
  have hstable : (prefixWord ++ tailWord_550289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550289).length < 2 ^ (prefixWord ++ tailWord_550289).sum := by decide
  have hdescent : baseEnd_550289 < baseStart_550289 := by decide
  rcases family_descends (prefixWord ++ tailWord_550289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550295 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 11]
def baseStart_550295 : Nat := 118140960795 + 550295 * 2 ^ 59
def prefixEnd_550295 : Nat := 4983230072969 + 3 ^ 40 * 550295 * 2
def baseEnd_550295 : Nat := 31396204085114411331305

theorem tailTrace_550295 : CollatzResearch.WordTrace tailWord_550295 prefixEnd_550295 31396204085114411331305 := by
  unfold tailWord_550295
  simp only [CollatzResearch.WordTrace]
  refine ⟨20070907541382672748748339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13380605027588448499165559 20070907541382672748748339)
  ·
    refine ⟨30106361312074009123122509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20070907541382672748748339 30106361312074009123122509)
    ·
      refine ⟨11289885492027753421170941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30106361312074009123122509 11289885492027753421170941)
      ·
        refine ⟨4233707059510407532939103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11289885492027753421170941 4233707059510407532939103)
        ·
          refine ⟨6350560589265611299408655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4233707059510407532939103 6350560589265611299408655)
          ·
            refine ⟨9525840883898416949112983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6350560589265611299408655 9525840883898416949112983)
            ·
              refine ⟨14288761325847625423669475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9525840883898416949112983 14288761325847625423669475)
              ·
                refine ⟨21433141988771438135504213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14288761325847625423669475 21433141988771438135504213)
                ·
                  refine ⟨31396204085114411331305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 21433141988771438135504213 31396204085114411331305)
                  ·
                    rfl

theorem cell23_550295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 11].length) (baseStart_550295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550295 prefixEnd_550295 := by exact prefixLift 550295
  have htrace : WordTrace (prefixWord ++ tailWord_550295) baseStart_550295 baseEnd_550295 := by
    simpa [prefixWord, tailWord_550295, baseEnd_550295] using wordTrace_append hprefix tailTrace_550295
  have hstable : (prefixWord ++ tailWord_550295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550295).length < 2 ^ (prefixWord ++ tailWord_550295).sum := by decide
  have hdescent : baseEnd_550295 < baseStart_550295 := by decide
  rcases family_descends (prefixWord ++ tailWord_550295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550300 : List Nat := [2, 2, 3, 4, 1, 2, 1, 2, 2, 1, 3]
def baseStart_550300 : Nat := 118140960795 + 550300 * 2 ^ 59
def prefixEnd_550300 : Nat := 4983230072969 + 3 ^ 40 * 550300 * 2
def baseEnd_550300 : Nat := 282568404169302182419223

theorem tailTrace_550300 : CollatzResearch.WordTrace tailWord_550300 prefixEnd_550300 282568404169302182419223 := by
  unfold tailWord_550300
  simp only [CollatzResearch.WordTrace]
  refine ⟨10035544953182279301340177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13380726604243039068453569 10035544953182279301340177)
  ·
    refine ⟨7526658714886709476005133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10035544953182279301340177 7526658714886709476005133)
    ·
      refine ⟨2822497018082516053501925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7526658714886709476005133 2822497018082516053501925)
      ·
        refine ⟨529218190890471760031611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2822497018082516053501925 529218190890471760031611)
        ·
          refine ⟨793827286335707640047417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529218190890471760031611 793827286335707640047417)
          ·
            refine ⟨595370464751780730035563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 793827286335707640047417 595370464751780730035563)
            ·
              refine ⟨893055697127671095053345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595370464751780730035563 893055697127671095053345)
              ·
                refine ⟨669791772845753321290009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 893055697127671095053345 669791772845753321290009)
                ·
                  refine ⟨502343829634314990967507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 669791772845753321290009 502343829634314990967507)
                  ·
                    refine ⟨753515744451472486451261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 502343829634314990967507 753515744451472486451261)
                    ·
                      refine ⟨282568404169302182419223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 753515744451472486451261 282568404169302182419223)
                      ·
                        rfl

theorem cell23_550300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_550300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550300 prefixEnd_550300 := by exact prefixLift 550300
  have htrace : WordTrace (prefixWord ++ tailWord_550300) baseStart_550300 baseEnd_550300 := by
    simpa [prefixWord, tailWord_550300, baseEnd_550300] using wordTrace_append hprefix tailTrace_550300
  have hstable : (prefixWord ++ tailWord_550300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550300).length < 2 ^ (prefixWord ++ tailWord_550300).sum := by decide
  have hdescent : baseEnd_550300 < baseStart_550300 := by decide
  rcases family_descends (prefixWord ++ tailWord_550300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550322 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3]
def baseStart_550322 : Nat := 118140960795 + 550322 * 2 ^ 59
def prefixEnd_550322 : Nat := 4983230072969 + 3 ^ 40 * 550322 * 2
def baseEnd_550322 : Nat := 282579700743701096344121

theorem tailTrace_550322 : CollatzResearch.WordTrace tailWord_550322 prefixEnd_550322 282579700743701096344121 := by
  unfold tailWord_550322
  simp only [CollatzResearch.WordTrace]
  refine ⟨5017973078071214089995305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13381261541523237573320813 5017973078071214089995305)
  ·
    refine ⟨3763479808553410567496479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5017973078071214089995305 3763479808553410567496479)
    ·
      refine ⟨5645219712830115851244719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3763479808553410567496479 5645219712830115851244719)
      ·
        refine ⟨8467829569245173776867079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5645219712830115851244719 8467829569245173776867079)
        ·
          refine ⟨12701744353867760665300619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8467829569245173776867079 12701744353867760665300619)
          ·
            refine ⟨19052616530801640997950929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12701744353867760665300619 19052616530801640997950929)
            ·
              refine ⟨14289462398101230748463197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19052616530801640997950929 14289462398101230748463197)
              ·
                refine ⟨5358548399287961530673699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14289462398101230748463197 5358548399287961530673699)
                ·
                  refine ⟨8037822598931942296010549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5358548399287961530673699 8037822598931942296010549)
                  ·
                    refine ⟨753545868649869590250989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8037822598931942296010549 753545868649869590250989)
                    ·
                      refine ⟨282579700743701096344121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 753545868649869590250989 282579700743701096344121)
                      ·
                        rfl

theorem cell23_550322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_550322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550322 prefixEnd_550322 := by exact prefixLift 550322
  have htrace : WordTrace (prefixWord ++ tailWord_550322) baseStart_550322 baseEnd_550322 := by
    simpa [prefixWord, tailWord_550322, baseEnd_550322] using wordTrace_append hprefix tailTrace_550322
  have hstable : (prefixWord ++ tailWord_550322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550322).length < 2 ^ (prefixWord ++ tailWord_550322).sum := by decide
  have hdescent : baseEnd_550322 < baseStart_550322 := by decide
  rcases family_descends (prefixWord ++ tailWord_550322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550346 : List Nat := [3, 1, 2, 1, 2, 5, 1, 3, 5]
def baseStart_550346 : Nat := 118140960795 + 550346 * 2 ^ 59
def prefixEnd_550346 : Nat := 4983230072969 + 3 ^ 40 * 550346 * 2
def baseEnd_550346 : Nat := 31399113808823222493779

theorem tailTrace_550346 : CollatzResearch.WordTrace tailWord_550346 prefixEnd_550346 31399113808823222493779 := by
  unfold tailWord_550346
  simp only [CollatzResearch.WordTrace]
  refine ⟨5018191916049477114713723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13381845109465272305903261 5018191916049477114713723)
  ·
    refine ⟨7527287874074215672070585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5018191916049477114713723 7527287874074215672070585)
    ·
      refine ⟨5645465905555661754052939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7527287874074215672070585 5645465905555661754052939)
      ·
        refine ⟨8468198858333492631079409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5645465905555661754052939 8468198858333492631079409)
        ·
          refine ⟨6351149143750119473309557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8468198858333492631079409 6351149143750119473309557)
          ·
            refine ⟨595420232226573700622771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6351149143750119473309557 595420232226573700622771)
            ·
              refine ⟨893130348339860550934157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595420232226573700622771 893130348339860550934157)
              ·
                refine ⟨334923880627447706600309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 893130348339860550934157 334923880627447706600309)
                ·
                  refine ⟨31399113808823222493779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 334923880627447706600309 31399113808823222493779)
                  ·
                    rfl

theorem cell23_550346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 3, 5].length) (baseStart_550346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550346 prefixEnd_550346 := by exact prefixLift 550346
  have htrace : WordTrace (prefixWord ++ tailWord_550346) baseStart_550346 baseEnd_550346 := by
    simpa [prefixWord, tailWord_550346, baseEnd_550346] using wordTrace_append hprefix tailTrace_550346
  have hstable : (prefixWord ++ tailWord_550346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550346).length < 2 ^ (prefixWord ++ tailWord_550346).sum := by decide
  have hdescent : baseEnd_550346 < baseStart_550346 := by decide
  rcases family_descends (prefixWord ++ tailWord_550346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550419 : List Nat := [1, 1, 1, 2, 1, 7, 2, 2, 6]
def baseStart_550419 : Nat := 118140960795 + 550419 * 2 ^ 59
def prefixEnd_550419 : Nat := 4983230072969 + 3 ^ 40 * 550419 * 2
def baseEnd_550419 : Nat := 31403278707465246314575

theorem tailTrace_550419 : CollatzResearch.WordTrace tailWord_550419 prefixEnd_550419 31403278707465246314575 := by
  unfold tailWord_550419
  simp only [CollatzResearch.WordTrace]
  refine ⟨20075430192933441926262311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13383620128622294617508207 20075430192933441926262311)
  ·
    refine ⟨30113145289400162889393467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20075430192933441926262311 30113145289400162889393467)
    ·
      refine ⟨45169717934100244334090201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30113145289400162889393467 45169717934100244334090201)
      ·
        refine ⟨33877288450575183250567651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45169717934100244334090201 33877288450575183250567651)
        ·
          refine ⟨50815932675862774875851477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33877288450575183250567651 50815932675862774875851477)
          ·
            refine ⟨1190998422090533786152769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 50815932675862774875851477 1190998422090533786152769)
            ·
              refine ⟨893248816567900339614577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1190998422090533786152769 893248816567900339614577)
              ·
                refine ⟨669936612425925254710933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 893248816567900339614577 669936612425925254710933)
                ·
                  refine ⟨31403278707465246314575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 669936612425925254710933 31403278707465246314575)
                  ·
                    rfl

theorem cell23_550419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 6].length) (baseStart_550419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550419 prefixEnd_550419 := by exact prefixLift 550419
  have htrace : WordTrace (prefixWord ++ tailWord_550419) baseStart_550419 baseEnd_550419 := by
    simpa [prefixWord, tailWord_550419, baseEnd_550419] using wordTrace_append hprefix tailTrace_550419
  have hstable : (prefixWord ++ tailWord_550419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550419).length < 2 ^ (prefixWord ++ tailWord_550419).sum := by decide
  have hdescent : baseEnd_550419 < baseStart_550419 := by decide
  rcases family_descends (prefixWord ++ tailWord_550419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550449 : List Nat := [1, 2, 2, 3, 1, 1, 1, 6, 1, 5]
def baseStart_550449 : Nat := 118140960795 + 550449 * 2 ^ 59
def prefixEnd_550449 : Nat := 4983230072969 + 3 ^ 40 * 550449 * 2
def baseEnd_550449 : Nat := 94214970928940699818679

theorem tailTrace_550449 : CollatzResearch.WordTrace tailWord_550449 prefixEnd_550449 94214970928940699818679 := by
  unfold tailWord_550449
  simp only [CollatzResearch.WordTrace]
  refine ⟨20076524382824757049854401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13384349588549838033236267 20076524382824757049854401)
  ·
    refine ⟨15057393287118567787390801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20076524382824757049854401 15057393287118567787390801)
    ·
      refine ⟨11293044965338925840543101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15057393287118567787390801 11293044965338925840543101)
      ·
        refine ⟨4234891862002097190203663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11293044965338925840543101 4234891862002097190203663)
        ·
          refine ⟨6352337793003145785305495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4234891862002097190203663 6352337793003145785305495)
          ·
            refine ⟨9528506689504718677958243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6352337793003145785305495 9528506689504718677958243)
            ·
              refine ⟨14292760034257078016937365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9528506689504718677958243 14292760034257078016937365)
              ·
                refine ⟨669973126605800532043939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14292760034257078016937365 669973126605800532043939)
                ·
                  refine ⟨1004959689908700798065909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 669973126605800532043939 1004959689908700798065909)
                  ·
                    refine ⟨94214970928940699818679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1004959689908700798065909 94214970928940699818679)
                    ·
                      rfl

theorem cell23_550449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 5].length) (baseStart_550449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550449 prefixEnd_550449 := by exact prefixLift 550449
  have htrace : WordTrace (prefixWord ++ tailWord_550449) baseStart_550449 baseEnd_550449 := by
    simpa [prefixWord, tailWord_550449, baseEnd_550449] using wordTrace_append hprefix tailTrace_550449
  have hstable : (prefixWord ++ tailWord_550449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550449).length < 2 ^ (prefixWord ++ tailWord_550449).sum := by decide
  have hdescent : baseEnd_550449 < baseStart_550449 := by decide
  rcases family_descends (prefixWord ++ tailWord_550449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550456 : List Nat := [2, 1, 2, 1, 4, 3, 1, 1, 1, 5, 2]
def baseStart_550456 : Nat := 118140960795 + 550456 * 2 ^ 59
def prefixEnd_550456 : Nat := 4983230072969 + 3 ^ 40 * 550456 * 2
def baseEnd_550456 : Nat := 282648507151403572068505

theorem tailTrace_550456 : CollatzResearch.WordTrace tailWord_550456 prefixEnd_550456 282648507151403572068505 := by
  unfold tailWord_550456
  simp only [CollatzResearch.WordTrace]
  refine ⟨10038389846899698622679611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13384519795866264830239481 10038389846899698622679611)
  ·
    refine ⟨15057584770349547934019417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10038389846899698622679611 15057584770349547934019417)
    ·
      refine ⟨11293188577762160950514563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15057584770349547934019417 11293188577762160950514563)
      ·
        refine ⟨16939782866643241425771845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11293188577762160950514563 16939782866643241425771845)
        ·
          refine ⟨3176209287495607767332221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16939782866643241425771845 3176209287495607767332221)
          ·
            refine ⟨1191078482810852912749583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3176209287495607767332221 1191078482810852912749583)
            ·
              refine ⟨1786617724216279369124375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1191078482810852912749583 1786617724216279369124375)
              ·
                refine ⟨2679926586324419053686563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1786617724216279369124375 2679926586324419053686563)
                ·
                  refine ⟨4019889879486628580529845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2679926586324419053686563 4019889879486628580529845)
                  ·
                    refine ⟨376864676201871429424673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4019889879486628580529845 376864676201871429424673)
                    ·
                      refine ⟨282648507151403572068505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 376864676201871429424673 282648507151403572068505)
                      ·
                        rfl

theorem cell23_550456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 1, 5, 2].length) (baseStart_550456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550456 prefixEnd_550456 := by exact prefixLift 550456
  have htrace : WordTrace (prefixWord ++ tailWord_550456) baseStart_550456 baseEnd_550456 := by
    simpa [prefixWord, tailWord_550456, baseEnd_550456] using wordTrace_append hprefix tailTrace_550456
  have hstable : (prefixWord ++ tailWord_550456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550456).length < 2 ^ (prefixWord ++ tailWord_550456).sum := by decide
  have hdescent : baseEnd_550456 < baseStart_550456 := by decide
  rcases family_descends (prefixWord ++ tailWord_550456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550463 : List Nat := [1, 1, 2, 2, 3, 3, 1, 5, 1, 1, 3]
def baseStart_550463 : Nat := 118140960795 + 550463 * 2 ^ 59
def prefixEnd_550463 : Nat := 4983230072969 + 3 ^ 40 * 550463 * 2
def baseEnd_550463 : Nat := 282652101515985044680973

theorem tailTrace_550463 : CollatzResearch.WordTrace tailWord_550463 prefixEnd_550463 282652101515985044680973 := by
  unfold tailWord_550463
  simp only [CollatzResearch.WordTrace]
  refine ⟨20077035004774037440864043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13384690003182691627242695 20077035004774037440864043)
  ·
    refine ⟨30115552507161056161296065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20077035004774037440864043 30115552507161056161296065)
    ·
      refine ⟨22586664380370792120972049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30115552507161056161296065 22586664380370792120972049)
      ·
        refine ⟨16939998285278094090729037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22586664380370792120972049 16939998285278094090729037)
        ·
          refine ⟨6352499356979285284023389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16939998285278094090729037 6352499356979285284023389)
          ·
            refine ⟨2382187258867231981508771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6352499356979285284023389 2382187258867231981508771)
            ·
              refine ⟨3573280888300847972263157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2382187258867231981508771 3573280888300847972263157)
              ·
                refine ⟨334995083278204497399671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3573280888300847972263157 334995083278204497399671)
                ·
                  refine ⟨502492624917306746099507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 334995083278204497399671 502492624917306746099507)
                  ·
                    refine ⟨753738937375960119149261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 502492624917306746099507 753738937375960119149261)
                    ·
                      refine ⟨282652101515985044680973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 753738937375960119149261 282652101515985044680973)
                      ·
                        rfl

theorem cell23_550463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 5, 1, 1, 3].length) (baseStart_550463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550463 prefixEnd_550463 := by exact prefixLift 550463
  have htrace : WordTrace (prefixWord ++ tailWord_550463) baseStart_550463 baseEnd_550463 := by
    simpa [prefixWord, tailWord_550463, baseEnd_550463] using wordTrace_append hprefix tailTrace_550463
  have hstable : (prefixWord ++ tailWord_550463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550463).length < 2 ^ (prefixWord ++ tailWord_550463).sum := by decide
  have hdescent : baseEnd_550463 < baseStart_550463 := by decide
  rcases family_descends (prefixWord ++ tailWord_550463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550470 : List Nat := [6, 1, 1, 1, 3, 2, 1, 2, 6]
def baseStart_550470 : Nat := 118140960795 + 550470 * 2 ^ 59
def prefixEnd_550470 : Nat := 4983230072969 + 3 ^ 40 * 550470 * 2
def baseEnd_550470 : Nat := 31406188431174057477049

theorem tailTrace_550470 : CollatzResearch.WordTrace tailWord_550470 prefixEnd_550470 31406188431174057477049 := by
  unfold tailWord_550470
  simp only [CollatzResearch.WordTrace]
  refine ⟨627415322367146176136527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13384860210499118424245909 627415322367146176136527)
  ·
    refine ⟨941122983550719264204791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 627415322367146176136527 941122983550719264204791)
    ·
      refine ⟨1411684475326078896307187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 941122983550719264204791 1411684475326078896307187)
      ·
        refine ⟨2117526712989118344460781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1411684475326078896307187 2117526712989118344460781)
        ·
          refine ⟨794072517370919379172793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2117526712989118344460781 794072517370919379172793)
          ·
            refine ⟨595554388028189534379595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 794072517370919379172793 595554388028189534379595)
            ·
              refine ⟨893331582042284301569393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595554388028189534379595 893331582042284301569393)
              ·
                refine ⟨669998686531713226177045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 893331582042284301569393 669998686531713226177045)
                ·
                  refine ⟨31406188431174057477049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 669998686531713226177045 31406188431174057477049)
                  ·
                    rfl

theorem cell23_550470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_550470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550470 prefixEnd_550470 := by exact prefixLift 550470
  have htrace : WordTrace (prefixWord ++ tailWord_550470) baseStart_550470 baseEnd_550470 := by
    simpa [prefixWord, tailWord_550470, baseEnd_550470] using wordTrace_append hprefix tailTrace_550470
  have hstable : (prefixWord ++ tailWord_550470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550470).length < 2 ^ (prefixWord ++ tailWord_550470).sum := by decide
  have hdescent : baseEnd_550470 < baseStart_550470 := by decide
  rcases family_descends (prefixWord ++ tailWord_550470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550489 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 5, 2, 3]
def baseStart_550489 : Nat := 118140960795 + 550489 * 2 ^ 59
def prefixEnd_550489 : Nat := 4983230072969 + 3 ^ 40 * 550489 * 2
def baseEnd_550489 : Nat := 282665452013001942955853

theorem tailTrace_550489 : CollatzResearch.WordTrace tailWord_550489 prefixEnd_550489 282665452013001942955853 := by
  unfold tailWord_550489
  simp only [CollatzResearch.WordTrace]
  refine ⟨20077983302679843881310521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13385322201786562587540347 20077983302679843881310521)
  ·
    refine ⟨15058487477009882910982891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20077983302679843881310521 15058487477009882910982891)
    ·
      refine ⟨22587731215514824366474337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15058487477009882910982891 22587731215514824366474337)
      ·
        refine ⟨16940798411636118274855753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22587731215514824366474337 16940798411636118274855753)
        ·
          refine ⟨12705598808727088706141815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16940798411636118274855753 12705598808727088706141815)
          ·
            refine ⟨19058398213090633059212723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12705598808727088706141815 19058398213090633059212723)
            ·
              refine ⟨28587597319635949588819085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19058398213090633059212723 28587597319635949588819085)
              ·
                refine ⟨10720348994863481095807157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28587597319635949588819085 10720348994863481095807157)
                ·
                  refine ⟨1005032718268451352731921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10720348994863481095807157 1005032718268451352731921)
                  ·
                    refine ⟨753774538701338514548941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1005032718268451352731921 753774538701338514548941)
                    ·
                      refine ⟨282665452013001942955853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 753774538701338514548941 282665452013001942955853)
                      ·
                        rfl

theorem cell23_550489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 2, 3].length) (baseStart_550489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550489 prefixEnd_550489 := by exact prefixLift 550489
  have htrace : WordTrace (prefixWord ++ tailWord_550489) baseStart_550489 baseEnd_550489 := by
    simpa [prefixWord, tailWord_550489, baseEnd_550489] using wordTrace_append hprefix tailTrace_550489
  have hstable : (prefixWord ++ tailWord_550489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550489).length < 2 ^ (prefixWord ++ tailWord_550489).sum := by decide
  have hdescent : baseEnd_550489 < baseStart_550489 := by decide
  rcases family_descends (prefixWord ++ tailWord_550489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550499 : List Nat := [1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 6]
def baseStart_550499 : Nat := 118140960795 + 550499 * 2 ^ 59
def prefixEnd_550499 : Nat := 4983230072969 + 3 ^ 40 * 550499 * 2
def baseEnd_550499 : Nat := 282670586819546903830807

theorem tailTrace_550499 : CollatzResearch.WordTrace tailWord_550499 prefixEnd_550499 282670586819546903830807 := by
  unfold tailWord_550499
  simp only [CollatzResearch.WordTrace]
  refine ⟨20078348032643615589174551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13385565355095743726116367 20078348032643615589174551)
  ·
    refine ⟨30117522048965423383761827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20078348032643615589174551 30117522048965423383761827)
    ·
      refine ⟨45176283073448135075642741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30117522048965423383761827 45176283073448135075642741)
      ·
        refine ⟨4235276538135762663341507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45176283073448135075642741 4235276538135762663341507)
        ·
          refine ⟨6352914807203643995012261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4235276538135762663341507 6352914807203643995012261)
          ·
            refine ⟨1191171526350683249064799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6352914807203643995012261 1191171526350683249064799)
            ·
              refine ⟨1786757289526024873597199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1191171526350683249064799 1786757289526024873597199)
              ·
                refine ⟨2680135934289037310395799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1786757289526024873597199 2680135934289037310395799)
                ·
                  refine ⟨4020203901433555965593699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2680135934289037310395799 4020203901433555965593699)
                  ·
                    refine ⟨6030305852150333948390549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4020203901433555965593699 6030305852150333948390549)
                    ·
                      refine ⟨282670586819546903830807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6030305852150333948390549 282670586819546903830807)
                      ·
                        rfl

theorem cell23_550499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_550499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550499 prefixEnd_550499 := by exact prefixLift 550499
  have htrace : WordTrace (prefixWord ++ tailWord_550499) baseStart_550499 baseEnd_550499 := by
    simpa [prefixWord, tailWord_550499, baseEnd_550499] using wordTrace_append hprefix tailTrace_550499
  have hstable : (prefixWord ++ tailWord_550499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550499).length < 2 ^ (prefixWord ++ tailWord_550499).sum := by decide
  have hdescent : baseEnd_550499 < baseStart_550499 := by decide
  rcases family_descends (prefixWord ++ tailWord_550499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550503 : List Nat := [1, 1, 5, 1, 1, 1, 4, 2, 3, 2, 2]
def baseStart_550503 : Nat := 118140960795 + 550503 * 2 ^ 59
def prefixEnd_550503 : Nat := 4983230072969 + 3 ^ 40 * 550503 * 2
def baseEnd_550503 : Nat := 282672640742164888180789

theorem tailTrace_550503 : CollatzResearch.WordTrace tailWord_550503 prefixEnd_550503 282672640742164888180789 := by
  unfold tailWord_550503
  simp only [CollatzResearch.WordTrace]
  refine ⟨20078493924629124272320163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13385662616419416181546775 20078493924629124272320163)
  ·
    refine ⟨30117740886943686408480245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20078493924629124272320163 30117740886943686408480245)
    ·
      refine ⟨2823538208150970600795023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30117740886943686408480245 2823538208150970600795023)
      ·
        refine ⟨4235307312226455901192535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2823538208150970600795023 4235307312226455901192535)
        ·
          refine ⟨6352960968339683851788803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4235307312226455901192535 6352960968339683851788803)
          ·
            refine ⟨9529441452509525777683205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6352960968339683851788803 9529441452509525777683205)
            ·
              refine ⟨1786770272345536083315601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9529441452509525777683205 1786770272345536083315601)
              ·
                refine ⟨1340077704259152062486701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1786770272345536083315601 1340077704259152062486701)
                ·
                  refine ⟨502529139097182023432513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1340077704259152062486701 502529139097182023432513)
                  ·
                    refine ⟨376896854322886517574385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 502529139097182023432513 376896854322886517574385)
                    ·
                      refine ⟨282672640742164888180789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 376896854322886517574385 282672640742164888180789)
                      ·
                        rfl

theorem cell23_550503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_550503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550503 prefixEnd_550503 := by exact prefixLift 550503
  have htrace : WordTrace (prefixWord ++ tailWord_550503) baseStart_550503 baseEnd_550503 := by
    simpa [prefixWord, tailWord_550503, baseEnd_550503] using wordTrace_append hprefix tailTrace_550503
  have hstable : (prefixWord ++ tailWord_550503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550503).length < 2 ^ (prefixWord ++ tailWord_550503).sum := by decide
  have hdescent : baseEnd_550503 < baseStart_550503 := by decide
  rcases family_descends (prefixWord ++ tailWord_550503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550519 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 3, 3, 3]
def baseStart_550519 : Nat := 118140960795 + 550519 * 2 ^ 59
def prefixEnd_550519 : Nat := 4983230072969 + 3 ^ 40 * 550519 * 2
def baseEnd_550519 : Nat := 282680856432636825580715

theorem tailTrace_550519 : CollatzResearch.WordTrace tailWord_550519 prefixEnd_550519 282680856432636825580715 := by
  unfold tailWord_550519
  simp only [CollatzResearch.WordTrace]
  refine ⟨20079077492571159004902611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13386051661714106003268407 20079077492571159004902611)
  ·
    refine ⟨30118616238856738507353917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20079077492571159004902611 30118616238856738507353917)
    ·
      refine ⟨11294481089571276940257719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30118616238856738507353917 11294481089571276940257719)
      ·
        refine ⟨16941721634356915410386579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11294481089571276940257719 16941721634356915410386579)
        ·
          refine ⟨25412582451535373115579869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16941721634356915410386579 25412582451535373115579869)
          ·
            refine ⟨9529718419325764918342451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25412582451535373115579869 9529718419325764918342451)
            ·
              refine ⟨14294577628988647377513677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9529718419325764918342451 14294577628988647377513677)
              ·
                refine ⟨5360466610870742766567629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14294577628988647377513677 5360466610870742766567629)
                ·
                  refine ⟨2010174979076528537462861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5360466610870742766567629 2010174979076528537462861)
                  ·
                    refine ⟨753815617153698201548573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2010174979076528537462861 753815617153698201548573)
                    ·
                      refine ⟨282680856432636825580715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 753815617153698201548573 282680856432636825580715)
                      ·
                        rfl

theorem cell23_550519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 3, 3].length) (baseStart_550519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550519 prefixEnd_550519 := by exact prefixLift 550519
  have htrace : WordTrace (prefixWord ++ tailWord_550519) baseStart_550519 baseEnd_550519 := by
    simpa [prefixWord, tailWord_550519, baseEnd_550519] using wordTrace_append hprefix tailTrace_550519
  have hstable : (prefixWord ++ tailWord_550519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550519).length < 2 ^ (prefixWord ++ tailWord_550519).sum := by decide
  have hdescent : baseEnd_550519 < baseStart_550519 := by decide
  rcases family_descends (prefixWord ++ tailWord_550519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550576 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 3, 4, 2]
def baseStart_550576 : Nat := 118140960795 + 550576 * 2 ^ 59
def prefixEnd_550576 : Nat := 4983230072969 + 3 ^ 40 * 550576 * 2
def baseEnd_550576 : Nat := 282710124829943102567953

theorem tailTrace_550576 : CollatzResearch.WordTrace tailWord_550576 prefixEnd_550576 282710124829943102567953 := by
  unfold tailWord_550576
  simp only [CollatzResearch.WordTrace]
  refine ⟨10040578226682328869863791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13387437635576438493151721 10040578226682328869863791)
  ·
    refine ⟨15060867340023493304795687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10040578226682328869863791 15060867340023493304795687)
    ·
      refine ⟨22591301010035239957193531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15060867340023493304795687 22591301010035239957193531)
      ·
        refine ⟨33886951515052859935790297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22591301010035239957193531 33886951515052859935790297)
        ·
          refine ⟨25415213636289644951842723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33886951515052859935790297 25415213636289644951842723)
          ·
            refine ⟨38122820454434467427764085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25415213636289644951842723 38122820454434467427764085)
            ·
              refine ⟨3574014417603231321352883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38122820454434467427764085 3574014417603231321352883)
              ·
                refine ⟨5361021626404846982029325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3574014417603231321352883 5361021626404846982029325)
                ·
                  refine ⟨2010383109901817618260997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5361021626404846982029325 2010383109901817618260997)
                  ·
                    refine ⟨376946833106590803423937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2010383109901817618260997 376946833106590803423937)
                    ·
                      refine ⟨282710124829943102567953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 376946833106590803423937 282710124829943102567953)
                      ·
                        rfl

theorem cell23_550576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 3, 4, 2].length) (baseStart_550576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550576 prefixEnd_550576 := by exact prefixLift 550576
  have htrace : WordTrace (prefixWord ++ tailWord_550576) baseStart_550576 baseEnd_550576 := by
    simpa [prefixWord, tailWord_550576, baseEnd_550576] using wordTrace_append hprefix tailTrace_550576
  have hstable : (prefixWord ++ tailWord_550576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550576).length < 2 ^ (prefixWord ++ tailWord_550576).sum := by decide
  have hdescent : baseEnd_550576 < baseStart_550576 := by decide
  rcases family_descends (prefixWord ++ tailWord_550576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550579 : List Nat := [1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 5]
def baseStart_550579 : Nat := 118140960795 + 550579 * 2 ^ 59
def prefixEnd_550579 : Nat := 4983230072969 + 3 ^ 40 * 550579 * 2
def baseEnd_550579 : Nat := 282711665271906590830439

theorem tailTrace_550579 : CollatzResearch.WordTrace tailWord_550579 prefixEnd_550579 282711665271906590830439 := by
  unfold tailWord_550579
  simp only [CollatzResearch.WordTrace]
  refine ⟨20081265872353789252086791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13387510581569192834724527 20081265872353789252086791)
  ·
    refine ⟨30121898808530683878130187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20081265872353789252086791 30121898808530683878130187)
    ·
      refine ⟨45182848212796025817195281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30121898808530683878130187 45182848212796025817195281)
      ·
        refine ⟨33887136159597019362896461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45182848212796025817195281 33887136159597019362896461)
        ·
          refine ⟨12707676059848882261086173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33887136159597019362896461 12707676059848882261086173)
          ·
            refine ⟨4765378522443330847907315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12707676059848882261086173 4765378522443330847907315)
            ·
              refine ⟨7148067783664996271860973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4765378522443330847907315 7148067783664996271860973)
              ·
                refine ⟨2680525418874373601947865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7148067783664996271860973 2680525418874373601947865)
                ·
                  refine ⟨2010394064155780201460899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2680525418874373601947865 2010394064155780201460899)
                  ·
                    refine ⟨3015591096233670302191349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2010394064155780201460899 3015591096233670302191349)
                    ·
                      refine ⟨282711665271906590830439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3015591096233670302191349 282711665271906590830439)
                      ·
                        rfl

theorem cell23_550579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 5].length) (baseStart_550579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550579 prefixEnd_550579 := by exact prefixLift 550579
  have htrace : WordTrace (prefixWord ++ tailWord_550579) baseStart_550579 baseEnd_550579 := by
    simpa [prefixWord, tailWord_550579, baseEnd_550579] using wordTrace_append hprefix tailTrace_550579
  have hstable : (prefixWord ++ tailWord_550579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550579).length < 2 ^ (prefixWord ++ tailWord_550579).sum := by decide
  have hdescent : baseEnd_550579 < baseStart_550579 := by decide
  rcases family_descends (prefixWord ++ tailWord_550579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550596 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 1, 6, 3]
def baseStart_550596 : Nat := 118140960795 + 550596 * 2 ^ 59
def prefixEnd_550596 : Nat := 4983230072969 + 3 ^ 40 * 550596 * 2
def baseEnd_550596 : Nat := 282720394443033024317861

theorem tailTrace_550596 : CollatzResearch.WordTrace tailWord_550596 prefixEnd_550596 282720394443033024317861 := by
  unfold tailWord_550596
  simp only [CollatzResearch.WordTrace]
  refine ⟨10040942956646100577727821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13387923942194800770303761 10040942956646100577727821)
  ·
    refine ⟨3765353608742287716647933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10040942956646100577727821 3765353608742287716647933)
    ·
      refine ⟨1412007603278357893742975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3765353608742287716647933 1412007603278357893742975)
      ·
        refine ⟨2118011404917536840614463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1412007603278357893742975 2118011404917536840614463)
        ·
          refine ⟨3177017107376305260921695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2118011404917536840614463 3177017107376305260921695)
          ·
            refine ⟨4765525661064457891382543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3177017107376305260921695 4765525661064457891382543)
            ·
              refine ⟨7148288491596686837073815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4765525661064457891382543 7148288491596686837073815)
              ·
                refine ⟨10722432737395030255610723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7148288491596686837073815 10722432737395030255610723)
                ·
                  refine ⟨16083649106092545383416085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10722432737395030255610723 16083649106092545383416085)
                  ·
                    refine ⟨753921051848088064847629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16083649106092545383416085 753921051848088064847629)
                    ·
                      refine ⟨282720394443033024317861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 753921051848088064847629 282720394443033024317861)
                      ·
                        rfl

theorem cell23_550596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_550596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550596 prefixEnd_550596 := by exact prefixLift 550596
  have htrace : WordTrace (prefixWord ++ tailWord_550596) baseStart_550596 baseEnd_550596 := by
    simpa [prefixWord, tailWord_550596, baseEnd_550596] using wordTrace_append hprefix tailTrace_550596
  have hstable : (prefixWord ++ tailWord_550596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550596).length < 2 ^ (prefixWord ++ tailWord_550596).sum := by decide
  have hdescent : baseEnd_550596 < baseStart_550596 := by decide
  rcases family_descends (prefixWord ++ tailWord_550596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550599 : List Nat := [1, 1, 4, 1, 1, 1, 4, 3, 7]
def baseStart_550599 : Nat := 118140960795 + 550599 * 2 ^ 59
def prefixEnd_550599 : Nat := 4983230072969 + 3 ^ 40 * 550599 * 2
def baseEnd_550599 : Nat := 31413548320555168064483

theorem tailTrace_550599 : CollatzResearch.WordTrace tailWord_550599 prefixEnd_550599 31413548320555168064483 := by
  unfold tailWord_550599
  simp only [CollatzResearch.WordTrace]
  refine ⟨20081995332281332667814851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13387996888187555111876567 20081995332281332667814851)
  ·
    refine ⟨30122992998421999001722277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20081995332281332667814851 30122992998421999001722277)
    ·
      refine ⟨5648061187204124812822927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30122992998421999001722277 5648061187204124812822927)
      ·
        refine ⟨8472091780806187219234391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5648061187204124812822927 8472091780806187219234391)
        ·
          refine ⟨12708137671209280828851587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8472091780806187219234391 12708137671209280828851587)
          ·
            refine ⟨19062206506813921243277381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12708137671209280828851587 19062206506813921243277381)
            ·
              refine ⟨3574163720027610233114509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19062206506813921243277381 3574163720027610233114509)
              ·
                refine ⟨1340311395010353837417941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3574163720027610233114509 1340311395010353837417941)
                ·
                  refine ⟨31413548320555168064483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1340311395010353837417941 31413548320555168064483)
                  ·
                    rfl

theorem cell23_550599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 7].length) (baseStart_550599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550599 prefixEnd_550599 := by exact prefixLift 550599
  have htrace : WordTrace (prefixWord ++ tailWord_550599) baseStart_550599 baseEnd_550599 := by
    simpa [prefixWord, tailWord_550599, baseEnd_550599] using wordTrace_append hprefix tailTrace_550599
  have hstable : (prefixWord ++ tailWord_550599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550599).length < 2 ^ (prefixWord ++ tailWord_550599).sum := by decide
  have hdescent : baseEnd_550599 < baseStart_550599 := by decide
  rcases family_descends (prefixWord ++ tailWord_550599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550606 : List Nat := [4, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4]
def baseStart_550606 : Nat := 118140960795 + 550606 * 2 ^ 59
def prefixEnd_550606 : Nat := 4983230072969 + 3 ^ 40 * 550606 * 2
def baseEnd_550606 : Nat := 282725529249577985192815

theorem tailTrace_550606 : CollatzResearch.WordTrace tailWord_550606 prefixEnd_550606 282725529249577985192815 := by
  unfold tailWord_550606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2510281330406996607914959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13388167095503981908879781 2510281330406996607914959)
  ·
    refine ⟨3765421995610494911872439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2510281330406996607914959 3765421995610494911872439)
    ·
      refine ⟨5648132993415742367808659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3765421995610494911872439 5648132993415742367808659)
      ·
        refine ⟨8472199490123613551712989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5648132993415742367808659 8472199490123613551712989)
        ·
          refine ⟨3177074808796355081892371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8472199490123613551712989 3177074808796355081892371)
          ·
            refine ⟨4765612213194532622838557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3177074808796355081892371 4765612213194532622838557)
            ·
              refine ⟨1787104579947949733564459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4765612213194532622838557 1787104579947949733564459)
              ·
                refine ⟨2680656869921924600346689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1787104579947949733564459 2680656869921924600346689)
                ·
                  refine ⟨2010492652441443450260017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2680656869921924600346689 2010492652441443450260017)
                  ·
                    refine ⟨1507869489331082587695013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2010492652441443450260017 1507869489331082587695013)
                    ·
                      refine ⟨282725529249577985192815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1507869489331082587695013 282725529249577985192815)
                      ·
                        rfl

theorem cell23_550606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_550606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550606 prefixEnd_550606 := by exact prefixLift 550606
  have htrace : WordTrace (prefixWord ++ tailWord_550606) baseStart_550606 baseEnd_550606 := by
    simpa [prefixWord, tailWord_550606, baseEnd_550606] using wordTrace_append hprefix tailTrace_550606
  have hstable : (prefixWord ++ tailWord_550606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550606).length < 2 ^ (prefixWord ++ tailWord_550606).sum := by decide
  have hdescent : baseEnd_550606 < baseStart_550606 := by decide
  rcases family_descends (prefixWord ++ tailWord_550606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550610 : List Nat := [3, 2, 2, 2, 2, 2, 2, 1, 1, 4, 2]
def baseStart_550610 : Nat := 118140960795 + 550610 * 2 ^ 59
def prefixEnd_550610 : Nat := 4983230072969 + 3 ^ 40 * 550610 * 2
def baseEnd_550610 : Nat := 282727583172195969542797

theorem tailTrace_550610 : CollatzResearch.WordTrace tailWord_550610 prefixEnd_550610 282727583172195969542797 := by
  unfold tailWord_550610
  simp only [CollatzResearch.WordTrace]
  refine ⟨5020599133810370386616321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13388264356827654364310189 5020599133810370386616321)
  ·
    refine ⟨3765449350357777789962241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5020599133810370386616321 3765449350357777789962241)
    ·
      refine ⟨2824087012768333342471681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3765449350357777789962241 2824087012768333342471681)
      ·
        refine ⟨2118065259576250006853761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2824087012768333342471681 2118065259576250006853761)
        ·
          refine ⟨1588548944682187505140321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2118065259576250006853761 1588548944682187505140321)
          ·
            refine ⟨1191411708511640628855241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1588548944682187505140321 1191411708511640628855241)
            ·
              refine ⟨893558781383730471641431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1191411708511640628855241 893558781383730471641431)
              ·
                refine ⟨1340338172075595707462147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 893558781383730471641431 1340338172075595707462147)
                ·
                  refine ⟨2010507258113393561193221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1340338172075595707462147 2010507258113393561193221)
                  ·
                    refine ⟨376970110896261292723729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2010507258113393561193221 376970110896261292723729)
                    ·
                      refine ⟨282727583172195969542797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 376970110896261292723729 282727583172195969542797)
                      ·
                        rfl

theorem cell23_550610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_550610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550610 prefixEnd_550610 := by exact prefixLift 550610
  have htrace : WordTrace (prefixWord ++ tailWord_550610) baseStart_550610 baseEnd_550610 := by
    simpa [prefixWord, tailWord_550610, baseEnd_550610] using wordTrace_append hprefix tailTrace_550610
  have hstable : (prefixWord ++ tailWord_550610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550610).length < 2 ^ (prefixWord ++ tailWord_550610).sum := by decide
  have hdescent : baseEnd_550610 < baseStart_550610 := by decide
  rcases family_descends (prefixWord ++ tailWord_550610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550631 : List Nat := [1, 1, 5, 4, 2, 1, 2, 1, 1, 3, 2]
def baseStart_550631 : Nat := 118140960795 + 550631 * 2 ^ 59
def prefixEnd_550631 : Nat := 4983230072969 + 3 ^ 40 * 550631 * 2
def baseEnd_550631 : Nat := 282738366265940387380201

theorem tailTrace_550631 : CollatzResearch.WordTrace tailWord_550631 prefixEnd_550631 282738366265940387380201 := by
  unfold tailWord_550631
  simp only [CollatzResearch.WordTrace]
  refine ⟨20083162468165402132979747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13388774978776934755319831 20083162468165402132979747)
  ·
    refine ⟨30124743702248103199469621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20083162468165402132979747 30124743702248103199469621)
    ·
      refine ⟨2824194722085759674950277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30124743702248103199469621 2824194722085759674950277)
      ·
        refine ⟨529536510391079939053177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2824194722085759674950277 529536510391079939053177)
        ·
          refine ⟨397152382793309954289883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 529536510391079939053177 397152382793309954289883)
          ·
            refine ⟨595728574189964931434825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397152382793309954289883 595728574189964931434825)
            ·
              refine ⟨446796430642473698576119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 595728574189964931434825 446796430642473698576119)
              ·
                refine ⟨670194645963710547864179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 446796430642473698576119 670194645963710547864179)
                ·
                  refine ⟨1005291968945565821796269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 670194645963710547864179 1005291968945565821796269)
                  ·
                    refine ⟨376984488354587183173601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1005291968945565821796269 376984488354587183173601)
                    ·
                      refine ⟨282738366265940387380201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 376984488354587183173601 282738366265940387380201)
                      ·
                        rfl

theorem cell23_550631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_550631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550631 prefixEnd_550631 := by exact prefixLift 550631
  have htrace : WordTrace (prefixWord ++ tailWord_550631) baseStart_550631 baseEnd_550631 := by
    simpa [prefixWord, tailWord_550631, baseEnd_550631] using wordTrace_append hprefix tailTrace_550631
  have hstable : (prefixWord ++ tailWord_550631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550631).length < 2 ^ (prefixWord ++ tailWord_550631).sum := by decide
  have hdescent : baseEnd_550631 < baseStart_550631 := by decide
  rcases family_descends (prefixWord ++ tailWord_550631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550644 : List Nat := [2, 6, 1, 1, 1, 2, 1, 1, 4, 2, 2]
def baseStart_550644 : Nat := 118140960795 + 550644 * 2 ^ 59
def prefixEnd_550644 : Nat := 4983230072969 + 3 ^ 40 * 550644 * 2
def baseEnd_550644 : Nat := 282745041514448836517641

theorem tailTrace_550644 : CollatzResearch.WordTrace tailWord_550644 prefixEnd_550644 282745041514448836517641 := by
  unfold tailWord_550644
  simp only [CollatzResearch.WordTrace]
  refine ⟨10041818308559152676601493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13389091078078870235468657 10041818308559152676601493)
  ·
    refine ⟨470710233213710281715695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10041818308559152676601493 470710233213710281715695)
    ·
      refine ⟨706065349820565422573543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 470710233213710281715695 706065349820565422573543)
      ·
        refine ⟨1059098024730848133860315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 706065349820565422573543 1059098024730848133860315)
        ·
          refine ⟨1588647037096272200790473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1059098024730848133860315 1588647037096272200790473)
          ·
            refine ⟨1191485277822204150592855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1588647037096272200790473 1191485277822204150592855)
            ·
              refine ⟨1787227916733306225889283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1191485277822204150592855 1787227916733306225889283)
              ·
                refine ⟨2680841875099959338833925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1787227916733306225889283 2680841875099959338833925)
                ·
                  refine ⟨502657851581242376031361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2680841875099959338833925 502657851581242376031361)
                  ·
                    refine ⟨376993388685931782023521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 502657851581242376031361 376993388685931782023521)
                    ·
                      refine ⟨282745041514448836517641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 376993388685931782023521 282745041514448836517641)
                      ·
                        rfl

theorem cell23_550644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_550644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550644 prefixEnd_550644 := by exact prefixLift 550644
  have htrace : WordTrace (prefixWord ++ tailWord_550644) baseStart_550644 baseEnd_550644 := by
    simpa [prefixWord, tailWord_550644, baseEnd_550644] using wordTrace_append hprefix tailTrace_550644
  have hstable : (prefixWord ++ tailWord_550644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550644).length < 2 ^ (prefixWord ++ tailWord_550644).sum := by decide
  have hdescent : baseEnd_550644 < baseStart_550644 := by decide
  rcases family_descends (prefixWord ++ tailWord_550644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550666 : List Nat := [3, 1, 2, 2, 1, 3, 1, 2, 1, 3, 4]
def baseStart_550666 : Nat := 118140960795 + 550666 * 2 ^ 59
def prefixEnd_550666 : Nat := 4983230072969 + 3 ^ 40 * 550666 * 2
def baseEnd_550666 : Nat := 282756338088847750442539

theorem tailTrace_550666 : CollatzResearch.WordTrace tailWord_550666 prefixEnd_550666 282756338088847750442539 := by
  unfold tailWord_550666
  simp only [CollatzResearch.WordTrace]
  refine ⟨5021109755759650777625963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13389626015359068740335901 5021109755759650777625963)
  ·
    refine ⟨7531664633639476166438945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5021109755759650777625963 7531664633639476166438945)
    ·
      refine ⟨5648748475229607124829209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7531664633639476166438945 5648748475229607124829209)
      ·
        refine ⟨4236561356422205343621907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5648748475229607124829209 4236561356422205343621907)
        ·
          refine ⟨6354842034633308015432861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4236561356422205343621907 6354842034633308015432861)
          ·
            refine ⟨2383065762987490505787323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6354842034633308015432861 2383065762987490505787323)
            ·
              refine ⟨3574598644481235758680985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2383065762987490505787323 3574598644481235758680985)
              ·
                refine ⟨2680948983360926819010739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3574598644481235758680985 2680948983360926819010739)
                ·
                  refine ⟨4021423475041390228516109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2680948983360926819010739 4021423475041390228516109)
                  ·
                    refine ⟨1508033803140521335693541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4021423475041390228516109 1508033803140521335693541)
                    ·
                      refine ⟨282756338088847750442539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1508033803140521335693541 282756338088847750442539)
                      ·
                        rfl

theorem cell23_550666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_550666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550666 prefixEnd_550666 := by exact prefixLift 550666
  have htrace : WordTrace (prefixWord ++ tailWord_550666) baseStart_550666 baseEnd_550666 := by
    simpa [prefixWord, tailWord_550666, baseEnd_550666] using wordTrace_append hprefix tailTrace_550666
  have hstable : (prefixWord ++ tailWord_550666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550666).length < 2 ^ (prefixWord ++ tailWord_550666).sum := by decide
  have hdescent : baseEnd_550666 < baseStart_550666 := by decide
  rcases family_descends (prefixWord ++ tailWord_550666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550706 : List Nat := [3, 2, 1, 1, 3, 2, 2, 1, 8]
def baseStart_550706 : Nat := 118140960795 + 550706 * 2 ^ 59
def prefixEnd_550706 : Nat := 4983230072969 + 3 ^ 40 * 550706 * 2
def baseEnd_550706 : Nat := 31419653035003065993595

theorem tailTrace_550706 : CollatzResearch.WordTrace tailWord_550706 prefixEnd_550706 31419653035003065993595 := by
  unfold tailWord_550706
  simp only [CollatzResearch.WordTrace]
  refine ⟨5021474485723422485489993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13390598628595793294639981 5021474485723422485489993)
  ·
    refine ⟨3766105864292566864117495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5021474485723422485489993 3766105864292566864117495)
    ·
      refine ⟨5649158796438850296176243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3766105864292566864117495 5649158796438850296176243)
      ·
        refine ⟨8473738194658275444264365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5649158796438850296176243 8473738194658275444264365)
        ·
          refine ⟨3177651822996853291599137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8473738194658275444264365 3177651822996853291599137)
          ·
            refine ⟨2383238867247639968699353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3177651822996853291599137 2383238867247639968699353)
            ·
              refine ⟨1787429150435729976524515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2383238867247639968699353 1787429150435729976524515)
              ·
                refine ⟨2681143725653594964786773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1787429150435729976524515 2681143725653594964786773)
                ·
                  refine ⟨31419653035003065993595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2681143725653594964786773 31419653035003065993595)
                  ·
                    rfl

theorem cell23_550706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 8].length) (baseStart_550706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550706 prefixEnd_550706 := by exact prefixLift 550706
  have htrace : WordTrace (prefixWord ++ tailWord_550706) baseStart_550706 baseEnd_550706 := by
    simpa [prefixWord, tailWord_550706, baseEnd_550706] using wordTrace_append hprefix tailTrace_550706
  have hstable : (prefixWord ++ tailWord_550706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550706).length < 2 ^ (prefixWord ++ tailWord_550706).sum := by decide
  have hdescent : baseEnd_550706 < baseStart_550706 := by decide
  rcases family_descends (prefixWord ++ tailWord_550706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550723 : List Nat := [1, 1, 1, 3, 1, 5, 4, 1, 6]
def baseStart_550723 : Nat := 118140960795 + 550723 * 2 ^ 59
def prefixEnd_550723 : Nat := 4983230072969 + 3 ^ 40 * 550723 * 2
def baseEnd_550723 : Nat := 31420622942906003047753

theorem tailTrace_550723 : CollatzResearch.WordTrace tailWord_550723 prefixEnd_550723 31420622942906003047753 := by
  unfold tailWord_550723
  simp only [CollatzResearch.WordTrace]
  refine ⟨20086517983832101845328823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13391011989221401230219215 20086517983832101845328823)
  ·
    refine ⟨30129776975748152767993235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20086517983832101845328823 30129776975748152767993235)
    ·
      refine ⟨45194665463622229151989853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30129776975748152767993235 45194665463622229151989853)
      ·
        refine ⟨16947999548858335931996195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45194665463622229151989853 16947999548858335931996195)
        ·
          refine ⟨25421999323287503897994293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16947999548858335931996195 25421999323287503897994293)
          ·
            refine ⟨2383312436558203490436965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25421999323287503897994293 2383312436558203490436965)
            ·
              refine ⟨446871081854663154456931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2383312436558203490436965 446871081854663154456931)
              ·
                refine ⟨670306622781994731685397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 446871081854663154456931 670306622781994731685397)
                ·
                  refine ⟨31420622942906003047753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 670306622781994731685397 31420622942906003047753)
                  ·
                    rfl

theorem cell23_550723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 6].length) (baseStart_550723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550723 prefixEnd_550723 := by exact prefixLift 550723
  have htrace : WordTrace (prefixWord ++ tailWord_550723) baseStart_550723 baseEnd_550723 := by
    simpa [prefixWord, tailWord_550723, baseEnd_550723] using wordTrace_append hprefix tailTrace_550723
  have hstable : (prefixWord ++ tailWord_550723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550723).length < 2 ^ (prefixWord ++ tailWord_550723).sum := by decide
  have hdescent : baseEnd_550723 < baseStart_550723 := by decide
  rcases family_descends (prefixWord ++ tailWord_550723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550760 : List Nat := [2, 1, 4, 2, 1, 1, 1, 4, 2, 3, 2]
def baseStart_550760 : Nat := 118140960795 + 550760 * 2 ^ 59
def prefixEnd_550760 : Nat := 4983230072969 + 3 ^ 40 * 550760 * 2
def baseEnd_550760 : Nat := 282804605270370382667107

theorem tailTrace_550760 : CollatzResearch.WordTrace tailWord_550760 prefixEnd_550760 282804605270370382667107 := by
  unfold tailWord_550760
  simp only [CollatzResearch.WordTrace]
  refine ⟨10043933742349028582212867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13391911656465371442950489 10043933742349028582212867)
  ·
    refine ⟨15065900613523542873319301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10043933742349028582212867 15065900613523542873319301)
    ·
      refine ⟨2824856365035664288747369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15065900613523542873319301 2824856365035664288747369)
      ·
        refine ⟨2118642273776748216560527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2824856365035664288747369 2118642273776748216560527)
        ·
          refine ⟨3177963410665122324840791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2118642273776748216560527 3177963410665122324840791)
          ·
            refine ⟨4766945115997683487261187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3177963410665122324840791 4766945115997683487261187)
            ·
              refine ⟨7150417673996525230891781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4766945115997683487261187 7150417673996525230891781)
              ·
                refine ⟨1340703313874348480792209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7150417673996525230891781 1340703313874348480792209)
                ·
                  refine ⟨1005527485405761360594157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1340703313874348480792209 1005527485405761360594157)
                  ·
                    refine ⟨377072807027160510222809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1005527485405761360594157 377072807027160510222809)
                    ·
                      refine ⟨282804605270370382667107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 377072807027160510222809 282804605270370382667107)
                      ·
                        rfl

theorem cell23_550760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_550760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550760 prefixEnd_550760 := by exact prefixLift 550760
  have htrace : WordTrace (prefixWord ++ tailWord_550760) baseStart_550760 baseEnd_550760 := by
    simpa [prefixWord, tailWord_550760, baseEnd_550760] using wordTrace_append hprefix tailTrace_550760
  have hstable : (prefixWord ++ tailWord_550760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550760).length < 2 ^ (prefixWord ++ tailWord_550760).sum := by decide
  have hdescent : baseEnd_550760 < baseStart_550760 := by decide
  rcases family_descends (prefixWord ++ tailWord_550760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550773 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_550773 : Nat := 118140960795 + 550773 * 2 ^ 59
def prefixEnd_550773 : Nat := 4983230072969 + 3 ^ 40 * 550773 * 2
def baseEnd_550773 : Nat := 282811280518878831804547

theorem tailTrace_550773 : CollatzResearch.WordTrace tailWord_550773 prefixEnd_550773 282811280518878831804547 := by
  unfold tailWord_550773
  simp only [CollatzResearch.WordTrace]
  refine ⟨20088341633650960384648973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13392227755767306923099315 20088341633650960384648973)
  ·
    refine ⟨7533128112619110144243365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20088341633650960384648973 7533128112619110144243365)
    ·
      refine ⟨1412461521116083152045631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7533128112619110144243365 1412461521116083152045631)
      ·
        refine ⟨2118692281674124728068447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1412461521116083152045631 2118692281674124728068447)
        ·
          refine ⟨3178038422511187092102671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2118692281674124728068447 3178038422511187092102671)
          ·
            refine ⟨4767057633766780638154007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3178038422511187092102671 4767057633766780638154007)
            ·
              refine ⟨7150586450650170957231011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4767057633766780638154007 7150586450650170957231011)
              ·
                refine ⟨10725879675975256435846517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7150586450650170957231011 10725879675975256435846517)
                ·
                  refine ⟨1005551219622680290860611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10725879675975256435846517 1005551219622680290860611)
                  ·
                    refine ⟨1508326829434020436290917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1005551219622680290860611 1508326829434020436290917)
                    ·
                      refine ⟨282811280518878831804547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1508326829434020436290917 282811280518878831804547)
                      ·
                        rfl

theorem cell23_550773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_550773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550773 prefixEnd_550773 := by exact prefixLift 550773
  have htrace : WordTrace (prefixWord ++ tailWord_550773) baseStart_550773 baseEnd_550773 := by
    simpa [prefixWord, tailWord_550773, baseEnd_550773] using wordTrace_append hprefix tailTrace_550773
  have hstable : (prefixWord ++ tailWord_550773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550773).length < 2 ^ (prefixWord ++ tailWord_550773).sum := by decide
  have hdescent : baseEnd_550773 < baseStart_550773 := by decide
  rcases family_descends (prefixWord ++ tailWord_550773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550793 : List Nat := [1, 2, 1, 1, 5, 1, 1, 3, 3, 2, 3]
def baseStart_550793 : Nat := 118140960795 + 550793 * 2 ^ 59
def prefixEnd_550793 : Nat := 4983230072969 + 3 ^ 40 * 550793 * 2
def baseEnd_550793 : Nat := 282821550131968753554455

theorem tailTrace_550793 : CollatzResearch.WordTrace tailWord_550793 prefixEnd_550793 282821550131968753554455 := by
  unfold tailWord_550793
  simp only [CollatzResearch.WordTrace]
  refine ⟨20089071093578503800377033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13392714062385669200251355 20089071093578503800377033)
  ·
    refine ⟨15066803320183877850282775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20089071093578503800377033 15066803320183877850282775)
    ·
      refine ⟨22600204980275816775424163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15066803320183877850282775 22600204980275816775424163)
      ·
        refine ⟨33900307470413725163136245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22600204980275816775424163 33900307470413725163136245)
        ·
          refine ⟨3178153825351286734044023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33900307470413725163136245 3178153825351286734044023)
          ·
            refine ⟨4767230738026930101066035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3178153825351286734044023 4767230738026930101066035)
            ·
              refine ⟨7150846107040395151599053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4767230738026930101066035 7150846107040395151599053)
              ·
                refine ⟨2681567290140148181849645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7150846107040395151599053 2681567290140148181849645)
                ·
                  refine ⟨1005587733802555568193617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2681567290140148181849645 1005587733802555568193617)
                  ·
                    refine ⟨754190800351916676145213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1005587733802555568193617 754190800351916676145213)
                    ·
                      refine ⟨282821550131968753554455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 754190800351916676145213 282821550131968753554455)
                      ·
                        rfl

theorem cell23_550793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 2, 3].length) (baseStart_550793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550793 prefixEnd_550793 := by exact prefixLift 550793
  have htrace : WordTrace (prefixWord ++ tailWord_550793) baseStart_550793 baseEnd_550793 := by
    simpa [prefixWord, tailWord_550793, baseEnd_550793] using wordTrace_append hprefix tailTrace_550793
  have hstable : (prefixWord ++ tailWord_550793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550793).length < 2 ^ (prefixWord ++ tailWord_550793).sum := by decide
  have hdescent : baseEnd_550793 < baseStart_550793 := by decide
  rcases family_descends (prefixWord ++ tailWord_550793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550794 : List Nat := [3, 1, 2, 4, 2, 2, 1, 1, 2, 3, 2]
def baseStart_550794 : Nat := 118140960795 + 550794 * 2 ^ 59
def prefixEnd_550794 : Nat := 4983230072969 + 3 ^ 40 * 550794 * 2
def baseEnd_550794 : Nat := 282822063612623249641951

theorem tailTrace_550794 : CollatzResearch.WordTrace tailWord_550794 prefixEnd_550794 282822063612623249641951 := by
  unfold tailWord_550794
  simp only [CollatzResearch.WordTrace]
  refine ⟨5022276891643720242790859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13392738377716587314108957 5022276891643720242790859)
  ·
    refine ⟨7533415337465580364186289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5022276891643720242790859 7533415337465580364186289)
    ·
      refine ⟨5650061503099185273139717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7533415337465580364186289 5650061503099185273139717)
      ·
        refine ⟨1059386531831097238713697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5650061503099185273139717 1059386531831097238713697)
        ·
          refine ⟨794539898873322929035273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1059386531831097238713697 794539898873322929035273)
          ·
            refine ⟨595904924154992196776455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 794539898873322929035273 595904924154992196776455)
            ·
              refine ⟨893857386232488295164683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595904924154992196776455 893857386232488295164683)
              ·
                refine ⟨1340786079348732442747025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 893857386232488295164683 1340786079348732442747025)
                ·
                  refine ⟨1005589559511549332060269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1340786079348732442747025 1005589559511549332060269)
                  ·
                    refine ⟨377096084816830999522601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1005589559511549332060269 377096084816830999522601)
                    ·
                      refine ⟨282822063612623249641951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 377096084816830999522601 282822063612623249641951)
                      ·
                        rfl

theorem cell23_550794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_550794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550794 prefixEnd_550794 := by exact prefixLift 550794
  have htrace : WordTrace (prefixWord ++ tailWord_550794) baseStart_550794 baseEnd_550794 := by
    simpa [prefixWord, tailWord_550794, baseEnd_550794] using wordTrace_append hprefix tailTrace_550794
  have hstable : (prefixWord ++ tailWord_550794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550794).length < 2 ^ (prefixWord ++ tailWord_550794).sum := by decide
  have hdescent : baseEnd_550794 < baseStart_550794 := by decide
  rcases family_descends (prefixWord ++ tailWord_550794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550807 : List Nat := [1, 1, 3, 3, 1, 5, 2, 1, 1, 1, 4]
def baseStart_550807 : Nat := 118140960795 + 550807 * 2 ^ 59
def prefixEnd_550807 : Nat := 4983230072969 + 3 ^ 40 * 550807 * 2
def baseEnd_550807 : Nat := 282828738861131698779391

theorem tailTrace_550807 : CollatzResearch.WordTrace tailWord_550807 prefixEnd_550807 282828738861131698779391 := by
  unfold tailWord_550807
  simp only [CollatzResearch.WordTrace]
  refine ⟨20089581715527784191386675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13393054477018522794257783 20089581715527784191386675)
  ·
    refine ⟨30134372573291676287080013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20089581715527784191386675 30134372573291676287080013)
    ·
      refine ⟨11300389714984378607655005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30134372573291676287080013 11300389714984378607655005)
      ·
        refine ⟨4237646143119141977870627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11300389714984378607655005 4237646143119141977870627)
        ·
          refine ⟨6356469214678712966805941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4237646143119141977870627 6356469214678712966805941)
          ·
            refine ⟨595918988876129340638057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6356469214678712966805941 595918988876129340638057)
            ·
              refine ⟨446939241657097005478543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 595918988876129340638057 446939241657097005478543)
              ·
                refine ⟨670408862485645508217815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 446939241657097005478543 670408862485645508217815)
                ·
                  refine ⟨1005613293728468262326723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 670408862485645508217815 1005613293728468262326723)
                  ·
                    refine ⟨1508419940592702393490085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1005613293728468262326723 1508419940592702393490085)
                    ·
                      refine ⟨282828738861131698779391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1508419940592702393490085 282828738861131698779391)
                      ·
                        rfl

theorem cell23_550807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_550807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550807 prefixEnd_550807 := by exact prefixLift 550807
  have htrace : WordTrace (prefixWord ++ tailWord_550807) baseStart_550807 baseEnd_550807 := by
    simpa [prefixWord, tailWord_550807, baseEnd_550807] using wordTrace_append hprefix tailTrace_550807
  have hstable : (prefixWord ++ tailWord_550807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550807).length < 2 ^ (prefixWord ++ tailWord_550807).sum := by decide
  have hdescent : baseEnd_550807 < baseStart_550807 := by decide
  rcases family_descends (prefixWord ++ tailWord_550807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550816 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 6]
def baseStart_550816 : Nat := 118140960795 + 550816 * 2 ^ 59
def prefixEnd_550816 : Nat := 4983230072969 + 3 ^ 40 * 550816 * 2
def baseEnd_550816 : Nat := 282833360187022163566849

theorem tailTrace_550816 : CollatzResearch.WordTrace tailWord_550816 prefixEnd_550816 282833360187022163566849 := by
  unfold tailWord_550816
  simp only [CollatzResearch.WordTrace]
  refine ⟨10044954986247589364232151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13393273314996785818976201 10044954986247589364232151)
  ·
    refine ⟨15067432479371384046348227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10044954986247589364232151 15067432479371384046348227)
    ·
      refine ⟨22601148719057076069522341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15067432479371384046348227 22601148719057076069522341)
      ·
        refine ⟨4237715384823201763035439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22601148719057076069522341 4237715384823201763035439)
        ·
          refine ⟨6356573077234802644553159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4237715384823201763035439 6356573077234802644553159)
          ·
            refine ⟨9534859615852203966829739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6356573077234802644553159 9534859615852203966829739)
            ·
              refine ⟨14302289423778305950244609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9534859615852203966829739 14302289423778305950244609)
              ·
                refine ⟨10726717067833729462683457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14302289423778305950244609 10726717067833729462683457)
                ·
                  refine ⟨8045037800875297097012593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10726717067833729462683457 8045037800875297097012593)
                  ·
                    refine ⟨6033778350656472822759445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8045037800875297097012593 6033778350656472822759445)
                    ·
                      refine ⟨282833360187022163566849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6033778350656472822759445 282833360187022163566849)
                      ·
                        rfl

theorem cell23_550816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_550816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550816 prefixEnd_550816 := by exact prefixLift 550816
  have htrace : WordTrace (prefixWord ++ tailWord_550816) baseStart_550816 baseEnd_550816 := by
    simpa [prefixWord, tailWord_550816, baseEnd_550816] using wordTrace_append hprefix tailTrace_550816
  have hstable : (prefixWord ++ tailWord_550816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550816).length < 2 ^ (prefixWord ++ tailWord_550816).sum := by decide
  have hdescent : baseEnd_550816 < baseStart_550816 := by decide
  rcases family_descends (prefixWord ++ tailWord_550816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550844 : List Nat := [2, 2, 2, 5, 1, 1, 2, 2, 1, 2, 3]
def baseStart_550844 : Nat := 118140960795 + 550844 * 2 ^ 59
def prefixEnd_550844 : Nat := 4983230072969 + 3 ^ 40 * 550844 * 2
def baseEnd_550844 : Nat := 282847737645348054016721

theorem tailTrace_550844 : CollatzResearch.WordTrace tailWord_550844 prefixEnd_550844 282847737645348054016721 := by
  unfold tailWord_550844
  simp only [CollatzResearch.WordTrace]
  refine ⟨10045465608196869755241793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13393954144262493006989057 10045465608196869755241793)
  ·
    refine ⟨7534099206147652316431345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10045465608196869755241793 7534099206147652316431345)
    ·
      refine ⟨5650574404610739237323509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7534099206147652316431345 5650574404610739237323509)
      ·
        refine ⟨529741350432256803499079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5650574404610739237323509 529741350432256803499079)
        ·
          refine ⟨794612025648385205248619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529741350432256803499079 794612025648385205248619)
          ·
            refine ⟨1191918038472577807872929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794612025648385205248619 1191918038472577807872929)
            ·
              refine ⟨893938528854433355904697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1191918038472577807872929 893938528854433355904697)
              ·
                refine ⟨670453896640825016928523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 893938528854433355904697 670453896640825016928523)
                ·
                  refine ⟨1005680844961237525392785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 670453896640825016928523 1005680844961237525392785)
                  ·
                    refine ⟨754260633720928144044589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1005680844961237525392785 754260633720928144044589)
                    ·
                      refine ⟨282847737645348054016721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 754260633720928144044589 282847737645348054016721)
                      ·
                        rfl

theorem cell23_550844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_550844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550844 prefixEnd_550844 := by exact prefixLift 550844
  have htrace : WordTrace (prefixWord ++ tailWord_550844) baseStart_550844 baseEnd_550844 := by
    simpa [prefixWord, tailWord_550844, baseEnd_550844] using wordTrace_append hprefix tailTrace_550844
  have hstable : (prefixWord ++ tailWord_550844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550844).length < 2 ^ (prefixWord ++ tailWord_550844).sum := by decide
  have hdescent : baseEnd_550844 < baseStart_550844 := by decide
  rcases family_descends (prefixWord ++ tailWord_550844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550920 : List Nat := [2, 1, 3, 2, 1, 2, 2, 5, 5]
def baseStart_550920 : Nat := 118140960795 + 550920 * 2 ^ 59
def prefixEnd_550920 : Nat := 4983230072969 + 3 ^ 40 * 550920 * 2
def baseEnd_550920 : Nat := 31431862463898861851819

theorem tailTrace_550920 : CollatzResearch.WordTrace tailWord_550920 prefixEnd_550920 31431862463898861851819 := by
  unfold tailWord_550920
  simp only [CollatzResearch.WordTrace]
  refine ⟨10046851582059202245125107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13395802109412269660166809 10046851582059202245125107)
  ·
    refine ⟨15070277373088803367687661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10046851582059202245125107 15070277373088803367687661)
    ·
      refine ⟨5651354014908301262882873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15070277373088803367687661 5651354014908301262882873)
      ·
        refine ⟨4238515511181225947162155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5651354014908301262882873 4238515511181225947162155)
        ·
          refine ⟨6357773266771838920743233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4238515511181225947162155 6357773266771838920743233)
          ·
            refine ⟨4768329950078879190557425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6357773266771838920743233 4768329950078879190557425)
            ·
              refine ⟨3576247462559159392918069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4768329950078879190557425 3576247462559159392918069)
              ·
                refine ⟨335273199614921193086069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3576247462559159392918069 335273199614921193086069)
                ·
                  refine ⟨31431862463898861851819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 335273199614921193086069 31431862463898861851819)
                  ·
                    rfl

theorem cell23_550920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 5, 5].length) (baseStart_550920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550920 prefixEnd_550920 := by exact prefixLift 550920
  have htrace : WordTrace (prefixWord ++ tailWord_550920) baseStart_550920 baseEnd_550920 := by
    simpa [prefixWord, tailWord_550920, baseEnd_550920] using wordTrace_append hprefix tailTrace_550920
  have hstable : (prefixWord ++ tailWord_550920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550920).length < 2 ^ (prefixWord ++ tailWord_550920).sum := by decide
  have hdescent : baseEnd_550920 < baseStart_550920 := by decide
  rcases family_descends (prefixWord ++ tailWord_550920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550943 : List Nat := [1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 5]
def baseStart_550943 : Nat := 118140960795 + 550943 * 2 ^ 59
def prefixEnd_550943 : Nat := 4983230072969 + 3 ^ 40 * 550943 * 2
def baseEnd_550943 : Nat := 282898572230143166678765

theorem tailTrace_550943 : CollatzResearch.WordTrace tailWord_550943 prefixEnd_550943 282898572230143166678765 := by
  unfold tailWord_550943
  simp only [CollatzResearch.WordTrace]
  refine ⟨20094542043035079418337483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13396361362023386278891655 20094542043035079418337483)
  ·
    refine ⟨30141813064552619127506225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20094542043035079418337483 30141813064552619127506225)
    ·
      refine ⟨22606359798414464345629669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30141813064552619127506225 22606359798414464345629669)
      ·
        refine ⟨4238692462202712064805563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22606359798414464345629669 4238692462202712064805563)
        ·
          refine ⟨6358038693304068097208345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4238692462202712064805563 6358038693304068097208345)
          ·
            refine ⟨4768529019978051072906259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6358038693304068097208345 4768529019978051072906259)
            ·
              refine ⟨7152793529967076609359389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4768529019978051072906259 7152793529967076609359389)
              ·
                refine ⟨2682297573737653728509771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7152793529967076609359389 2682297573737653728509771)
                ·
                  refine ⟨4023446360606480592764657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2682297573737653728509771 4023446360606480592764657)
                  ·
                    refine ⟨3017584770454860444573493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4023446360606480592764657 3017584770454860444573493)
                    ·
                      refine ⟨282898572230143166678765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3017584770454860444573493 282898572230143166678765)
                      ·
                        rfl

theorem cell23_550943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_550943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550943 prefixEnd_550943 := by exact prefixLift 550943
  have htrace : WordTrace (prefixWord ++ tailWord_550943) baseStart_550943 baseEnd_550943 := by
    simpa [prefixWord, tailWord_550943, baseEnd_550943] using wordTrace_append hprefix tailTrace_550943
  have hstable : (prefixWord ++ tailWord_550943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550943).length < 2 ^ (prefixWord ++ tailWord_550943).sum := by decide
  have hdescent : baseEnd_550943 < baseStart_550943 := by decide
  rcases family_descends (prefixWord ++ tailWord_550943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550970 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 3, 6, 2]
def baseStart_550970 : Nat := 118140960795 + 550970 * 2 ^ 59
def prefixEnd_550970 : Nat := 4983230072969 + 3 ^ 40 * 550970 * 2
def baseEnd_550970 : Nat := 282912436207814561041141

theorem tailTrace_550970 : CollatzResearch.WordTrace tailWord_550970 prefixEnd_550970 282912436207814561041141 := by
  unfold tailWord_550970
  simp only [CollatzResearch.WordTrace]
  refine ⟨5023881703484315757392591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13397017875958175353046909 5023881703484315757392591)
  ·
    refine ⟨7535822555226473636088887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5023881703484315757392591 7535822555226473636088887)
    ·
      refine ⟨11303733832839710454133331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7535822555226473636088887 11303733832839710454133331)
      ·
        refine ⟨16955600749259565681199997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11303733832839710454133331 16955600749259565681199997)
        ·
          refine ⟨6358350280972337130449999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16955600749259565681199997 6358350280972337130449999)
          ·
            refine ⟨9537525421458505695674999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6358350280972337130449999 9537525421458505695674999)
            ·
              refine ⟨14306288132187758543512499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9537525421458505695674999 14306288132187758543512499)
              ·
                refine ⟨21459432198281637815268749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14306288132187758543512499 21459432198281637815268749)
                ·
                  refine ⟨8047287074355614180725781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21459432198281637815268749 8047287074355614180725781)
                  ·
                    refine ⟨377216581610419414721521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8047287074355614180725781 377216581610419414721521)
                    ·
                      refine ⟨282912436207814561041141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 377216581610419414721521 282912436207814561041141)
                      ·
                        rfl

theorem cell23_550970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 6, 2].length) (baseStart_550970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550970 prefixEnd_550970 := by exact prefixLift 550970
  have htrace : WordTrace (prefixWord ++ tailWord_550970) baseStart_550970 baseEnd_550970 := by
    simpa [prefixWord, tailWord_550970, baseEnd_550970] using wordTrace_append hprefix tailTrace_550970
  have hstable : (prefixWord ++ tailWord_550970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550970).length < 2 ^ (prefixWord ++ tailWord_550970).sum := by decide
  have hdescent : baseEnd_550970 < baseStart_550970 := by decide
  rcases family_descends (prefixWord ++ tailWord_550970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550983 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 6]
def baseStart_550983 : Nat := 118140960795 + 550983 * 2 ^ 59
def prefixEnd_550983 : Nat := 4983230072969 + 3 ^ 40 * 550983 * 2
def baseEnd_550983 : Nat := 282919111456323010178581

theorem tailTrace_550983 : CollatzResearch.WordTrace tailWord_550983 prefixEnd_550983 282919111456323010178581 := by
  unfold tailWord_550983
  simp only [CollatzResearch.WordTrace]
  refine ⟨20096000962890166249793603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13397333975260110833195735 20096000962890166249793603)
  ·
    refine ⟨30144001444335249374690405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20096000962890166249793603 30144001444335249374690405)
    ·
      refine ⟨5652000270812859257754451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30144001444335249374690405 5652000270812859257754451)
      ·
        refine ⟨8478000406219288886631677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5652000270812859257754451 8478000406219288886631677)
        ·
          refine ⟨3179250152332233332486879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8478000406219288886631677 3179250152332233332486879)
          ·
            refine ⟨4768875228498349998730319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3179250152332233332486879 4768875228498349998730319)
            ·
              refine ⟨7153312842747524998095479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4768875228498349998730319 7153312842747524998095479)
              ·
                refine ⟨10729969264121287497143219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7153312842747524998095479 10729969264121287497143219)
                ·
                  refine ⟨16094953896181931245714829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10729969264121287497143219 16094953896181931245714829)
                  ·
                    refine ⟨6035607711068224217143061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16094953896181931245714829 6035607711068224217143061)
                    ·
                      refine ⟨282919111456323010178581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6035607711068224217143061 282919111456323010178581)
                      ·
                        rfl

theorem cell23_550983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_550983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550983 prefixEnd_550983 := by exact prefixLift 550983
  have htrace : WordTrace (prefixWord ++ tailWord_550983) baseStart_550983 baseEnd_550983 := by
    simpa [prefixWord, tailWord_550983, baseEnd_550983] using wordTrace_append hprefix tailTrace_550983
  have hstable : (prefixWord ++ tailWord_550983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550983).length < 2 ^ (prefixWord ++ tailWord_550983).sum := by decide
  have hdescent : baseEnd_550983 < baseStart_550983 := by decide
  rcases family_descends (prefixWord ++ tailWord_550983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550997 : List Nat := [1, 3, 2, 2, 1, 4, 2, 1, 3, 4]
def baseStart_550997 : Nat := 118140960795 + 550997 * 2 ^ 59
def prefixEnd_550997 : Nat := 4983230072969 + 3 ^ 40 * 550997 * 2
def baseEnd_550997 : Nat := 94308766728495318467839

theorem tailTrace_550997 : CollatzResearch.WordTrace tailWord_550997 prefixEnd_550997 94308766728495318467839 := by
  unfold tailWord_550997
  simp only [CollatzResearch.WordTrace]
  refine ⟨20096511584839446640803245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13397674389892964427202163 20096511584839446640803245)
  ·
    refine ⟨7536191844314792490301217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20096511584839446640803245 7536191844314792490301217)
    ·
      refine ⟨5652143883236094367725913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7536191844314792490301217 5652143883236094367725913)
      ·
        refine ⟨4239107912427070775794435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5652143883236094367725913 4239107912427070775794435)
        ·
          refine ⟨6358661868640606163691653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4239107912427070775794435 6358661868640606163691653)
          ·
            refine ⟨1192249100370113655692185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6358661868640606163691653 1192249100370113655692185)
            ·
              refine ⟨894186825277585241769139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1192249100370113655692185 894186825277585241769139)
              ·
                refine ⟨1341280237916377862653709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 894186825277585241769139 1341280237916377862653709)
                ·
                  refine ⟨502980089218641698495141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1341280237916377862653709 502980089218641698495141)
                  ·
                    refine ⟨94308766728495318467839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 502980089218641698495141 94308766728495318467839)
                    ·
                      rfl

theorem cell23_550997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_550997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_550997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_550997 prefixEnd_550997 := by exact prefixLift 550997
  have htrace : WordTrace (prefixWord ++ tailWord_550997) baseStart_550997 baseEnd_550997 := by
    simpa [prefixWord, tailWord_550997, baseEnd_550997] using wordTrace_append hprefix tailTrace_550997
  have hstable : (prefixWord ++ tailWord_550997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550997).length < 2 ^ (prefixWord ++ tailWord_550997).sum := by decide
  have hdescent : baseEnd_550997 < baseStart_550997 := by decide
  rcases family_descends (prefixWord ++ tailWord_550997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551047 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 4, 3, 2]
def baseStart_551047 : Nat := 118140960795 + 551047 * 2 ^ 59
def prefixEnd_551047 : Nat := 4983230072969 + 3 ^ 40 * 551047 * 2
def baseEnd_551047 : Nat := 282951974218210759778287

theorem tailTrace_551047 : CollatzResearch.WordTrace tailWord_551047 prefixEnd_551047 282951974218210759778287 := by
  unfold tailWord_551047
  simp only [CollatzResearch.WordTrace]
  refine ⟨20098335234658305180123395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13398890156438870120082263 20098335234658305180123395)
  ·
    refine ⟨30147502851987457770185093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20098335234658305180123395 30147502851987457770185093)
    ·
      refine ⟨5652656784747648331909705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30147502851987457770185093 5652656784747648331909705)
      ·
        refine ⟨4239492588560736248932279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5652656784747648331909705 4239492588560736248932279)
        ·
          refine ⟨6359238882841104373398419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4239492588560736248932279 6359238882841104373398419)
          ·
            refine ⟨9538858324261656560097629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6359238882841104373398419 9538858324261656560097629)
            ·
              refine ⟨3577071871598121210036611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9538858324261656560097629 3577071871598121210036611)
              ·
                refine ⟨5365607807397181815054917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3577071871598121210036611 5365607807397181815054917)
                ·
                  refine ⟨1006051463886971590322797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5365607807397181815054917 1006051463886971590322797)
                  ·
                    refine ⟨377269298957614346371049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1006051463886971590322797 377269298957614346371049)
                    ·
                      refine ⟨282951974218210759778287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 377269298957614346371049 282951974218210759778287)
                      ·
                        rfl

theorem cell23_551047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_551047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551047 prefixEnd_551047 := by exact prefixLift 551047
  have htrace : WordTrace (prefixWord ++ tailWord_551047) baseStart_551047 baseEnd_551047 := by
    simpa [prefixWord, tailWord_551047, baseEnd_551047] using wordTrace_append hprefix tailTrace_551047
  have hstable : (prefixWord ++ tailWord_551047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551047).length < 2 ^ (prefixWord ++ tailWord_551047).sum := by decide
  have hdescent : baseEnd_551047 < baseStart_551047 := by decide
  rcases family_descends (prefixWord ++ tailWord_551047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551074 : List Nat := [3, 3, 1, 3, 1, 1, 3, 2, 1, 5]
def baseStart_551074 : Nat := 118140960795 + 551074 * 2 ^ 59
def prefixEnd_551074 : Nat := 4983230072969 + 3 ^ 40 * 551074 * 2
def baseEnd_551074 : Nat := 94321946065294051380221

theorem tailTrace_551074 : CollatzResearch.WordTrace tailWord_551074 prefixEnd_551074 94321946065294051380221 := by
  unfold tailWord_551074
  simp only [CollatzResearch.WordTrace]
  refine ⟨5024830001390122197839069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13399546670373659194237517 5024830001390122197839069)
  ·
    refine ⟨1884311250521295824189651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5024830001390122197839069 1884311250521295824189651)
    ·
      refine ⟨2826466875781943736284477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1884311250521295824189651 2826466875781943736284477)
      ·
        refine ⟨1059925078418228901106679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2826466875781943736284477 1059925078418228901106679)
        ·
          refine ⟨1589887617627343351660019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1059925078418228901106679 1589887617627343351660019)
          ·
            refine ⟨2384831426441015027490029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1589887617627343351660019 2384831426441015027490029)
            ·
              refine ⟨894311784915380635308761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2384831426441015027490029 894311784915380635308761)
              ·
                refine ⟨670733838686535476481571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 894311784915380635308761 670733838686535476481571)
                ·
                  refine ⟨1006100758029803214722357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 670733838686535476481571 1006100758029803214722357)
                  ·
                    refine ⟨94321946065294051380221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1006100758029803214722357 94321946065294051380221)
                    ·
                      rfl

theorem cell23_551074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_551074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551074 prefixEnd_551074 := by exact prefixLift 551074
  have htrace : WordTrace (prefixWord ++ tailWord_551074) baseStart_551074 baseEnd_551074 := by
    simpa [prefixWord, tailWord_551074, baseEnd_551074] using wordTrace_append hprefix tailTrace_551074
  have hstable : (prefixWord ++ tailWord_551074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551074).length < 2 ^ (prefixWord ++ tailWord_551074).sum := by decide
  have hdescent : baseEnd_551074 < baseStart_551074 := by decide
  rcases family_descends (prefixWord ++ tailWord_551074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551100 : List Nat := [2, 2, 2, 3, 3, 11]
def baseStart_551100 : Nat := 118140960795 + 551100 * 2 ^ 59
def prefixEnd_551100 : Nat := 4983230072969 + 3 ^ 40 * 551100 * 2
def baseEnd_551100 : Nat := 1164523410258843837101

theorem tailTrace_551100 : CollatzResearch.WordTrace tailWord_551100 prefixEnd_551100 1164523410258843837101 := by
  unfold tailWord_551100
  simp only [CollatzResearch.WordTrace]
  refine ⟨10050134151733147615901377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13400178868977530154535169 10050134151733147615901377)
  ·
    refine ⟨7537600613799860711926033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10050134151733147615901377 7537600613799860711926033)
    ·
      refine ⟨5653200460349895533944525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7537600613799860711926033 5653200460349895533944525)
      ·
        refine ⟨2119950172631210825229197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5653200460349895533944525 2119950172631210825229197)
        ·
          refine ⟨794981314736704059460949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2119950172631210825229197 794981314736704059460949)
          ·
            refine ⟨1164523410258843837101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 794981314736704059460949 1164523410258843837101)
            ·
              rfl

theorem cell23_551100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 11].length) (baseStart_551100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551100 prefixEnd_551100 := by exact prefixLift 551100
  have htrace : WordTrace (prefixWord ++ tailWord_551100) baseStart_551100 baseEnd_551100 := by
    simpa [prefixWord, tailWord_551100, baseEnd_551100] using wordTrace_append hprefix tailTrace_551100
  have hstable : (prefixWord ++ tailWord_551100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551100).length < 2 ^ (prefixWord ++ tailWord_551100).sum := by decide
  have hdescent : baseEnd_551100 < baseStart_551100 := by decide
  rcases family_descends (prefixWord ++ tailWord_551100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551104 : List Nat := [2, 1, 1, 2, 5, 2, 2, 2, 2, 4]
def baseStart_551104 : Nat := 118140960795 + 551104 * 2 ^ 59
def prefixEnd_551104 : Nat := 4983230072969 + 3 ^ 40 * 551104 * 2
def baseEnd_551104 : Nat := 94327080871839012255175

theorem tailTrace_551104 : CollatzResearch.WordTrace tailWord_551104 prefixEnd_551104 94327080871839012255175 := by
  unfold tailWord_551104
  simp only [CollatzResearch.WordTrace]
  refine ⟨10050207097725901957474183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13400276130301202609965577 10050207097725901957474183)
  ·
    refine ⟨15075310646588852936211275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10050207097725901957474183 15075310646588852936211275)
    ·
      refine ⟨22612965969883279404316913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15075310646588852936211275 22612965969883279404316913)
      ·
        refine ⟨16959724477412459553237685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22612965969883279404316913 16959724477412459553237685)
        ·
          refine ⟨1589974169757418083116033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16959724477412459553237685 1589974169757418083116033)
          ·
            refine ⟨1192480627318063562337025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1589974169757418083116033 1192480627318063562337025)
            ·
              refine ⟨894360470488547671752769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1192480627318063562337025 894360470488547671752769)
              ·
                refine ⟨670770352866410753814577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 894360470488547671752769 670770352866410753814577)
                ·
                  refine ⟨503077764649808065360933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 670770352866410753814577 503077764649808065360933)
                  ·
                    refine ⟨94327080871839012255175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 503077764649808065360933 94327080871839012255175)
                    ·
                      rfl

theorem cell23_551104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 2, 4].length) (baseStart_551104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551104 prefixEnd_551104 := by exact prefixLift 551104
  have htrace : WordTrace (prefixWord ++ tailWord_551104) baseStart_551104 baseEnd_551104 := by
    simpa [prefixWord, tailWord_551104, baseEnd_551104] using wordTrace_append hprefix tailTrace_551104
  have hstable : (prefixWord ++ tailWord_551104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551104).length < 2 ^ (prefixWord ++ tailWord_551104).sum := by decide
  have hdescent : baseEnd_551104 < baseStart_551104 := by decide
  rcases family_descends (prefixWord ++ tailWord_551104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551127 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 6, 1, 3]
def baseStart_551127 : Nat := 118140960795 + 551127 * 2 ^ 59
def prefixEnd_551127 : Nat := 4983230072969 + 3 ^ 40 * 551127 * 2
def baseEnd_551127 : Nat := 282993052670570446777919

theorem tailTrace_551127 : CollatzResearch.WordTrace tailWord_551127 prefixEnd_551127 282993052670570446777919 := by
  unfold tailWord_551127
  simp only [CollatzResearch.WordTrace]
  refine ⟨20101253074368478843035635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13400835382912319228690423 20101253074368478843035635)
  ·
    refine ⟨30151879611552718264553453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20101253074368478843035635 30151879611552718264553453)
    ·
      refine ⟨11306954854332269349207545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30151879611552718264553453 11306954854332269349207545)
      ·
        refine ⟨8480216140749202011905659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11306954854332269349207545 8480216140749202011905659)
        ·
          refine ⟨12720324211123803017858489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8480216140749202011905659 12720324211123803017858489)
          ·
            refine ⟨9540243158342852263393867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12720324211123803017858489 9540243158342852263393867)
            ·
              refine ⟨14310364737514278395090801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9540243158342852263393867 14310364737514278395090801)
              ·
                refine ⟨10732773553135708796318101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14310364737514278395090801 10732773553135708796318101)
                ·
                  refine ⟨503098760303236349827411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10732773553135708796318101 503098760303236349827411)
                  ·
                    refine ⟨754648140454854524741117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 503098760303236349827411 754648140454854524741117)
                    ·
                      refine ⟨282993052670570446777919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 754648140454854524741117 282993052670570446777919)
                      ·
                        rfl

theorem cell23_551127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_551127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551127 prefixEnd_551127 := by exact prefixLift 551127
  have htrace : WordTrace (prefixWord ++ tailWord_551127) baseStart_551127 baseEnd_551127 := by
    simpa [prefixWord, tailWord_551127, baseEnd_551127] using wordTrace_append hprefix tailTrace_551127
  have hstable : (prefixWord ++ tailWord_551127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551127).length < 2 ^ (prefixWord ++ tailWord_551127).sum := by decide
  have hdescent : baseEnd_551127 < baseStart_551127 := by decide
  rcases family_descends (prefixWord ++ tailWord_551127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551140 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 2, 2, 5]
def baseStart_551140 : Nat := 118140960795 + 551140 * 2 ^ 59
def prefixEnd_551140 : Nat := 4983230072969 + 3 ^ 40 * 551140 * 2
def baseEnd_551140 : Nat := 282999727919078895915359

theorem tailTrace_551140 : CollatzResearch.WordTrace tailWord_551140 prefixEnd_551140 282999727919078895915359 := by
  unfold tailWord_551140
  simp only [CollatzResearch.WordTrace]
  refine ⟨10050863611660691031629437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13401151482214254708839249 10050863611660691031629437)
  ·
    refine ⟨3769073854372759136861039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10050863611660691031629437 3769073854372759136861039)
    ·
      refine ⟨5653610781559138705291559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3769073854372759136861039 5653610781559138705291559)
      ·
        refine ⟨8480416172338708057937339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5653610781559138705291559 8480416172338708057937339)
        ·
          refine ⟨12720624258508062086906009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8480416172338708057937339 12720624258508062086906009)
          ·
            refine ⟨9540468193881046565179507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12720624258508062086906009 9540468193881046565179507)
            ·
              refine ⟨14310702290821569847769261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9540468193881046565179507 14310702290821569847769261)
              ·
                refine ⟨5366513359058088692913473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14310702290821569847769261 5366513359058088692913473)
                ·
                  refine ⟨4024885019293566519685105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5366513359058088692913473 4024885019293566519685105)
                  ·
                    refine ⟨3018663764470174889763829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4024885019293566519685105 3018663764470174889763829)
                    ·
                      refine ⟨282999727919078895915359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3018663764470174889763829 282999727919078895915359)
                      ·
                        rfl

theorem cell23_551140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_551140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551140 prefixEnd_551140 := by exact prefixLift 551140
  have htrace : WordTrace (prefixWord ++ tailWord_551140) baseStart_551140 baseEnd_551140 := by
    simpa [prefixWord, tailWord_551140, baseEnd_551140] using wordTrace_append hprefix tailTrace_551140
  have hstable : (prefixWord ++ tailWord_551140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551140).length < 2 ^ (prefixWord ++ tailWord_551140).sum := by decide
  have hdescent : baseEnd_551140 < baseStart_551140 := by decide
  rcases family_descends (prefixWord ++ tailWord_551140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551277 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 2, 3, 5]
def baseStart_551277 : Nat := 118140960795 + 551277 * 2 ^ 59
def prefixEnd_551277 : Nat := 4983230072969 + 3 ^ 40 * 551277 * 2
def baseEnd_551277 : Nat := 283070074768744859902229

theorem tailTrace_551277 : CollatzResearch.WordTrace tailWord_551277 prefixEnd_551277 283070074768744859902229 := by
  unfold tailWord_551277
  simp only [CollatzResearch.WordTrace]
  refine ⟨20106724023825054460996085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13404482682550036307330723 20106724023825054460996085)
  ·
    refine ⟨1885005377233598855718383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20106724023825054460996085 1885005377233598855718383)
    ·
      refine ⟨2827508065850398283577575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1885005377233598855718383 2827508065850398283577575)
      ·
        refine ⟨4241262098775597425366363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2827508065850398283577575 4241262098775597425366363)
        ·
          refine ⟨6361893148163396138049545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4241262098775597425366363 6361893148163396138049545)
          ·
            refine ⟨4771419861122547103537159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6361893148163396138049545 4771419861122547103537159)
            ·
              refine ⟨7157129791683820655305739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4771419861122547103537159 7157129791683820655305739)
              ·
                refine ⟨10735694687525730982958609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7157129791683820655305739 10735694687525730982958609)
                ·
                  refine ⟨8051771015644298237218957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10735694687525730982958609 8051771015644298237218957)
                  ·
                    refine ⟨3019414130866611838957109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8051771015644298237218957 3019414130866611838957109)
                    ·
                      refine ⟨283070074768744859902229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3019414130866611838957109 283070074768744859902229)
                      ·
                        rfl

theorem cell23_551277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_551277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551277 prefixEnd_551277 := by exact prefixLift 551277
  have htrace : WordTrace (prefixWord ++ tailWord_551277) baseStart_551277 baseEnd_551277 := by
    simpa [prefixWord, tailWord_551277, baseEnd_551277] using wordTrace_append hprefix tailTrace_551277
  have hstable : (prefixWord ++ tailWord_551277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551277).length < 2 ^ (prefixWord ++ tailWord_551277).sum := by decide
  have hdescent : baseEnd_551277 < baseStart_551277 := by decide
  rcases family_descends (prefixWord ++ tailWord_551277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551381 : List Nat := [1, 3, 2, 3, 1, 2, 2, 3, 1, 1, 4]
def baseStart_551381 : Nat := 118140960795 + 551381 * 2 ^ 59
def prefixEnd_551381 : Nat := 4983230072969 + 3 ^ 40 * 551381 * 2
def baseEnd_551381 : Nat := 283123476756812453001751

theorem tailTrace_551381 : CollatzResearch.WordTrace tailWord_551381 prefixEnd_551381 283123476756812453001751 := by
  unfold tailWord_551381
  simp only [CollatzResearch.WordTrace]
  refine ⟨20110517215448280222781997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13407011476965520148521331 20110517215448280222781997)
  ·
    refine ⟨7541443955793105083543249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20110517215448280222781997 7541443955793105083543249)
    ·
      refine ⟨5656082966844828812657437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7541443955793105083543249 5656082966844828812657437)
      ·
        refine ⟨2121031112566810804746539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5656082966844828812657437 2121031112566810804746539)
        ·
          refine ⟨3181546668850216207119809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2121031112566810804746539 3181546668850216207119809)
          ·
            refine ⟨2386160001637662155339857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3181546668850216207119809 2386160001637662155339857)
            ·
              refine ⟨1789620001228246616504893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2386160001637662155339857 1789620001228246616504893)
              ·
                refine ⟨671107500460592481189335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1789620001228246616504893 671107500460592481189335)
                ·
                  refine ⟨1006661250690888721784003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 671107500460592481189335 1006661250690888721784003)
                  ·
                    refine ⟨1509991876036333082676005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1006661250690888721784003 1509991876036333082676005)
                    ·
                      refine ⟨283123476756812453001751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1509991876036333082676005 283123476756812453001751)
                      ·
                        rfl

theorem cell23_551381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_551381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551381 prefixEnd_551381 := by exact prefixLift 551381
  have htrace : WordTrace (prefixWord ++ tailWord_551381) baseStart_551381 baseEnd_551381 := by
    simpa [prefixWord, tailWord_551381, baseEnd_551381] using wordTrace_append hprefix tailTrace_551381
  have hstable : (prefixWord ++ tailWord_551381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551381).length < 2 ^ (prefixWord ++ tailWord_551381).sum := by decide
  have hdescent : baseEnd_551381 < baseStart_551381 := by decide
  rcases family_descends (prefixWord ++ tailWord_551381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551384 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 5, 2, 3]
def baseStart_551384 : Nat := 118140960795 + 551384 * 2 ^ 59
def prefixEnd_551384 : Nat := 4983230072969 + 3 ^ 40 * 551384 * 2
def baseEnd_551384 : Nat := 283125017198775941264237

theorem tailTrace_551384 : CollatzResearch.WordTrace tailWord_551384 prefixEnd_551384 283125017198775941264237 := by
  unfold tailWord_551384
  simp only [CollatzResearch.WordTrace]
  refine ⟨10055313317218705867570603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13407084422958274490094137 10055313317218705867570603)
  ·
    refine ⟨15082969975828058801355905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10055313317218705867570603 15082969975828058801355905)
    ·
      refine ⟨11312227481871044101016929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15082969975828058801355905 11312227481871044101016929)
      ·
        refine ⟨8484170611403283075762697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11312227481871044101016929 8484170611403283075762697)
        ·
          refine ⟨6363127958552462306822023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8484170611403283075762697 6363127958552462306822023)
          ·
            refine ⟨9544691937828693460233035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6363127958552462306822023 9544691937828693460233035)
            ·
              refine ⟨14317037906743040190349553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9544691937828693460233035 14317037906743040190349553)
              ·
                refine ⟨10737778430057280142762165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14317037906743040190349553 10737778430057280142762165)
                ·
                  refine ⟨1006666727817870013383953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10737778430057280142762165 1006666727817870013383953)
                  ·
                    refine ⟨755000045863402510037965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1006666727817870013383953 755000045863402510037965)
                    ·
                      refine ⟨283125017198775941264237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 755000045863402510037965 283125017198775941264237)
                      ·
                        rfl

theorem cell23_551384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_551384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551384 prefixEnd_551384 := by exact prefixLift 551384
  have htrace : WordTrace (prefixWord ++ tailWord_551384) baseStart_551384 baseEnd_551384 := by
    simpa [prefixWord, tailWord_551384, baseEnd_551384] using wordTrace_append hprefix tailTrace_551384
  have hstable : (prefixWord ++ tailWord_551384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551384).length < 2 ^ (prefixWord ++ tailWord_551384).sum := by decide
  have hdescent : baseEnd_551384 < baseStart_551384 := by decide
  rcases family_descends (prefixWord ++ tailWord_551384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551407 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 6]
def baseStart_551407 : Nat := 118140960795 + 551407 * 2 ^ 59
def prefixEnd_551407 : Nat := 4983230072969 + 3 ^ 40 * 551407 * 2
def baseEnd_551407 : Nat := 283136827253829351276631

theorem tailTrace_551407 : CollatzResearch.WordTrace tailWord_551407 prefixEnd_551407 283136827253829351276631 := by
  unfold tailWord_551407
  simp only [CollatzResearch.WordTrace]
  refine ⟨20111465513354086663228475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13407643675569391108818983 20111465513354086663228475)
  ·
    refine ⟨30167198270031129994842713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20111465513354086663228475 30167198270031129994842713)
    ·
      refine ⟨22625398702523347496132035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30167198270031129994842713 22625398702523347496132035)
      ·
        refine ⟨33938098053785021244198053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22625398702523347496132035 33938098053785021244198053)
        ·
          refine ⟨6363393385084691483287135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33938098053785021244198053 6363393385084691483287135)
          ·
            refine ⟨9545090077627037224930703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6363393385084691483287135 9545090077627037224930703)
            ·
              refine ⟨14317635116440555837396055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9545090077627037224930703 14317635116440555837396055)
              ·
                refine ⟨21476452674660833756094083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14317635116440555837396055 21476452674660833756094083)
                ·
                  refine ⟨32214679011991250634141125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21476452674660833756094083 32214679011991250634141125)
                  ·
                    refine ⟨6040252314748359493901461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32214679011991250634141125 6040252314748359493901461)
                    ·
                      refine ⟨283136827253829351276631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6040252314748359493901461 283136827253829351276631)
                      ·
                        rfl

theorem cell23_551407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 6].length) (baseStart_551407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551407 prefixEnd_551407 := by exact prefixLift 551407
  have htrace : WordTrace (prefixWord ++ tailWord_551407) baseStart_551407 baseEnd_551407 := by
    simpa [prefixWord, tailWord_551407, baseEnd_551407] using wordTrace_append hprefix tailTrace_551407
  have hstable : (prefixWord ++ tailWord_551407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551407).length < 2 ^ (prefixWord ++ tailWord_551407).sum := by decide
  have hdescent : baseEnd_551407 < baseStart_551407 := by decide
  rcases family_descends (prefixWord ++ tailWord_551407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551448 : List Nat := [2, 1, 2, 3, 3, 1, 1, 4, 2, 1, 3]
def baseStart_551448 : Nat := 118140960795 + 551448 * 2 ^ 59
def prefixEnd_551448 : Nat := 4983230072969 + 3 ^ 40 * 551448 * 2
def baseEnd_551448 : Nat := 283157879960663690863943

theorem tailTrace_551448 : CollatzResearch.WordTrace tailWord_551448 prefixEnd_551448 283157879960663690863943 := by
  unfold tailWord_551448
  simp only [CollatzResearch.WordTrace]
  refine ⟨10056480453102775332735499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13408640604137033776980665 10056480453102775332735499)
  ·
    refine ⟨15084720679654162999103249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10056480453102775332735499 15084720679654162999103249)
    ·
      refine ⟨11313540509740622249327437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15084720679654162999103249 11313540509740622249327437)
      ·
        refine ⟨4242577691152733343497789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11313540509740622249327437 4242577691152733343497789)
        ·
          refine ⟨1590966634182275003811671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4242577691152733343497789 1590966634182275003811671)
          ·
            refine ⟨2386449951273412505717507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1590966634182275003811671 2386449951273412505717507)
            ·
              refine ⟨3579674926910118758576261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2386449951273412505717507 3579674926910118758576261)
              ·
                refine ⟨671189048795647267233049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3579674926910118758576261 671189048795647267233049)
                ·
                  refine ⟨503391786596735450424787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 671189048795647267233049 503391786596735450424787)
                  ·
                    refine ⟨755087679895103175637181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 503391786596735450424787 755087679895103175637181)
                    ·
                      refine ⟨283157879960663690863943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 755087679895103175637181 283157879960663690863943)
                      ·
                        rfl

theorem cell23_551448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_551448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551448 prefixEnd_551448 := by exact prefixLift 551448
  have htrace : WordTrace (prefixWord ++ tailWord_551448) baseStart_551448 baseEnd_551448 := by
    simpa [prefixWord, tailWord_551448, baseEnd_551448] using wordTrace_append hprefix tailTrace_551448
  have hstable : (prefixWord ++ tailWord_551448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551448).length < 2 ^ (prefixWord ++ tailWord_551448).sum := by decide
  have hdescent : baseEnd_551448 < baseStart_551448 := by decide
  rcases family_descends (prefixWord ++ tailWord_551448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551474 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5]
def baseStart_551474 : Nat := 118140960795 + 551474 * 2 ^ 59
def prefixEnd_551474 : Nat := 4983230072969 + 3 ^ 40 * 551474 * 2
def baseEnd_551474 : Nat := 283171230457680589138823

theorem tailTrace_551474 : CollatzResearch.WordTrace tailWord_551474 prefixEnd_551474 283171230457680589138823 := by
  unfold tailWord_551474
  simp only [CollatzResearch.WordTrace]
  refine ⟨5028477301027839276479369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13409272802740904737278317 5028477301027839276479369)
  ·
    refine ⟨3771357975770879457359527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5028477301027839276479369 3771357975770879457359527)
    ·
      refine ⟨5657036963656319186039291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3771357975770879457359527 5657036963656319186039291)
      ·
        refine ⟨8485555445484478779058937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5657036963656319186039291 8485555445484478779058937)
        ·
          refine ⟨6364166584113359084294203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8485555445484478779058937 6364166584113359084294203)
          ·
            refine ⟨9546249876170038626441305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6364166584113359084294203 9546249876170038626441305)
            ·
              refine ⟨7159687407127528969830979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9546249876170038626441305 7159687407127528969830979)
              ·
                refine ⟨10739531110691293454746469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7159687407127528969830979 10739531110691293454746469)
                ·
                  refine ⟨2013662083254617522764963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10739531110691293454746469 2013662083254617522764963)
                  ·
                    refine ⟨3020493124881926284147445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2013662083254617522764963 3020493124881926284147445)
                    ·
                      refine ⟨283171230457680589138823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3020493124881926284147445 283171230457680589138823)
                      ·
                        rfl

theorem cell23_551474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_551474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551474 prefixEnd_551474 := by exact prefixLift 551474
  have htrace : WordTrace (prefixWord ++ tailWord_551474) baseStart_551474 baseEnd_551474 := by
    simpa [prefixWord, tailWord_551474, baseEnd_551474] using wordTrace_append hprefix tailTrace_551474
  have hstable : (prefixWord ++ tailWord_551474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551474).length < 2 ^ (prefixWord ++ tailWord_551474).sum := by decide
  have hdescent : baseEnd_551474 < baseStart_551474 := by decide
  rcases family_descends (prefixWord ++ tailWord_551474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551505 : List Nat := [1, 2, 2, 1, 3, 3, 3, 2, 2, 2, 2]
def baseStart_551505 : Nat := 118140960795 + 551505 * 2 ^ 59
def prefixEnd_551505 : Nat := 4983230072969 + 3 ^ 40 * 551505 * 2
def baseEnd_551505 : Nat := 283187148357969967851181

theorem tailTrace_551505 : CollatzResearch.WordTrace tailWord_551505 prefixEnd_551505 283187148357969967851181 := by
  unfold tailWord_551505
  simp only [CollatzResearch.WordTrace]
  refine ⟨20115039866999049400295969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13410026577999366266863979 20115039866999049400295969)
  ·
    refine ⟨15086279900249287050221977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20115039866999049400295969 15086279900249287050221977)
    ·
      refine ⟨11314709925186965287666483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15086279900249287050221977 11314709925186965287666483)
      ·
        refine ⟨16972064887780447931499725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11314709925186965287666483 16972064887780447931499725)
        ·
          refine ⟨6364524332917667974312397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16972064887780447931499725 6364524332917667974312397)
          ·
            refine ⟨2386696624844125490367149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6364524332917667974312397 2386696624844125490367149)
            ·
              refine ⟨895011234316547058887681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2386696624844125490367149 895011234316547058887681)
              ·
                refine ⟨671258425737410294165761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 895011234316547058887681 671258425737410294165761)
                ·
                  refine ⟨503443819303057720624321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 671258425737410294165761 503443819303057720624321)
                  ·
                    refine ⟨377582864477293290468241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 503443819303057720624321 377582864477293290468241)
                    ·
                      refine ⟨283187148357969967851181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 377582864477293290468241 283187148357969967851181)
                      ·
                        rfl

theorem cell23_551505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 2, 2, 2].length) (baseStart_551505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551505 prefixEnd_551505 := by exact prefixLift 551505
  have htrace : WordTrace (prefixWord ++ tailWord_551505) baseStart_551505 baseEnd_551505 := by
    simpa [prefixWord, tailWord_551505, baseEnd_551505] using wordTrace_append hprefix tailTrace_551505
  have hstable : (prefixWord ++ tailWord_551505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551505).length < 2 ^ (prefixWord ++ tailWord_551505).sum := by decide
  have hdescent : baseEnd_551505 < baseStart_551505 := by decide
  rcases family_descends (prefixWord ++ tailWord_551505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551511 : List Nat := [1, 1, 3, 2, 2, 2, 1, 6, 5]
def baseStart_551511 : Nat := 118140960795 + 551511 * 2 ^ 59
def prefixEnd_551511 : Nat := 4983230072969 + 3 ^ 40 * 551511 * 2
def baseEnd_551511 : Nat := 31465581026877438264017

theorem tailTrace_551511 : CollatzResearch.WordTrace tailWord_551511 prefixEnd_551511 31465581026877438264017 := by
  unfold tailWord_551511
  simp only [CollatzResearch.WordTrace]
  refine ⟨20115258704977312425014387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13410172469984874950009591 20115258704977312425014387)
  ·
    refine ⟨30172888057465968637521581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20115258704977312425014387 30172888057465968637521581)
    ·
      refine ⟨11314833021549738239070593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30172888057465968637521581 11314833021549738239070593)
      ·
        refine ⟨8486124766162303679302945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11314833021549738239070593 8486124766162303679302945)
        ·
          refine ⟨6364593574621727759477209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8486124766162303679302945 6364593574621727759477209)
          ·
            refine ⟨4773445180966295819607907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6364593574621727759477209 4773445180966295819607907)
            ·
              refine ⟨7160167771449443729411861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4773445180966295819607907 7160167771449443729411861)
              ·
                refine ⟨335632864286692674816181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7160167771449443729411861 335632864286692674816181)
                ·
                  refine ⟨31465581026877438264017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 335632864286692674816181 31465581026877438264017)
                  ·
                    rfl

theorem cell23_551511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 6, 5].length) (baseStart_551511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551511 prefixEnd_551511 := by exact prefixLift 551511
  have htrace : WordTrace (prefixWord ++ tailWord_551511) baseStart_551511 baseEnd_551511 := by
    simpa [prefixWord, tailWord_551511, baseEnd_551511] using wordTrace_append hprefix tailTrace_551511
  have hstable : (prefixWord ++ tailWord_551511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551511).length < 2 ^ (prefixWord ++ tailWord_551511).sum := by decide
  have hdescent : baseEnd_551511 < baseStart_551511 := by decide
  rcases family_descends (prefixWord ++ tailWord_551511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551521 : List Nat := [1, 2, 3, 1, 1, 4, 2, 1, 2, 3, 3]
def baseStart_551521 : Nat := 118140960795 + 551521 * 2 ^ 59
def prefixEnd_551521 : Nat := 4983230072969 + 3 ^ 40 * 551521 * 2
def baseEnd_551521 : Nat := 283195364048441905251107

theorem tailTrace_551521 : CollatzResearch.WordTrace tailWord_551521 prefixEnd_551521 283195364048441905251107 := by
  unfold tailWord_551521
  simp only [CollatzResearch.WordTrace]
  refine ⟨20115623434941084132878417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13410415623294056088585611 20115623434941084132878417)
  ·
    refine ⟨15086717576205813099658813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20115623434941084132878417 15086717576205813099658813)
    ·
      refine ⟨5657519091077179912372055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15086717576205813099658813 5657519091077179912372055)
      ·
        refine ⟨8486278636615769868558083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5657519091077179912372055 8486278636615769868558083)
        ·
          refine ⟨12729417954923654802837125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8486278636615769868558083 12729417954923654802837125)
          ·
            refine ⟨2386765866548185275531961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12729417954923654802837125 2386765866548185275531961)
            ·
              refine ⟨1790074399911138956648971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2386765866548185275531961 1790074399911138956648971)
              ·
                refine ⟨2685111599866708434973457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1790074399911138956648971 2685111599866708434973457)
                ·
                  refine ⟨2013833699900031326230093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2685111599866708434973457 2013833699900031326230093)
                  ·
                    refine ⟨755187637462511747336285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2013833699900031326230093 755187637462511747336285)
                    ·
                      refine ⟨283195364048441905251107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 755187637462511747336285 283195364048441905251107)
                      ·
                        rfl

theorem cell23_551521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_551521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551521 prefixEnd_551521 := by exact prefixLift 551521
  have htrace : WordTrace (prefixWord ++ tailWord_551521) baseStart_551521 baseEnd_551521 := by
    simpa [prefixWord, tailWord_551521, baseEnd_551521] using wordTrace_append hprefix tailTrace_551521
  have hstable : (prefixWord ++ tailWord_551521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551521).length < 2 ^ (prefixWord ++ tailWord_551521).sum := by decide
  have hdescent : baseEnd_551521 < baseStart_551521 := by decide
  rcases family_descends (prefixWord ++ tailWord_551521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551524 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 3, 7]
def baseStart_551524 : Nat := 118140960795 + 551524 * 2 ^ 59
def prefixEnd_551524 : Nat := 4983230072969 + 3 ^ 40 * 551524 * 2
def baseEnd_551524 : Nat := 94398968163468464504531

theorem tailTrace_551524 : CollatzResearch.WordTrace tailWord_551524 prefixEnd_551524 94398968163468464504531 := by
  unfold tailWord_551524
  simp only [CollatzResearch.WordTrace]
  refine ⟨10057866426965107822618813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13410488569286810430158417 10057866426965107822618813)
  ·
    refine ⟨3771699910111915433482055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10057866426965107822618813 3771699910111915433482055)
    ·
      refine ⟨5657549865167873150223083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3771699910111915433482055 5657549865167873150223083)
      ·
        refine ⟨8486324797751809725334625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5657549865167873150223083 8486324797751809725334625)
        ·
          refine ⟨6364743598313857294000969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8486324797751809725334625 6364743598313857294000969)
          ·
            refine ⟨4773557698735392970500727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6364743598313857294000969 4773557698735392970500727)
            ·
              refine ⟨7160336548103089455751091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4773557698735392970500727 7160336548103089455751091)
              ·
                refine ⟨10740504822154634183626637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7160336548103089455751091 10740504822154634183626637)
                ·
                  refine ⟨4027689308307987818859989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10740504822154634183626637 4027689308307987818859989)
                  ·
                    refine ⟨94398968163468464504531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4027689308307987818859989 94398968163468464504531)
                    ·
                      rfl

theorem cell23_551524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_551524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551524 prefixEnd_551524 := by exact prefixLift 551524
  have htrace : WordTrace (prefixWord ++ tailWord_551524) baseStart_551524 baseEnd_551524 := by
    simpa [prefixWord, tailWord_551524, baseEnd_551524] using wordTrace_append hprefix tailTrace_551524
  have hstable : (prefixWord ++ tailWord_551524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551524).length < 2 ^ (prefixWord ++ tailWord_551524).sum := by decide
  have hdescent : baseEnd_551524 < baseStart_551524 := by decide
  rcases family_descends (prefixWord ++ tailWord_551524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551564 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 1, 5, 5]
def baseStart_551564 : Nat := 118140960795 + 551564 * 2 ^ 59
def prefixEnd_551564 : Nat := 4983230072969 + 3 ^ 40 * 551564 * 2
def baseEnd_551564 : Nat := 283217443716585237013409

theorem tailTrace_551564 : CollatzResearch.WordTrace tailWord_551564 prefixEnd_551564 283217443716585237013409 := by
  unfold tailWord_551564
  simp only [CollatzResearch.WordTrace]
  refine ⟨10058595886892651238346873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13411461182523534984462497 10058595886892651238346873)
  ·
    refine ⟨7543946915169488428760155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10058595886892651238346873 7543946915169488428760155)
    ·
      refine ⟨11315920372754232643140233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7543946915169488428760155 11315920372754232643140233)
      ·
        refine ⟨8486940279565674482355175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11315920372754232643140233 8486940279565674482355175)
        ·
          refine ⟨12730410419348511723532763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8486940279565674482355175 12730410419348511723532763)
          ·
            refine ⟨19095615629022767585299145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12730410419348511723532763 19095615629022767585299145)
            ·
              refine ⟨14321711721767075688974359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19095615629022767585299145 14321711721767075688974359)
              ·
                refine ⟨21482567582650613533461539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14321711721767075688974359 21482567582650613533461539)
                ·
                  refine ⟨32223851373975920300192309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21482567582650613533461539 32223851373975920300192309)
                  ·
                    refine ⟨3020986066310242528143029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32223851373975920300192309 3020986066310242528143029)
                    ·
                      refine ⟨283217443716585237013409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3020986066310242528143029 283217443716585237013409)
                      ·
                        rfl

theorem cell23_551564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_551564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551564 prefixEnd_551564 := by exact prefixLift 551564
  have htrace : WordTrace (prefixWord ++ tailWord_551564) baseStart_551564 baseEnd_551564 := by
    simpa [prefixWord, tailWord_551564, baseEnd_551564] using wordTrace_append hprefix tailTrace_551564
  have hstable : (prefixWord ++ tailWord_551564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551564).length < 2 ^ (prefixWord ++ tailWord_551564).sum := by decide
  have hdescent : baseEnd_551564 < baseStart_551564 := by decide
  rcases family_descends (prefixWord ++ tailWord_551564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551581 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 3, 4, 3]
def baseStart_551581 : Nat := 118140960795 + 551581 * 2 ^ 59
def prefixEnd_551581 : Nat := 4983230072969 + 3 ^ 40 * 551581 * 2
def baseEnd_551581 : Nat := 283226172887711670500831

theorem tailTrace_551581 : CollatzResearch.WordTrace tailWord_551581 prefixEnd_551581 283226172887711670500831 := by
  unfold tailWord_551581
  simp only [CollatzResearch.WordTrace]
  refine ⟨20117811814723714380062597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13411874543149142920041731 20117811814723714380062597)
  ·
    refine ⟨3772089715260696446261737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20117811814723714380062597 3772089715260696446261737)
    ·
      refine ⟨2829067286445522334696303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3772089715260696446261737 2829067286445522334696303)
      ·
        refine ⟨4243600929668283502044455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2829067286445522334696303 4243600929668283502044455)
        ·
          refine ⟨6365401394502425253066683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4243600929668283502044455 6365401394502425253066683)
          ·
            refine ⟨9548102091753637879600025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6365401394502425253066683 9548102091753637879600025)
            ·
              refine ⟨7161076568815228409700019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9548102091753637879600025 7161076568815228409700019)
              ·
                refine ⟨10741614853222842614550029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7161076568815228409700019 10741614853222842614550029)
                ·
                  refine ⟨4028105569958565980456261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10741614853222842614550029 4028105569958565980456261)
                  ·
                    refine ⟨755269794367231121335549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4028105569958565980456261 755269794367231121335549)
                    ·
                      refine ⟨283226172887711670500831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 755269794367231121335549 283226172887711670500831)
                      ·
                        rfl

theorem cell23_551581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_551581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551581 prefixEnd_551581 := by exact prefixLift 551581
  have htrace : WordTrace (prefixWord ++ tailWord_551581) baseStart_551581 baseEnd_551581 := by
    simpa [prefixWord, tailWord_551581, baseEnd_551581] using wordTrace_append hprefix tailTrace_551581
  have hstable : (prefixWord ++ tailWord_551581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551581).length < 2 ^ (prefixWord ++ tailWord_551581).sum := by decide
  have hdescent : baseEnd_551581 < baseStart_551581 := by decide
  rcases family_descends (prefixWord ++ tailWord_551581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551662 : List Nat := [4, 1, 2, 1, 1, 3, 1, 5, 1, 1, 3]
def baseStart_551662 : Nat := 118140960795 + 551662 * 2 ^ 59
def prefixEnd_551662 : Nat := 4983230072969 + 3 ^ 40 * 551662 * 2
def baseEnd_551662 : Nat := 283267764820725853587959

theorem tailTrace_551662 : CollatzResearch.WordTrace tailWord_551662 prefixEnd_551662 283267764820725853587959 := by
  unfold tailWord_551662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2515095765928783151720155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13413844084953510142507493 2515095765928783151720155)
  ·
    refine ⟨3772643648893174727580233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2515095765928783151720155 3772643648893174727580233)
    ·
      refine ⟨2829482736669881045685175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3772643648893174727580233 2829482736669881045685175)
      ·
        refine ⟨4244224105004821568527763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2829482736669881045685175 4244224105004821568527763)
        ·
          refine ⟨6366336157507232352791645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4244224105004821568527763 6366336157507232352791645)
          ·
            refine ⟨2387376059065212132296867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6366336157507232352791645 2387376059065212132296867)
            ·
              refine ⟨3581064088597818198445301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2387376059065212132296867 3581064088597818198445301)
              ·
                refine ⟨335724758306045456104247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3581064088597818198445301 335724758306045456104247)
                ·
                  refine ⟨503587137459068184156371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 335724758306045456104247 503587137459068184156371)
                  ·
                    refine ⟨755380706188602276234557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 503587137459068184156371 755380706188602276234557)
                    ·
                      refine ⟨283267764820725853587959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 755380706188602276234557 283267764820725853587959)
                      ·
                        rfl

theorem cell23_551662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_551662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_551662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_551662 prefixEnd_551662 := by exact prefixLift 551662
  have htrace : WordTrace (prefixWord ++ tailWord_551662) baseStart_551662 baseEnd_551662 := by
    simpa [prefixWord, tailWord_551662, baseEnd_551662] using wordTrace_append hprefix tailTrace_551662
  have hstable : (prefixWord ++ tailWord_551662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551662).length < 2 ^ (prefixWord ++ tailWord_551662).sum := by decide
  have hdescent : baseEnd_551662 < baseStart_551662 := by decide
  rcases family_descends (prefixWord ++ tailWord_551662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
