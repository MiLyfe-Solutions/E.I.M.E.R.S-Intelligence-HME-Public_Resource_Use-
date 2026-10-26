import V185TrunkScan23Chunk1367

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8101469 : List Nat := [1, 4, 4, 2, 1, 2, 1, 2, 1, 3, 2]
def baseStart_8101469 : Nat := 118140960795 + 8101469 * 2 ^ 59
def prefixEnd_8101469 : Nat := 4983230072969 + 3 ^ 40 * 8101469 * 2
def baseEnd_8101469 : Nat := 4159947604499868698979529

theorem tailTrace_8101469 : CollatzResearch.WordTrace tailWord_8101469 prefixEnd_8101469 4159947604499868698979529 := by
  unfold tailWord_8101469
  simp only [CollatzResearch.WordTrace]
  refine ⟨295484849486768908594635461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196989899657845939063090307 295484849486768908594635461)
  ·
    refine ⟨55403409278769170361494149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295484849486768908594635461 55403409278769170361494149)
    ·
      refine ⟨10388139239769219442780153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55403409278769170361494149 10388139239769219442780153)
      ·
        refine ⟨7791104429826914582085115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10388139239769219442780153 7791104429826914582085115)
        ·
          refine ⟨11686656644740371873127673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7791104429826914582085115 11686656644740371873127673)
          ·
            refine ⟨8764992483555278904845755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11686656644740371873127673 8764992483555278904845755)
            ·
              refine ⟨13147488725332918357268633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8764992483555278904845755 13147488725332918357268633)
              ·
                refine ⟨9860616543999688767951475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13147488725332918357268633 9860616543999688767951475)
                ·
                  refine ⟨14790924815999533151927213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9860616543999688767951475 14790924815999533151927213)
                  ·
                    refine ⟨5546596805999824931972705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14790924815999533151927213 5546596805999824931972705)
                    ·
                      refine ⟨4159947604499868698979529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5546596805999824931972705 4159947604499868698979529)
                      ·
                        rfl

theorem cell23_8101469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_8101469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101469 prefixEnd_8101469 := by exact prefixLift 8101469
  have htrace : WordTrace (prefixWord ++ tailWord_8101469) baseStart_8101469 baseEnd_8101469 := by
    simpa [prefixWord, tailWord_8101469, baseEnd_8101469] using wordTrace_append hprefix tailTrace_8101469
  have hstable : (prefixWord ++ tailWord_8101469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101469).length < 2 ^ (prefixWord ++ tailWord_8101469).sum := by decide
  have hdescent : baseEnd_8101469 < baseStart_8101469 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101501 : List Nat := [1, 4, 1, 1, 4, 1, 2, 2, 2, 5]
def baseStart_8101501 : Nat := 118140960795 + 8101501 * 2 ^ 59
def prefixEnd_8101501 : Nat := 4983230072969 + 3 ^ 40 * 8101501 * 2
def baseEnd_8101501 : Nat := 1386654678626937524593127

theorem tailTrace_8101501 : CollatzResearch.WordTrace tailWord_8101501 prefixEnd_8101501 1386654678626937524593127 := by
  unfold tailWord_8101501
  simp only [CollatzResearch.WordTrace]
  refine ⟨295486016622652978059800357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196990677748435318706533571 295486016622652978059800357)
  ·
    refine ⟨55403628116747433386212567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295486016622652978059800357 55403628116747433386212567)
    ·
      refine ⟨83105442175121150079318851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55403628116747433386212567 83105442175121150079318851)
      ·
        refine ⟨124658163262681725118978277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83105442175121150079318851 124658163262681725118978277)
        ·
          refine ⟨23373405611752823459808427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124658163262681725118978277 23373405611752823459808427)
          ·
            refine ⟨35060108417629235189712641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23373405611752823459808427 35060108417629235189712641)
            ·
              refine ⟨26295081313221926392284481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35060108417629235189712641 26295081313221926392284481)
              ·
                refine ⟨19721310984916444794213361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26295081313221926392284481 19721310984916444794213361)
                ·
                  refine ⟨14790983238687333595660021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19721310984916444794213361 14790983238687333595660021)
                  ·
                    refine ⟨1386654678626937524593127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14790983238687333595660021 1386654678626937524593127)
                    ·
                      rfl

theorem cell23_8101501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_8101501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101501 prefixEnd_8101501 := by exact prefixLift 8101501
  have htrace : WordTrace (prefixWord ++ tailWord_8101501) baseStart_8101501 baseEnd_8101501 := by
    simpa [prefixWord, tailWord_8101501, baseEnd_8101501] using wordTrace_append hprefix tailTrace_8101501
  have hstable : (prefixWord ++ tailWord_8101501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101501).length < 2 ^ (prefixWord ++ tailWord_8101501).sum := by decide
  have hdescent : baseEnd_8101501 < baseStart_8101501 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101505 : List Nat := [1, 2, 4, 2, 1, 4, 2, 2, 5]
def baseStart_8101505 : Nat := 118140960795 + 8101505 * 2 ^ 59
def prefixEnd_8101505 : Nat := 4983230072969 + 3 ^ 40 * 8101505 * 2
def baseEnd_8101505 : Nat := 462218454422603395347707

theorem tailTrace_8101505 : CollatzResearch.WordTrace tailWord_8101505 prefixEnd_8101505 462218454422603395347707 := by
  unfold tailWord_8101505
  simp only [CollatzResearch.WordTrace]
  refine ⟨295486162514638486742945969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196990775009758991161963979 295486162514638486742945969)
  ·
    refine ⟨221614621885978865057209477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295486162514638486742945969 221614621885978865057209477)
    ·
      refine ⟨41552741603621037198226777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221614621885978865057209477 41552741603621037198226777)
      ·
        refine ⟨31164556202715777898670083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41552741603621037198226777 31164556202715777898670083)
        ·
          refine ⟨46746834304073666848005125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31164556202715777898670083 46746834304073666848005125)
          ·
            refine ⟨8765031432013812534000961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46746834304073666848005125 8765031432013812534000961)
            ·
              refine ⟨6573773574010359400500721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8765031432013812534000961 6573773574010359400500721)
              ·
                refine ⟨4930330180507769550375541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6573773574010359400500721 4930330180507769550375541)
                ·
                  refine ⟨462218454422603395347707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4930330180507769550375541 462218454422603395347707)
                  ·
                    rfl

theorem cell23_8101505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 2, 5].length) (baseStart_8101505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101505 prefixEnd_8101505 := by exact prefixLift 8101505
  have htrace : WordTrace (prefixWord ++ tailWord_8101505) baseStart_8101505 baseEnd_8101505 := by
    simpa [prefixWord, tailWord_8101505, baseEnd_8101505] using wordTrace_append hprefix tailTrace_8101505
  have hstable : (prefixWord ++ tailWord_8101505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101505).length < 2 ^ (prefixWord ++ tailWord_8101505).sum := by decide
  have hdescent : baseEnd_8101505 < baseStart_8101505 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101535 : List Nat := [1, 1, 2, 7, 1, 2, 1, 1, 2, 5]
def baseStart_8101535 : Nat := 118140960795 + 8101535 * 2 ^ 59
def prefixEnd_8101535 : Nat := 4983230072969 + 3 ^ 40 * 8101535 * 2
def baseEnd_8101535 : Nat := 1386660498074355146918075

theorem tailTrace_8101535 : CollatzResearch.WordTrace tailWord_8101535 prefixEnd_8101535 1386660498074355146918075 := by
  unfold tailWord_8101535
  simp only [CollatzResearch.WordTrace]
  refine ⟨295487256704529801866538059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196991504469686534577692039 295487256704529801866538059)
  ·
    refine ⟨443230885056794702799807089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295487256704529801866538059 443230885056794702799807089)
    ·
      refine ⟨332423163792596027099855317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443230885056794702799807089 332423163792596027099855317)
      ·
        refine ⟨7791167901388969385152859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 332423163792596027099855317 7791167901388969385152859)
        ·
          refine ⟨11686751852083454077729289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7791167901388969385152859 11686751852083454077729289)
          ·
            refine ⟨8765063889062590558296967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11686751852083454077729289 8765063889062590558296967)
            ·
              refine ⟨13147595833593885837445451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8765063889062590558296967 13147595833593885837445451)
              ·
                refine ⟨19721393750390828756168177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13147595833593885837445451 19721393750390828756168177)
                ·
                  refine ⟨14791045312793121567126133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19721393750390828756168177 14791045312793121567126133)
                  ·
                    refine ⟨1386660498074355146918075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14791045312793121567126133 1386660498074355146918075)
                    ·
                      rfl

theorem cell23_8101535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 5].length) (baseStart_8101535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101535 prefixEnd_8101535 := by exact prefixLift 8101535
  have htrace : WordTrace (prefixWord ++ tailWord_8101535) baseStart_8101535 baseEnd_8101535 := by
    simpa [prefixWord, tailWord_8101535, baseEnd_8101535] using wordTrace_append hprefix tailTrace_8101535
  have hstable : (prefixWord ++ tailWord_8101535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101535).length < 2 ^ (prefixWord ++ tailWord_8101535).sum := by decide
  have hdescent : baseEnd_8101535 < baseStart_8101535 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101561 : List Nat := [1, 2, 1, 4, 1, 1, 5, 2, 6]
def baseStart_8101561 : Nat := 118140960795 + 8101561 * 2 ^ 59
def prefixEnd_8101561 : Nat := 4983230072969 + 3 ^ 40 * 8101561 * 2
def baseEnd_8101561 : Nat := 462221649413342482114345

theorem tailTrace_8101561 : CollatzResearch.WordTrace tailWord_8101561 prefixEnd_8101561 462221649413342482114345 := by
  unfold tailWord_8101561
  simp only [CollatzResearch.WordTrace]
  refine ⟨295488205002435608306984537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196992136668290405537989691 295488205002435608306984537)
  ·
    refine ⟨221616153751826706230238403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295488205002435608306984537 221616153751826706230238403)
    ·
      refine ⟨332424230627740059345357605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221616153751826706230238403 332424230627740059345357605)
      ·
        refine ⟨62329543242701261127254551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 332424230627740059345357605 62329543242701261127254551)
        ·
          refine ⟨93494314864051891690881827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62329543242701261127254551 93494314864051891690881827)
          ·
            refine ⟨140241472296077837536322741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93494314864051891690881827 140241472296077837536322741)
            ·
              refine ⟨13147638027757297269030257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140241472296077837536322741 13147638027757297269030257)
              ·
                refine ⟨9860728520817972951772693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13147638027757297269030257 9860728520817972951772693)
                ·
                  refine ⟨462221649413342482114345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9860728520817972951772693 462221649413342482114345)
                  ·
                    rfl

theorem cell23_8101561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 6].length) (baseStart_8101561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101561 prefixEnd_8101561 := by exact prefixLift 8101561
  have htrace : WordTrace (prefixWord ++ tailWord_8101561) baseStart_8101561 baseEnd_8101561 := by
    simpa [prefixWord, tailWord_8101561, baseEnd_8101561] using wordTrace_append hprefix tailTrace_8101561
  have hstable : (prefixWord ++ tailWord_8101561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101561).length < 2 ^ (prefixWord ++ tailWord_8101561).sum := by decide
  have hdescent : baseEnd_8101561 < baseStart_8101561 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101608 : List Nat := [2, 1, 4, 1, 3, 1, 2, 3, 1, 5]
def baseStart_8101608 : Nat := 118140960795 + 8101608 * 2 ^ 59
def prefixEnd_8101608 : Nat := 4983230072969 + 3 ^ 40 * 8101608 * 2
def baseEnd_8101608 : Nat := 1386672992770281218380463

theorem tailTrace_8101608 : CollatzResearch.WordTrace tailWord_8101608 prefixEnd_8101608 1386672992770281218380463 := by
  unfold tailWord_8101608
  simp only [CollatzResearch.WordTrace]
  refine ⟨147744959616632667666972739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196993279488843556889296985 147744959616632667666972739)
  ·
    refine ⟨221617439424949001500459109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147744959616632667666972739 221617439424949001500459109)
    ·
      refine ⟨41553269892177937781336083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221617439424949001500459109 41553269892177937781336083)
      ·
        refine ⟨62329904838266906672004125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41553269892177937781336083 62329904838266906672004125)
        ·
          refine ⟨23373714314350090002001547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62329904838266906672004125 23373714314350090002001547)
          ·
            refine ⟨35060571471525135003002321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23373714314350090002001547 35060571471525135003002321)
            ·
              refine ⟨26295428603643851252251741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35060571471525135003002321 26295428603643851252251741)
              ·
                refine ⟨9860785726366444219594403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26295428603643851252251741 9860785726366444219594403)
                ·
                  refine ⟨14791178589549666329391605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9860785726366444219594403 14791178589549666329391605)
                  ·
                    refine ⟨1386672992770281218380463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14791178589549666329391605 1386672992770281218380463)
                    ·
                      rfl

theorem cell23_8101608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_8101608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101608 prefixEnd_8101608 := by exact prefixLift 8101608
  have htrace : WordTrace (prefixWord ++ tailWord_8101608) baseStart_8101608 baseEnd_8101608 := by
    simpa [prefixWord, tailWord_8101608, baseEnd_8101608] using wordTrace_append hprefix tailTrace_8101608
  have hstable : (prefixWord ++ tailWord_8101608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101608).length < 2 ^ (prefixWord ++ tailWord_8101608).sum := by decide
  have hdescent : baseEnd_8101608 < baseStart_8101608 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101622 : List Nat := [5, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3]
def baseStart_8101622 : Nat := 118140960795 + 8101622 * 2 ^ 59
def prefixEnd_8101622 : Nat := 4983230072969 + 3 ^ 40 * 8101622 * 2
def baseEnd_8101622 : Nat := 4160026167040006600366325

theorem tailTrace_8101622 : CollatzResearch.WordTrace tailWord_8101622 prefixEnd_8101622 4160026167040006600366325 := by
  unfold tailWord_8101622
  simp only [CollatzResearch.WordTrace]
  refine ⟨18468151865950913482809695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196993619903476410483303413 18468151865950913482809695)
  ·
    refine ⟨27702227798926370224214543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18468151865950913482809695 27702227798926370224214543)
    ·
      refine ⟨41553341698389555336321815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27702227798926370224214543 41553341698389555336321815)
      ·
        refine ⟨62330012547584333004482723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41553341698389555336321815 62330012547584333004482723)
        ·
          refine ⟨93495018821376499506724085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62330012547584333004482723 93495018821376499506724085)
          ·
            refine ⟨8765158014504046828755383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93495018821376499506724085 8765158014504046828755383)
            ·
              refine ⟨13147737021756070243133075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8765158014504046828755383 13147737021756070243133075)
              ·
                refine ⟨19721605532634105364699613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13147737021756070243133075 19721605532634105364699613)
                ·
                  refine ⟨7395602074737789511762355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19721605532634105364699613 7395602074737789511762355)
                  ·
                    refine ⟨11093403112106684267643533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7395602074737789511762355 11093403112106684267643533)
                    ·
                      refine ⟨4160026167040006600366325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11093403112106684267643533 4160026167040006600366325)
                      ·
                        rfl

theorem cell23_8101622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_8101622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101622 prefixEnd_8101622 := by exact prefixLift 8101622
  have htrace : WordTrace (prefixWord ++ tailWord_8101622) baseStart_8101622 baseEnd_8101622 := by
    simpa [prefixWord, tailWord_8101622, baseEnd_8101622] using wordTrace_append hprefix tailTrace_8101622
  have hstable : (prefixWord ++ tailWord_8101622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101622).length < 2 ^ (prefixWord ++ tailWord_8101622).sum := by decide
  have hdescent : baseEnd_8101622 < baseStart_8101622 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101631 : List Nat := [1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 5]
def baseStart_8101631 : Nat := 118140960795 + 8101631 * 2 ^ 59
def prefixEnd_8101631 : Nat := 4983230072969 + 3 ^ 40 * 8101631 * 2
def baseEnd_8101631 : Nat := 4160030788365897065153783

theorem tailTrace_8101631 : CollatzResearch.WordTrace tailWord_8101631 prefixEnd_8101631 4160030788365897065153783 := by
  unfold tailWord_8101631
  simp only [CollatzResearch.WordTrace]
  refine ⟨295490758112182010262032747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196993838741454673508021831 295490758112182010262032747)
  ·
    refine ⟨443236137168273015393049121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295490758112182010262032747 443236137168273015393049121)
    ·
      refine ⟨332427102876204761544786841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443236137168273015393049121 332427102876204761544786841)
      ·
        refine ⟨249320327157153571158590131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332427102876204761544786841 249320327157153571158590131)
        ·
          refine ⟨373980490735730356737885197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249320327157153571158590131 373980490735730356737885197)
          ·
            refine ⟨140242684025898883776706949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 373980490735730356737885197 140242684025898883776706949)
            ·
              refine ⟨26295503254856040708132553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140242684025898883776706949 26295503254856040708132553)
              ·
                refine ⟨19721627441142030531099415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26295503254856040708132553 19721627441142030531099415)
                ·
                  refine ⟨29582441161713045796649123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19721627441142030531099415 29582441161713045796649123)
                  ·
                    refine ⟨44373661742569568694973685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29582441161713045796649123 44373661742569568694973685)
                    ·
                      refine ⟨4160030788365897065153783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44373661742569568694973685 4160030788365897065153783)
                      ·
                        rfl

theorem cell23_8101631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_8101631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101631 prefixEnd_8101631 := by exact prefixLift 8101631
  have htrace : WordTrace (prefixWord ++ tailWord_8101631) baseStart_8101631 baseEnd_8101631 := by
    simpa [prefixWord, tailWord_8101631, baseEnd_8101631] using wordTrace_append hprefix tailTrace_8101631
  have hstable : (prefixWord ++ tailWord_8101631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101631).length < 2 ^ (prefixWord ++ tailWord_8101631).sum := by decide
  have hdescent : baseEnd_8101631 < baseStart_8101631 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101641 : List Nat := [1, 2, 1, 1, 3, 2, 1, 5, 1, 2, 4]
def baseStart_8101641 : Nat := 118140960795 + 8101641 * 2 ^ 59
def prefixEnd_8101641 : Nat := 4983230072969 + 3 ^ 40 * 8101641 * 2
def baseEnd_8101641 : Nat := 4160035923172442026028737

theorem tailTrace_8101641 : CollatzResearch.WordTrace tailWord_8101641 prefixEnd_8101641 4160035923172442026028737 := by
  unfold tailWord_8101641
  simp only [CollatzResearch.WordTrace]
  refine ⟨295491122842145781969896777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196994081894763854646597851 295491122842145781969896777)
  ·
    refine ⟨221618342131609336477422583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295491122842145781969896777 221618342131609336477422583)
    ·
      refine ⟨332427513197414004716133875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221618342131609336477422583 332427513197414004716133875)
      ·
        refine ⟨498641269796121007074200813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332427513197414004716133875 498641269796121007074200813)
        ·
          refine ⟨186990476173545377652825305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 498641269796121007074200813 186990476173545377652825305)
          ·
            refine ⟨140242857130159033239618979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186990476173545377652825305 140242857130159033239618979)
            ·
              refine ⟨210364285695238549859428469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140242857130159033239618979 210364285695238549859428469)
              ·
                refine ⟨19721651783928614049321419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 210364285695238549859428469 19721651783928614049321419)
                ·
                  refine ⟨29582477675892921073982129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19721651783928614049321419 29582477675892921073982129)
                  ·
                    refine ⟨22186858256919690805486597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29582477675892921073982129 22186858256919690805486597)
                    ·
                      refine ⟨4160035923172442026028737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22186858256919690805486597 4160035923172442026028737)
                      ·
                        rfl

theorem cell23_8101641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 2, 4].length) (baseStart_8101641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101641 prefixEnd_8101641 := by exact prefixLift 8101641
  have htrace : WordTrace (prefixWord ++ tailWord_8101641) baseStart_8101641 baseEnd_8101641 := by
    simpa [prefixWord, tailWord_8101641, baseEnd_8101641] using wordTrace_append hprefix tailTrace_8101641
  have hstable : (prefixWord ++ tailWord_8101641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101641).length < 2 ^ (prefixWord ++ tailWord_8101641).sum := by decide
  have hdescent : baseEnd_8101641 < baseStart_8101641 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101658 : List Nat := [3, 1, 1, 3, 2, 3, 1, 2, 1, 2, 4]
def baseStart_8101658 : Nat := 118140960795 + 8101658 * 2 ^ 59
def prefixEnd_8101658 : Nat := 4983230072969 + 3 ^ 40 * 8101658 * 2
def baseEnd_8101658 : Nat := 4160044652343568459516159

theorem tailTrace_8101658 : CollatzResearch.WordTrace tailWord_8101658 prefixEnd_8101658 4160044652343568459516159 := by
  unfold tailWord_8101658
  simp only [CollatzResearch.WordTrace]
  refine ⟨73872935720771048468316407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196994495255389462582177085 73872935720771048468316407)
  ·
    refine ⟨110809403581156572702474611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73872935720771048468316407 110809403581156572702474611)
    ·
      refine ⟨166214105371734859053711917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110809403581156572702474611 166214105371734859053711917)
      ·
        refine ⟨62330289514400572145141969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166214105371734859053711917 62330289514400572145141969)
        ·
          refine ⟨46747717135800429108856477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62330289514400572145141969 46747717135800429108856477)
          ·
            refine ⟨17530393925925160915821179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46747717135800429108856477 17530393925925160915821179)
            ·
              refine ⟨26295590888887741373731769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17530393925925160915821179 26295590888887741373731769)
              ·
                refine ⟨19721693166665806030298827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26295590888887741373731769 19721693166665806030298827)
                ·
                  refine ⟨29582539749998709045448241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19721693166665806030298827 29582539749998709045448241)
                  ·
                    refine ⟨22186904812499031784086181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29582539749998709045448241 22186904812499031784086181)
                    ·
                      refine ⟨4160044652343568459516159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22186904812499031784086181 4160044652343568459516159)
                      ·
                        rfl

theorem cell23_8101658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_8101658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101658 prefixEnd_8101658 := by exact prefixLift 8101658
  have htrace : WordTrace (prefixWord ++ tailWord_8101658) baseStart_8101658 baseEnd_8101658 := by
    simpa [prefixWord, tailWord_8101658, baseEnd_8101658] using wordTrace_append hprefix tailTrace_8101658
  have hstable : (prefixWord ++ tailWord_8101658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101658).length < 2 ^ (prefixWord ++ tailWord_8101658).sum := by decide
  have hdescent : baseEnd_8101658 < baseStart_8101658 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101681 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 2, 7]
def baseStart_8101681 : Nat := 118140960795 + 8101681 * 2 ^ 59
def prefixEnd_8101681 : Nat := 4983230072969 + 3 ^ 40 * 8101681 * 2
def baseEnd_8101681 : Nat := 1386685487466207289842851

theorem tailTrace_8101681 : CollatzResearch.WordTrace tailWord_8101681 prefixEnd_8101681 1386685487466207289842851 := by
  unfold tailWord_8101681
  simp only [CollatzResearch.WordTrace]
  refine ⟨295492581762000868801352897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196995054508000579200901931 295492581762000868801352897)
  ·
    refine ⟨221619436321500651601014673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295492581762000868801352897 221619436321500651601014673)
    ·
      refine ⟨166214577241125488700761005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221619436321500651601014673 166214577241125488700761005)
      ·
        refine ⟨62330466465422058262785377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166214577241125488700761005 62330466465422058262785377)
        ·
          refine ⟨46747849849066543697089033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62330466465422058262785377 46747849849066543697089033)
          ·
            refine ⟨35060887386799907772816775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46747849849066543697089033 35060887386799907772816775)
            ·
              refine ⟨52591331080199861659225163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35060887386799907772816775 52591331080199861659225163)
              ·
                refine ⟨78886996620299792488837745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52591331080199861659225163 78886996620299792488837745)
                ·
                  refine ⟨59165247465224844366628309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78886996620299792488837745 59165247465224844366628309)
                  ·
                    refine ⟨1386685487466207289842851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59165247465224844366628309 1386685487466207289842851)
                    ·
                      rfl

theorem cell23_8101681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 7].length) (baseStart_8101681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101681 prefixEnd_8101681 := by exact prefixLift 8101681
  have htrace : WordTrace (prefixWord ++ tailWord_8101681) baseStart_8101681 baseEnd_8101681 := by
    simpa [prefixWord, tailWord_8101681, baseEnd_8101681] using wordTrace_append hprefix tailTrace_8101681
  have hstable : (prefixWord ++ tailWord_8101681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101681).length < 2 ^ (prefixWord ++ tailWord_8101681).sum := by decide
  have hdescent : baseEnd_8101681 < baseStart_8101681 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101685 : List Nat := [1, 3, 3, 1, 5, 1, 1, 8]
def baseStart_8101685 : Nat := 118140960795 + 8101685 * 2 ^ 59
def prefixEnd_8101685 : Nat := 4983230072969 + 3 ^ 40 * 8101685 * 2
def baseEnd_8101685 : Nat := 154076241345231105699205

theorem tailTrace_8101685 : CollatzResearch.WordTrace tailWord_8101685 prefixEnd_8101685 154076241345231105699205 := by
  unfold tailWord_8101685
  simp only [CollatzResearch.WordTrace]
  refine ⟨295492727653986377484498509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196995151769324251656332339 295492727653986377484498509)
  ·
    refine ⟨110809772870244891556686941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295492727653986377484498509 110809772870244891556686941)
    ·
      refine ⟨41553664826341834333757603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110809772870244891556686941 41553664826341834333757603)
      ·
        refine ⟨62330497239512751500636405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41553664826341834333757603 62330497239512751500636405)
        ·
          refine ⟨5843484116204320453184663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62330497239512751500636405 5843484116204320453184663)
          ·
            refine ⟨8765226174306480679776995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5843484116204320453184663 8765226174306480679776995)
            ·
              refine ⟨13147839261459721019665493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8765226174306480679776995 13147839261459721019665493)
              ·
                refine ⟨154076241345231105699205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13147839261459721019665493 154076241345231105699205)
                ·
                  rfl

theorem cell23_8101685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 8].length) (baseStart_8101685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101685 prefixEnd_8101685 := by exact prefixLift 8101685
  have htrace : WordTrace (prefixWord ++ tailWord_8101685) baseStart_8101685 baseEnd_8101685 := by
    simpa [prefixWord, tailWord_8101685, baseEnd_8101685] using wordTrace_append hprefix tailTrace_8101685
  have hstable : (prefixWord ++ tailWord_8101685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101685).length < 2 ^ (prefixWord ++ tailWord_8101685).sum := by decide
  have hdescent : baseEnd_8101685 < baseStart_8101685 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101695 : List Nat := [1, 1, 2, 2, 6, 1, 2, 1, 1, 3, 3]
def baseStart_8101695 : Nat := 118140960795 + 8101695 * 2 ^ 59
def prefixEnd_8101695 : Nat := 4983230072969 + 3 ^ 40 * 8101695 * 2
def baseEnd_8101695 : Nat := 4160063651127784814753489

theorem tailTrace_8101695 : CollatzResearch.WordTrace tailWord_8101695 prefixEnd_8101695 4160063651127784814753489 := by
  unfold tailWord_8101695
  simp only [CollatzResearch.WordTrace]
  refine ⟨295493092383950149192362539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196995394922633432794908359 295493092383950149192362539)
  ·
    refine ⟨443239638575925223788543809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295493092383950149192362539 443239638575925223788543809)
    ·
      refine ⟨332429728931943917841407857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443239638575925223788543809 332429728931943917841407857)
      ·
        refine ⟨249322296698957938381055893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332429728931943917841407857 249322296698957938381055893)
        ·
          refine ⟨11686982657763653361611995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 249322296698957938381055893 11686982657763653361611995)
          ·
            refine ⟨17530473986645480042417993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11686982657763653361611995 17530473986645480042417993)
            ·
              refine ⟨13147855489984110031813495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17530473986645480042417993 13147855489984110031813495)
              ·
                refine ⟨19721783234976165047720243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13147855489984110031813495 19721783234976165047720243)
                ·
                  refine ⟨29582674852464247571580365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19721783234976165047720243 29582674852464247571580365)
                  ·
                    refine ⟨11093503069674092839342637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29582674852464247571580365 11093503069674092839342637)
                    ·
                      refine ⟨4160063651127784814753489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11093503069674092839342637 4160063651127784814753489)
                      ·
                        rfl

theorem cell23_8101695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 3, 3].length) (baseStart_8101695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101695 prefixEnd_8101695 := by exact prefixLift 8101695
  have htrace : WordTrace (prefixWord ++ tailWord_8101695) baseStart_8101695 baseEnd_8101695 := by
    simpa [prefixWord, tailWord_8101695, baseEnd_8101695] using wordTrace_append hprefix tailTrace_8101695
  have hstable : (prefixWord ++ tailWord_8101695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101695).length < 2 ^ (prefixWord ++ tailWord_8101695).sum := by decide
  have hdescent : baseEnd_8101695 < baseStart_8101695 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101701 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 2, 3, 4]
def baseStart_8101701 : Nat := 118140960795 + 8101701 * 2 ^ 59
def prefixEnd_8101701 : Nat := 4983230072969 + 3 ^ 40 * 8101701 * 2
def baseEnd_8101701 : Nat := 4160066732011711791278461

theorem tailTrace_8101701 : CollatzResearch.WordTrace tailWord_8101701 prefixEnd_8101701 4160066732011711791278461 := by
  unfold tailWord_8101701
  simp only [CollatzResearch.WordTrace]
  refine ⟨295493311221928412217080957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196995540814618941478053971 295493311221928412217080957)
  ·
    refine ⟨110809991708223154581405359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295493311221928412217080957 110809991708223154581405359)
    ·
      refine ⟨166214987562334731872108039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110809991708223154581405359 166214987562334731872108039)
      ·
        refine ⟨249322481343502097808162059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166214987562334731872108039 249322481343502097808162059)
        ·
          refine ⟨373983722015253146712243089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249322481343502097808162059 373983722015253146712243089)
          ·
            refine ⟨280487791511439860034182317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373983722015253146712243089 280487791511439860034182317)
            ·
              refine ⟨105182921816789947512818369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280487791511439860034182317 105182921816789947512818369)
              ·
                refine ⟨78887191362592460634613777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105182921816789947512818369 78887191362592460634613777)
                ·
                  refine ⟨59165393521944345475960333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78887191362592460634613777 59165393521944345475960333)
                  ·
                    refine ⟨22187022570729129553485125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59165393521944345475960333 22187022570729129553485125)
                    ·
                      refine ⟨4160066732011711791278461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22187022570729129553485125 4160066732011711791278461)
                      ·
                        rfl

theorem cell23_8101701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_8101701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101701 prefixEnd_8101701 := by exact prefixLift 8101701
  have htrace : WordTrace (prefixWord ++ tailWord_8101701) baseStart_8101701 baseEnd_8101701 := by
    simpa [prefixWord, tailWord_8101701, baseEnd_8101701] using wordTrace_append hprefix tailTrace_8101701
  have hstable : (prefixWord ++ tailWord_8101701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101701).length < 2 ^ (prefixWord ++ tailWord_8101701).sum := by decide
  have hdescent : baseEnd_8101701 < baseStart_8101701 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101702 : List Nat := [6, 1, 1, 2, 1, 2, 3, 7]
def baseStart_8101702 : Nat := 118140960795 + 8101702 * 2 ^ 59
def prefixEnd_8101702 : Nat := 4983230072969 + 3 ^ 40 * 8101702 * 2
def baseEnd_8101702 : Nat := 154076564647865418050591

theorem tailTrace_8101702 : CollatzResearch.WordTrace tailWord_8101702 prefixEnd_8101702 154076564647865418050591 := by
  unfold tailWord_8101702
  simp only [CollatzResearch.WordTrace]
  refine ⟨9234167115466399668370855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 196995565129949859591911573 9234167115466399668370855)
  ·
    refine ⟨13851250673199599502556283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9234167115466399668370855 13851250673199599502556283)
    ·
      refine ⟨20776876009799399253834425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13851250673199599502556283 20776876009799399253834425)
      ·
        refine ⟨15582657007349549440375819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20776876009799399253834425 15582657007349549440375819)
        ·
          refine ⟨23373985511024324160563729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15582657007349549440375819 23373985511024324160563729)
          ·
            refine ⟨17530489133268243120422797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23373985511024324160563729 17530489133268243120422797)
            ·
              refine ⟨6573933424975591170158549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17530489133268243120422797 6573933424975591170158549)
              ·
                refine ⟨154076564647865418050591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6573933424975591170158549 154076564647865418050591)
                ·
                  rfl

theorem cell23_8101702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_8101702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101702 prefixEnd_8101702 := by exact prefixLift 8101702
  have htrace : WordTrace (prefixWord ++ tailWord_8101702) baseStart_8101702 baseEnd_8101702 := by
    simpa [prefixWord, tailWord_8101702, baseEnd_8101702] using wordTrace_append hprefix tailTrace_8101702
  have hstable : (prefixWord ++ tailWord_8101702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101702).length < 2 ^ (prefixWord ++ tailWord_8101702).sum := by decide
  have hdescent : baseEnd_8101702 < baseStart_8101702 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101705 : List Nat := [1, 2, 1, 1, 2, 4, 2, 4, 1, 3, 2]
def baseStart_8101705 : Nat := 118140960795 + 8101705 * 2 ^ 59
def prefixEnd_8101705 : Nat := 4983230072969 + 3 ^ 40 * 8101705 * 2
def baseEnd_8101705 : Nat := 4160068785934329775628443

theorem tailTrace_8101705 : CollatzResearch.WordTrace tailWord_8101705 prefixEnd_8101705 4160068785934329775628443 := by
  unfold tailWord_8101705
  simp only [CollatzResearch.WordTrace]
  refine ⟨295493457113913920900226569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196995638075942613933484379 295493457113913920900226569)
  ·
    refine ⟨221620092835435440675169927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295493457113913920900226569 221620092835435440675169927)
    ·
      refine ⟨332430139253153161012754891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221620092835435440675169927 332430139253153161012754891)
      ·
        refine ⟨498645208879729741519132337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332430139253153161012754891 498645208879729741519132337)
        ·
          refine ⟨373983906659797306139349253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498645208879729741519132337 373983906659797306139349253)
          ·
            refine ⟨70121982498711994901127985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 373983906659797306139349253 70121982498711994901127985)
            ·
              refine ⟨52591486874033996175845989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70121982498711994901127985 52591486874033996175845989)
              ·
                refine ⟨9860903788881374282971123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52591486874033996175845989 9860903788881374282971123)
                ·
                  refine ⟨14791355683322061424456685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9860903788881374282971123 14791355683322061424456685)
                  ·
                    refine ⟨5546758381245773034171257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14791355683322061424456685 5546758381245773034171257)
                    ·
                      refine ⟨4160068785934329775628443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5546758381245773034171257 4160068785934329775628443)
                      ·
                        rfl

theorem cell23_8101705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 3, 2].length) (baseStart_8101705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101705 prefixEnd_8101705 := by exact prefixLift 8101705
  have htrace : WordTrace (prefixWord ++ tailWord_8101705) baseStart_8101705 baseEnd_8101705 := by
    simpa [prefixWord, tailWord_8101705, baseEnd_8101705] using wordTrace_append hprefix tailTrace_8101705
  have hstable : (prefixWord ++ tailWord_8101705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101705).length < 2 ^ (prefixWord ++ tailWord_8101705).sum := by decide
  have hdescent : baseEnd_8101705 < baseStart_8101705 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101721 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 1, 3, 5]
def baseStart_8101721 : Nat := 118140960795 + 8101721 * 2 ^ 59
def prefixEnd_8101721 : Nat := 4983230072969 + 3 ^ 40 * 8101721 * 2
def baseEnd_8101721 : Nat := 4160077001624801713028369

theorem tailTrace_8101721 : CollatzResearch.WordTrace tailWord_8101721 prefixEnd_8101721 4160077001624801713028369 := by
  unfold tailWord_8101721
  simp only [CollatzResearch.WordTrace]
  refine ⟨295494040681855955632809017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196996027121237303755206011 295494040681855955632809017)
  ·
    refine ⟨221620530511391966724606763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295494040681855955632809017 221620530511391966724606763)
    ·
      refine ⟨332430795767087950086910145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221620530511391966724606763 332430795767087950086910145)
      ·
        refine ⟨249323096825315962565182609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332430795767087950086910145 249323096825315962565182609)
        ·
          refine ⟨186992322618986971923886957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249323096825315962565182609 186992322618986971923886957)
          ·
            refine ⟨70122120982120114471457609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186992322618986971923886957 70122120982120114471457609)
            ·
              refine ⟨52591590736590085853593207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70122120982120114471457609 52591590736590085853593207)
              ·
                refine ⟨78887386104885128780389811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52591590736590085853593207 78887386104885128780389811)
                ·
                  refine ⟨118331079157327693170584717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78887386104885128780389811 118331079157327693170584717)
                  ·
                    refine ⟨44374154683997884938969269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118331079157327693170584717 44374154683997884938969269)
                    ·
                      refine ⟨4160077001624801713028369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44374154683997884938969269 4160077001624801713028369)
                      ·
                        rfl

theorem cell23_8101721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_8101721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101721 prefixEnd_8101721 := by exact prefixLift 8101721
  have htrace : WordTrace (prefixWord ++ tailWord_8101721) baseStart_8101721 baseEnd_8101721 := by
    simpa [prefixWord, tailWord_8101721, baseEnd_8101721] using wordTrace_append hprefix tailTrace_8101721
  have hstable : (prefixWord ++ tailWord_8101721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101721).length < 2 ^ (prefixWord ++ tailWord_8101721).sum := by decide
  have hdescent : baseEnd_8101721 < baseStart_8101721 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101801 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 2, 8]
def baseStart_8101801 : Nat := 118140960795 + 8101801 * 2 ^ 59
def prefixEnd_8101801 : Nat := 4983230072969 + 3 ^ 40 * 8101801 * 2
def baseEnd_8101801 : Nat := 1386706026692387133342667

theorem tailTrace_8101801 : CollatzResearch.WordTrace tailWord_8101801 prefixEnd_8101801 1386706026692387133342667 := by
  unfold tailWord_8101801
  simp only [CollatzResearch.WordTrace]
  refine ⟨295496958521566129295721257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196997972347710752863814171 295496958521566129295721257)
  ·
    refine ⟨221622718891174596971790943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295496958521566129295721257 221622718891174596971790943)
    ·
      refine ⟨332434078336761895457686415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221622718891174596971790943 332434078336761895457686415)
      ·
        refine ⟨498651117505142843186529623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332434078336761895457686415 498651117505142843186529623)
        ·
          refine ⟨747976676257714264779794435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498651117505142843186529623 747976676257714264779794435)
          ·
            refine ⟨1121965014386571397169691653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747976676257714264779794435 1121965014386571397169691653)
            ·
              refine ⟨210368440197482136969317185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1121965014386571397169691653 210368440197482136969317185)
              ·
                refine ⟨157776330148111602726987889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210368440197482136969317185 157776330148111602726987889)
                ·
                  refine ⟨118332247611083702045240917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157776330148111602726987889 118332247611083702045240917)
                  ·
                    refine ⟨1386706026692387133342667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 118332247611083702045240917 1386706026692387133342667)
                    ·
                      rfl

theorem cell23_8101801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 8].length) (baseStart_8101801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101801 prefixEnd_8101801 := by exact prefixLift 8101801
  have htrace : WordTrace (prefixWord ++ tailWord_8101801) baseStart_8101801 baseEnd_8101801 := by
    simpa [prefixWord, tailWord_8101801, baseEnd_8101801] using wordTrace_append hprefix tailTrace_8101801
  have hstable : (prefixWord ++ tailWord_8101801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101801).length < 2 ^ (prefixWord ++ tailWord_8101801).sum := by decide
  have hdescent : baseEnd_8101801 < baseStart_8101801 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101838 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6]
def baseStart_8101838 : Nat := 118140960795 + 8101838 * 2 ^ 59
def prefixEnd_8101838 : Nat := 4983230072969 + 3 ^ 40 * 8101838 * 2
def baseEnd_8101838 : Nat := 4160137078861377755265331

theorem tailTrace_8101838 : CollatzResearch.WordTrace tailWord_8101838 prefixEnd_8101838 4160137078861377755265331 := by
  unfold tailWord_8101838
  simp only [CollatzResearch.WordTrace]
  refine ⟨36937288502804010576852271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196998872014954723076545445 36937288502804010576852271)
  ·
    refine ⟨55405932754206015865278407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36937288502804010576852271 55405932754206015865278407)
    ·
      refine ⟨83108899131309023797917611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55405932754206015865278407 83108899131309023797917611)
      ·
        refine ⟨124663348696963535696876417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83108899131309023797917611 124663348696963535696876417)
        ·
          refine ⟨93497511522722651772657313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124663348696963535696876417 93497511522722651772657313)
          ·
            refine ⟨70123133642041988829492985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93497511522722651772657313 70123133642041988829492985)
            ·
              refine ⟨52592350231531491622119739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70123133642041988829492985 52592350231531491622119739)
              ·
                refine ⟨78888525347297237433179609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52592350231531491622119739 78888525347297237433179609)
                ·
                  refine ⟨59166394010472928074884707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78888525347297237433179609 59166394010472928074884707)
                  ·
                    refine ⟨88749591015709392112327061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59166394010472928074884707 88749591015709392112327061)
                    ·
                      refine ⟨4160137078861377755265331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88749591015709392112327061 4160137078861377755265331)
                      ·
                        rfl

theorem cell23_8101838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_8101838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101838 prefixEnd_8101838 := by exact prefixLift 8101838
  have htrace : WordTrace (prefixWord ++ tailWord_8101838) baseStart_8101838 baseEnd_8101838 := by
    simpa [prefixWord, tailWord_8101838, baseEnd_8101838] using wordTrace_append hprefix tailTrace_8101838
  have hstable : (prefixWord ++ tailWord_8101838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101838).length < 2 ^ (prefixWord ++ tailWord_8101838).sum := by decide
  have hdescent : baseEnd_8101838 < baseStart_8101838 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101869 : List Nat := [1, 5, 1, 4, 1, 1, 1, 2, 3, 4]
def baseStart_8101869 : Nat := 118140960795 + 8101869 * 2 ^ 59
def prefixEnd_8101869 : Nat := 4983230072969 + 3 ^ 40 * 8101869 * 2
def baseEnd_8101869 : Nat := 1386717665587222377992563

theorem tailTrace_8101869 : CollatzResearch.WordTrace tailWord_8101869 prefixEnd_8101869 1386717665587222377992563 := by
  unfold tailWord_8101869
  simp only [CollatzResearch.WordTrace]
  refine ⟨295499438685319776909196661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196999625790213184606131107 295499438685319776909196661)
  ·
    refine ⟨27703072376748729085237187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 295499438685319776909196661 27703072376748729085237187)
    ·
      refine ⟨41554608565123093627855781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27703072376748729085237187 41554608565123093627855781)
      ·
        refine ⟨7791489105960580055222959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41554608565123093627855781 7791489105960580055222959)
        ·
          refine ⟨11687233658940870082834439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7791489105960580055222959 11687233658940870082834439)
          ·
            refine ⟨17530850488411305124251659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11687233658940870082834439 17530850488411305124251659)
            ·
              refine ⟨26296275732616957686377489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17530850488411305124251659 26296275732616957686377489)
              ·
                refine ⟨19722206799462718264783117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26296275732616957686377489 19722206799462718264783117)
                ·
                  refine ⟨7395827549798519349293669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19722206799462718264783117 7395827549798519349293669)
                  ·
                    refine ⟨1386717665587222377992563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7395827549798519349293669 1386717665587222377992563)
                    ·
                      rfl

theorem cell23_8101869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_8101869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101869 prefixEnd_8101869 := by exact prefixLift 8101869
  have htrace : WordTrace (prefixWord ++ tailWord_8101869) baseStart_8101869 baseEnd_8101869 := by
    simpa [prefixWord, tailWord_8101869, baseEnd_8101869] using wordTrace_append hprefix tailTrace_8101869
  have hstable : (prefixWord ++ tailWord_8101869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101869).length < 2 ^ (prefixWord ++ tailWord_8101869).sum := by decide
  have hdescent : baseEnd_8101869 < baseStart_8101869 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101886 : List Nat := [4, 2, 2, 2, 1, 2, 2, 3, 1, 4]
def baseStart_8101886 : Nat := 118140960795 + 8101886 * 2 ^ 59
def prefixEnd_8101886 : Nat := 4983230072969 + 3 ^ 40 * 8101886 * 2
def baseEnd_8101886 : Nat := 1386720575310931189155037

theorem tailTrace_8101886 : CollatzResearch.WordTrace tailWord_8101886 prefixEnd_8101886 1386720575310931189155037 := by
  unfold tailWord_8101886
  simp only [CollatzResearch.WordTrace]
  refine ⟨36937507340782273601570689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197000039150838792541710341 36937507340782273601570689)
  ·
    refine ⟨27703130505586705201178017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36937507340782273601570689 27703130505586705201178017)
    ·
      refine ⟨20777347879190028900883513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27703130505586705201178017 20777347879190028900883513)
      ·
        refine ⟨15583010909392521675662635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20777347879190028900883513 15583010909392521675662635)
        ·
          refine ⟨23374516364088782513493953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15583010909392521675662635 23374516364088782513493953)
          ·
            refine ⟨17530887273066586885120465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23374516364088782513493953 17530887273066586885120465)
            ·
              refine ⟨13148165454799940163840349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17530887273066586885120465 13148165454799940163840349)
              ·
                refine ⟨4930562045549977561440131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13148165454799940163840349 4930562045549977561440131)
                ·
                  refine ⟨7395843068324966342160197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4930562045549977561440131 7395843068324966342160197)
                  ·
                    refine ⟨1386720575310931189155037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7395843068324966342160197 1386720575310931189155037)
                    ·
                      rfl

theorem cell23_8101886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_8101886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101886 prefixEnd_8101886 := by exact prefixLift 8101886
  have htrace : WordTrace (prefixWord ++ tailWord_8101886) baseStart_8101886 baseEnd_8101886 := by
    simpa [prefixWord, tailWord_8101886, baseEnd_8101886] using wordTrace_append hprefix tailTrace_8101886
  have hstable : (prefixWord ++ tailWord_8101886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101886).length < 2 ^ (prefixWord ++ tailWord_8101886).sum := by decide
  have hdescent : baseEnd_8101886 < baseStart_8101886 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101902 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2]
def baseStart_8101902 : Nat := 118140960795 + 8101902 * 2 ^ 59
def prefixEnd_8101902 : Nat := 4983230072969 + 3 ^ 40 * 8101902 * 2
def baseEnd_8101902 : Nat := 4160169941623265504865037

theorem tailTrace_8101902 : CollatzResearch.WordTrace tailWord_8101902 prefixEnd_8101902 4160169941623265504865037 := by
  unfold tailWord_8101902
  simp only [CollatzResearch.WordTrace]
  refine ⟨36937580286775027943143495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197000428196133482363431973 36937580286775027943143495)
  ·
    refine ⟨55406370430162541914715243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36937580286775027943143495 55406370430162541914715243)
    ·
      refine ⟨83109555645243812872072865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55406370430162541914715243 83109555645243812872072865)
      ·
        refine ⟨62332166733932859654054649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83109555645243812872072865 62332166733932859654054649)
        ·
          refine ⟨46749125050449644740540987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62332166733932859654054649 46749125050449644740540987)
          ·
            refine ⟨70123687575674467110811481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46749125050449644740540987 70123687575674467110811481)
            ·
              refine ⟨52592765681755850333108611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70123687575674467110811481 52592765681755850333108611)
              ·
                refine ⟨78889148522633775499662917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52592765681755850333108611 78889148522633775499662917)
                ·
                  refine ⟨14791715347993832906186797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78889148522633775499662917 14791715347993832906186797)
                  ·
                    refine ⟨5546893255497687339820049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14791715347993832906186797 5546893255497687339820049)
                    ·
                      refine ⟨4160169941623265504865037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5546893255497687339820049 4160169941623265504865037)
                      ·
                        rfl

theorem cell23_8101902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_8101902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101902 prefixEnd_8101902 := by exact prefixLift 8101902
  have htrace : WordTrace (prefixWord ++ tailWord_8101902) baseStart_8101902 baseEnd_8101902 := by
    simpa [prefixWord, tailWord_8101902, baseEnd_8101902] using wordTrace_append hprefix tailTrace_8101902
  have hstable : (prefixWord ++ tailWord_8101902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101902).length < 2 ^ (prefixWord ++ tailWord_8101902).sum := by decide
  have hdescent : baseEnd_8101902 < baseStart_8101902 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101909 : List Nat := [1, 3, 2, 1, 5, 1, 2, 1, 3, 1, 3]
def baseStart_8101909 : Nat := 118140960795 + 8101909 * 2 ^ 59
def prefixEnd_8101909 : Nat := 4983230072969 + 3 ^ 40 * 8101909 * 2
def baseEnd_8101909 : Nat := 4160173535987846977477505

theorem tailTrace_8101909 : CollatzResearch.WordTrace tailWord_8101909 prefixEnd_8101909 4160173535987846977477505 := by
  unfold tailWord_8101909
  simp only [CollatzResearch.WordTrace]
  refine ⟨295500897605174863740652781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197000598403449909160435187 295500897605174863740652781)
  ·
    refine ⟨110812836601940573902744793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295500897605174863740652781 110812836601940573902744793)
    ·
      refine ⟨83109627451455430427058595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110812836601940573902744793 83109627451455430427058595)
      ·
        refine ⟨124664441177183145640587893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83109627451455430427058595 124664441177183145640587893)
        ·
          refine ⟨11687291360360919903805115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124664441177183145640587893 11687291360360919903805115)
          ·
            refine ⟨17530937040541379855707673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11687291360360919903805115 17530937040541379855707673)
            ·
              refine ⟨13148202780406034891780755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17530937040541379855707673 13148202780406034891780755)
              ·
                refine ⟨19722304170609052337671133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13148202780406034891780755 19722304170609052337671133)
                ·
                  refine ⟨7395864063978394626626675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19722304170609052337671133 7395864063978394626626675)
                  ·
                    refine ⟨11093796095967591939940013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7395864063978394626626675 11093796095967591939940013)
                    ·
                      refine ⟨4160173535987846977477505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11093796095967591939940013 4160173535987846977477505)
                      ·
                        rfl

theorem cell23_8101909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_8101909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101909 prefixEnd_8101909 := by exact prefixLift 8101909
  have htrace : WordTrace (prefixWord ++ tailWord_8101909) baseStart_8101909 baseEnd_8101909 := by
    simpa [prefixWord, tailWord_8101909, baseEnd_8101909] using wordTrace_append hprefix tailTrace_8101909
  have hstable : (prefixWord ++ tailWord_8101909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101909).length < 2 ^ (prefixWord ++ tailWord_8101909).sum := by decide
  have hdescent : baseEnd_8101909 < baseStart_8101909 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101925 : List Nat := [1, 3, 1, 2, 2, 3, 3, 1, 1, 6]
def baseStart_8101925 : Nat := 118140960795 + 8101925 * 2 ^ 59
def prefixEnd_8101925 : Nat := 4983230072969 + 3 ^ 40 * 8101925 * 2
def baseEnd_8101925 : Nat := 1386727250559439638292477

theorem tailTrace_8101925 : CollatzResearch.WordTrace tailWord_8101925 prefixEnd_8101925 1386727250559439638292477 := by
  unfold tailWord_8101925
  simp only [CollatzResearch.WordTrace]
  refine ⟨295501481173116898473235229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197000987448744598982156819 295501481173116898473235229)
  ·
    refine ⟨110813055439918836927463211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295501481173116898473235229 110813055439918836927463211)
    ·
      refine ⟨166219583159878255391194817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110813055439918836927463211 166219583159878255391194817)
      ·
        refine ⟨124664687369908691543396113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166219583159878255391194817 124664687369908691543396113)
        ·
          refine ⟨93498515527431518657547085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124664687369908691543396113 93498515527431518657547085)
          ·
            refine ⟨35061943322786819496580157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93498515527431518657547085 35061943322786819496580157)
            ·
              refine ⟨13148228746045057311217559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35061943322786819496580157 13148228746045057311217559)
              ·
                refine ⟨19722343119067585966826339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13148228746045057311217559 19722343119067585966826339)
                ·
                  refine ⟨29583514678601378950239509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19722343119067585966826339 29583514678601378950239509)
                  ·
                    refine ⟨1386727250559439638292477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29583514678601378950239509 1386727250559439638292477)
                    ·
                      rfl

theorem cell23_8101925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 6].length) (baseStart_8101925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101925 prefixEnd_8101925 := by exact prefixLift 8101925
  have htrace : WordTrace (prefixWord ++ tailWord_8101925) baseStart_8101925 baseEnd_8101925 := by
    simpa [prefixWord, tailWord_8101925, baseEnd_8101925] using wordTrace_append hprefix tailTrace_8101925
  have hstable : (prefixWord ++ tailWord_8101925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101925).length < 2 ^ (prefixWord ++ tailWord_8101925).sum := by decide
  have hdescent : baseEnd_8101925 < baseStart_8101925 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101932 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 5, 2, 2]
def baseStart_8101932 : Nat := 118140960795 + 8101932 * 2 ^ 59
def prefixEnd_8101932 : Nat := 4983230072969 + 3 ^ 40 * 8101932 * 2
def baseEnd_8101932 : Nat := 4160185346042900387489899

theorem tailTrace_8101932 : CollatzResearch.WordTrace tailWord_8101932 prefixEnd_8101932 4160185346042900387489899 := by
  unfold tailWord_8101932
  simp only [CollatzResearch.WordTrace]
  refine ⟨147750868242045769334370025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197001157656061025779160033 147750868242045769334370025)
  ·
    refine ⟨110813151181534327000777519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147750868242045769334370025 110813151181534327000777519)
    ·
      refine ⟨166219726772301490501166279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110813151181534327000777519 166219726772301490501166279)
      ·
        refine ⟨249329590158452235751749419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166219726772301490501166279 249329590158452235751749419)
        ·
          refine ⟨373994385237678353627624129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249329590158452235751749419 373994385237678353627624129)
          ·
            refine ⟨280495788928258765220718097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 373994385237678353627624129 280495788928258765220718097)
            ·
              refine ⟨210371841696194073915538573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280495788928258765220718097 210371841696194073915538573)
              ·
                refine ⟨78889440636072777718326965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210371841696194073915538573 78889440636072777718326965)
                ·
                  refine ⟨7395885059631822911093153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78889440636072777718326965 7395885059631822911093153)
                  ·
                    refine ⟨5546913794723867183319865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7395885059631822911093153 5546913794723867183319865)
                    ·
                      refine ⟨4160185346042900387489899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5546913794723867183319865 4160185346042900387489899)
                      ·
                        rfl

theorem cell23_8101932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 2, 2].length) (baseStart_8101932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101932 prefixEnd_8101932 := by exact prefixLift 8101932
  have htrace : WordTrace (prefixWord ++ tailWord_8101932) baseStart_8101932 baseEnd_8101932 := by
    simpa [prefixWord, tailWord_8101932, baseEnd_8101932] using wordTrace_append hprefix tailTrace_8101932
  have hstable : (prefixWord ++ tailWord_8101932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101932).length < 2 ^ (prefixWord ++ tailWord_8101932).sum := by decide
  have hdescent : baseEnd_8101932 < baseStart_8101932 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101942 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 6, 4]
def baseStart_8101942 : Nat := 118140960795 + 8101942 * 2 ^ 59
def prefixEnd_8101942 : Nat := 4983230072969 + 3 ^ 40 * 8101942 * 2
def baseEnd_8101942 : Nat := 1386730160283148449454951

theorem tailTrace_8101942 : CollatzResearch.WordTrace tailWord_8101942 prefixEnd_8101942 1386730160283148449454951 := by
  unfold tailWord_8101942
  simp only [CollatzResearch.WordTrace]
  refine ⟨18468881325878456898537755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197001400809370206917736053 18468881325878456898537755)
  ·
    refine ⟨27703321988817685347806633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18468881325878456898537755 27703321988817685347806633)
    ·
      refine ⟨20777491491613264010854975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27703321988817685347806633 20777491491613264010854975)
      ·
        refine ⟨31166237237419896016282463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20777491491613264010854975 31166237237419896016282463)
        ·
          refine ⟨46749355856129844024423695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31166237237419896016282463 46749355856129844024423695)
          ·
            refine ⟨70124033784194766036635543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46749355856129844024423695 70124033784194766036635543)
            ·
              refine ⟨105186050676292149054953315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70124033784194766036635543 105186050676292149054953315)
              ·
                refine ⟨157779076014438223582429973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105186050676292149054953315 157779076014438223582429973)
                ·
                  refine ⟨7395894188176791730426405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 157779076014438223582429973 7395894188176791730426405)
                  ·
                    refine ⟨1386730160283148449454951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7395894188176791730426405 1386730160283148449454951)
                    ·
                      rfl

theorem cell23_8101942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_8101942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101942 prefixEnd_8101942 := by exact prefixLift 8101942
  have htrace : WordTrace (prefixWord ++ tailWord_8101942) baseStart_8101942 baseEnd_8101942 := by
    simpa [prefixWord, tailWord_8101942, baseEnd_8101942] using wordTrace_append hprefix tailTrace_8101942
  have hstable : (prefixWord ++ tailWord_8101942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101942).length < 2 ^ (prefixWord ++ tailWord_8101942).sum := by decide
  have hdescent : baseEnd_8101942 < baseStart_8101942 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101952 : List Nat := [2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 3]
def baseStart_8101952 : Nat := 118140960795 + 8101952 * 2 ^ 59
def prefixEnd_8101952 : Nat := 4983230072969 + 3 ^ 40 * 8101952 * 2
def baseEnd_8101952 : Nat := 4160195615655990309239807

theorem tailTrace_8101952 : CollatzResearch.WordTrace tailWord_8101952 prefixEnd_8101952 4160195615655990309239807 := by
  unfold tailWord_8101952
  simp only [CollatzResearch.WordTrace]
  refine ⟨147751232972009541042234055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197001643962679388056312073 147751232972009541042234055)
  ·
    refine ⟨221626849458014311563351083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147751232972009541042234055 221626849458014311563351083)
    ·
      refine ⟨332440274187021467345026625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221626849458014311563351083 332440274187021467345026625)
      ·
        refine ⟨249330205640266100508769969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332440274187021467345026625 249330205640266100508769969)
        ·
          refine ⟨186997654230199575381577477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249330205640266100508769969 186997654230199575381577477)
          ·
            refine ⟨35062060168162420384045777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186997654230199575381577477 35062060168162420384045777)
            ·
              refine ⟨26296545126121815288034333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35062060168162420384045777 26296545126121815288034333)
              ·
                refine ⟨9861204422295680733012875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26296545126121815288034333 9861204422295680733012875)
                ·
                  refine ⟨14791806633443521099519313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9861204422295680733012875 14791806633443521099519313)
                  ·
                    refine ⟨11093854975082640824639485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14791806633443521099519313 11093854975082640824639485)
                    ·
                      refine ⟨4160195615655990309239807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11093854975082640824639485 4160195615655990309239807)
                      ·
                        rfl

theorem cell23_8101952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 3].length) (baseStart_8101952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101952 prefixEnd_8101952 := by exact prefixLift 8101952
  have htrace : WordTrace (prefixWord ++ tailWord_8101952) baseStart_8101952 baseEnd_8101952 := by
    simpa [prefixWord, tailWord_8101952, baseEnd_8101952] using wordTrace_append hprefix tailTrace_8101952
  have hstable : (prefixWord ++ tailWord_8101952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101952).length < 2 ^ (prefixWord ++ tailWord_8101952).sum := by decide
  have hdescent : baseEnd_8101952 < baseStart_8101952 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8101966 : List Nat := [4, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2]
def baseStart_8101966 : Nat := 118140960795 + 8101966 * 2 ^ 59
def prefixEnd_8101966 : Nat := 4983230072969 + 3 ^ 40 * 8101966 * 2
def baseEnd_8101966 : Nat := 4160202804385153254464743

theorem tailTrace_8101966 : CollatzResearch.WordTrace tailWord_8101966 prefixEnd_8101966 4160202804385153254464743 := by
  unfold tailWord_8101966
  simp only [CollatzResearch.WordTrace]
  refine ⟨36937872070746045309434719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197001984377312241650318501 36937872070746045309434719)
  ·
    refine ⟨55406808106119067964152079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36937872070746045309434719 55406808106119067964152079)
    ·
      refine ⟨83110212159178601946228119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55406808106119067964152079 83110212159178601946228119)
      ·
        refine ⟨124665318238767902919342179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83110212159178601946228119 124665318238767902919342179)
        ·
          refine ⟨186997977358151854379013269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124665318238767902919342179 186997977358151854379013269)
          ·
            refine ⟨8765530188663368174016247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 186997977358151854379013269 8765530188663368174016247)
            ·
              refine ⟨13148295282995052261024371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8765530188663368174016247 13148295282995052261024371)
              ·
                refine ⟨19722442924492578391536557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13148295282995052261024371 19722442924492578391536557)
                ·
                  refine ⟨7395916096684716896826209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19722442924492578391536557 7395916096684716896826209)
                  ·
                    refine ⟨5546937072513537672619657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7395916096684716896826209 5546937072513537672619657)
                    ·
                      refine ⟨4160202804385153254464743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5546937072513537672619657 4160202804385153254464743)
                      ·
                        rfl

theorem cell23_8101966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2].length) (baseStart_8101966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8101966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8101966 prefixEnd_8101966 := by exact prefixLift 8101966
  have htrace : WordTrace (prefixWord ++ tailWord_8101966) baseStart_8101966 baseEnd_8101966 := by
    simpa [prefixWord, tailWord_8101966, baseEnd_8101966] using wordTrace_append hprefix tailTrace_8101966
  have hstable : (prefixWord ++ tailWord_8101966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8101966).length < 2 ^ (prefixWord ++ tailWord_8101966).sum := by decide
  have hdescent : baseEnd_8101966 < baseStart_8101966 := by decide
  rcases family_descends (prefixWord ++ tailWord_8101966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102017 : List Nat := [1, 2, 4, 2, 4, 1, 2, 2, 1, 2, 2]
def baseStart_8102017 : Nat := 118140960795 + 8102017 * 2 ^ 59
def prefixEnd_8102017 : Nat := 4983230072969 + 3 ^ 40 * 8102017 * 2
def baseEnd_8102017 : Nat := 4160228991898532554927009

theorem tailTrace_8102017 : CollatzResearch.WordTrace tailWord_8102017 prefixEnd_8102017 4160228991898532554927009 := by
  unfold tailWord_8102017
  simp only [CollatzResearch.WordTrace]
  refine ⟨295504836688783598185584305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197003224459189065457056203 295504836688783598185584305)
  ·
    refine ⟨221628627516587698639188229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295504836688783598185584305 221628627516587698639188229)
    ·
      refine ⟨41555367659360193494847793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221628627516587698639188229 41555367659360193494847793)
      ·
        refine ⟨31166525744520145121135845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41555367659360193494847793 31166525744520145121135845)
        ·
          refine ⟨5843723577097527210212971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31166525744520145121135845 5843723577097527210212971)
          ·
            refine ⟨8765585365646290815319457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5843723577097527210212971 8765585365646290815319457)
            ·
              refine ⟨6574189024234718111489593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8765585365646290815319457 6574189024234718111489593)
              ·
                refine ⟨4930641768176038583617195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6574189024234718111489593 4930641768176038583617195)
                ·
                  refine ⟨7395962652264057875425793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4930641768176038583617195 7395962652264057875425793)
                  ·
                    refine ⟨5546971989198043406569345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7395962652264057875425793 5546971989198043406569345)
                    ·
                      refine ⟨4160228991898532554927009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5546971989198043406569345 4160228991898532554927009)
                      ·
                        rfl

theorem cell23_8102017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_8102017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102017 prefixEnd_8102017 := by exact prefixLift 8102017
  have htrace : WordTrace (prefixWord ++ tailWord_8102017) baseStart_8102017 baseEnd_8102017 := by
    simpa [prefixWord, tailWord_8102017, baseEnd_8102017] using wordTrace_append hprefix tailTrace_8102017
  have hstable : (prefixWord ++ tailWord_8102017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102017).length < 2 ^ (prefixWord ++ tailWord_8102017).sum := by decide
  have hdescent : baseEnd_8102017 < baseStart_8102017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102025 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 1, 6, 3]
def baseStart_8102025 : Nat := 118140960795 + 8102025 * 2 ^ 59
def prefixEnd_8102025 : Nat := 4983230072969 + 3 ^ 40 * 8102025 * 2
def baseEnd_8102025 : Nat := 4160233099743768523626971

theorem tailTrace_8102025 : CollatzResearch.WordTrace tailWord_8102025 prefixEnd_8102025 4160233099743768523626971 := by
  unfold tailWord_8102025
  simp only [CollatzResearch.WordTrace]
  refine ⟨295505128472754615551875529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197003418981836410367917019 295505128472754615551875529)
  ·
    refine ⟨221628846354565961663906647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295505128472754615551875529 221628846354565961663906647)
    ·
      refine ⟨332443269531848942495859971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221628846354565961663906647 332443269531848942495859971)
      ·
        refine ⟨498664904297773413743789957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332443269531848942495859971 498664904297773413743789957)
        ·
          refine ⟨93499669555832515076960617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 498664904297773413743789957 93499669555832515076960617)
          ·
            refine ⟨70124752166874386307720463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93499669555832515076960617 70124752166874386307720463)
            ·
              refine ⟨105187128250311579461580695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70124752166874386307720463 105187128250311579461580695)
              ·
                refine ⟨157780692375467369192371043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105187128250311579461580695 157780692375467369192371043)
                ·
                  refine ⟨236671038563201053788556565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157780692375467369192371043 236671038563201053788556565)
                  ·
                    refine ⟨11093954932650049396338589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 236671038563201053788556565 11093954932650049396338589)
                    ·
                      refine ⟨4160233099743768523626971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11093954932650049396338589 4160233099743768523626971)
                      ·
                        rfl

theorem cell23_8102025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 6, 3].length) (baseStart_8102025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102025 prefixEnd_8102025 := by exact prefixLift 8102025
  have htrace : WordTrace (prefixWord ++ tailWord_8102025) baseStart_8102025 baseEnd_8102025 := by
    simpa [prefixWord, tailWord_8102025, baseEnd_8102025] using wordTrace_append hprefix tailTrace_8102025
  have hstable : (prefixWord ++ tailWord_8102025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102025).length < 2 ^ (prefixWord ++ tailWord_8102025).sum := by decide
  have hdescent : baseEnd_8102025 < baseStart_8102025 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102045 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 9]
def baseStart_8102045 : Nat := 118140960795 + 8102045 * 2 ^ 59
def prefixEnd_8102045 : Nat := 4983230072969 + 3 ^ 40 * 8102045 * 2
def baseEnd_8102045 : Nat := 462249263261873160597431

theorem tailTrace_8102045 : CollatzResearch.WordTrace tailWord_8102045 prefixEnd_8102045 462249263261873160597431 := by
  unfold tailWord_8102045
  simp only [CollatzResearch.WordTrace]
  refine ⟨295505857932682158967603589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197003905288454772645069059 295505857932682158967603589)
  ·
    refine ⟨55407348362377904806425673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295505857932682158967603589 55407348362377904806425673)
    ·
      refine ⟨41555511271783428604819255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55407348362377904806425673 41555511271783428604819255)
      ·
        refine ⟨62333266907675142907228883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41555511271783428604819255 62333266907675142907228883)
        ·
          refine ⟨93499900361512714360843325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62333266907675142907228883 93499900361512714360843325)
          ·
            refine ⟨35062462635567267885316247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93499900361512714360843325 35062462635567267885316247)
            ·
              refine ⟨52593693953350901827974371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35062462635567267885316247 52593693953350901827974371)
              ·
                refine ⟨78890540930026352741961557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52593693953350901827974371 78890540930026352741961557)
                ·
                  refine ⟨462249263261873160597431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78890540930026352741961557 462249263261873160597431)
                  ·
                    rfl

theorem cell23_8102045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 9].length) (baseStart_8102045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102045 prefixEnd_8102045 := by exact prefixLift 8102045
  have htrace : WordTrace (prefixWord ++ tailWord_8102045) baseStart_8102045 baseEnd_8102045 := by
    simpa [prefixWord, tailWord_8102045, baseEnd_8102045] using wordTrace_append hprefix tailTrace_8102045
  have hstable : (prefixWord ++ tailWord_8102045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102045).length < 2 ^ (prefixWord ++ tailWord_8102045).sum := by decide
  have hdescent : baseEnd_8102045 < baseStart_8102045 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102075 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 4, 5]
def baseStart_8102075 : Nat := 118140960795 + 8102075 * 2 ^ 59
def prefixEnd_8102075 : Nat := 4983230072969 + 3 ^ 40 * 8102075 * 2
def baseEnd_8102075 : Nat := 1386752924592164442667247

theorem tailTrace_8102075 : CollatzResearch.WordTrace tailWord_8102075 prefixEnd_8102075 1386752924592164442667247 := by
  unfold tailWord_8102075
  simp only [CollatzResearch.WordTrace]
  refine ⟨295506952122573474091195679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197004634748382316060797119 295506952122573474091195679)
  ·
    refine ⟨443260428183860211136793519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295506952122573474091195679 443260428183860211136793519)
    ·
      refine ⟨664890642275790316705190279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443260428183860211136793519 664890642275790316705190279)
      ·
        refine ⟨997335963413685475057785419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664890642275790316705190279 997335963413685475057785419)
        ·
          refine ⟨1496003945120528212586678129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 997335963413685475057785419 1496003945120528212586678129)
          ·
            refine ⟨1122002958840396159440008597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1496003945120528212586678129 1122002958840396159440008597)
            ·
              refine ⟨52593888695643569973750403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1122002958840396159440008597 52593888695643569973750403)
              ·
                refine ⟨78890833043465354960625605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52593888695643569973750403 78890833043465354960625605)
                ·
                  refine ⟨14792031195649754055117301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78890833043465354960625605 14792031195649754055117301)
                  ·
                    refine ⟨1386752924592164442667247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14792031195649754055117301 1386752924592164442667247)
                    ·
                      rfl

theorem cell23_8102075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 5].length) (baseStart_8102075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102075 prefixEnd_8102075 := by exact prefixLift 8102075
  have htrace : WordTrace (prefixWord ++ tailWord_8102075) baseStart_8102075 baseEnd_8102075 := by
    simpa [prefixWord, tailWord_8102075, baseEnd_8102075] using wordTrace_append hprefix tailTrace_8102075
  have hstable : (prefixWord ++ tailWord_8102075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102075).length < 2 ^ (prefixWord ++ tailWord_8102075).sum := by decide
  have hdescent : baseEnd_8102075 < baseStart_8102075 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102085 : List Nat := [1, 3, 1, 1, 1, 1, 4, 3, 1, 2, 5]
def baseStart_8102085 : Nat := 118140960795 + 8102085 * 2 ^ 59
def prefixEnd_8102085 : Nat := 4983230072969 + 3 ^ 40 * 8102085 * 2
def baseEnd_8102085 : Nat := 4160263908583038288876695

theorem tailTrace_8102085 : CollatzResearch.WordTrace tailWord_8102085 prefixEnd_8102085 4160263908583038288876695 := by
  unfold tailWord_8102085
  simp only [CollatzResearch.WordTrace]
  refine ⟨295507316852537245799059709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197004877901691497199373139 295507316852537245799059709)
  ·
    refine ⟨110815243819701467174647391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295507316852537245799059709 110815243819701467174647391)
    ·
      refine ⟨166222865729552200761971087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110815243819701467174647391 166222865729552200761971087)
      ·
        refine ⟨249334298594328301142956631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166222865729552200761971087 249334298594328301142956631)
        ·
          refine ⟨374001447891492451714434947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249334298594328301142956631 374001447891492451714434947)
          ·
            refine ⟨561002171837238677571652421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374001447891492451714434947 561002171837238677571652421)
            ·
              refine ⟨105187907219482252044684829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 561002171837238677571652421 105187907219482252044684829)
              ·
                refine ⟨39445465207305844516756811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105187907219482252044684829 39445465207305844516756811)
                ·
                  refine ⟨59168197810958766775135217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39445465207305844516756811 59168197810958766775135217)
                  ·
                    refine ⟨44376148358219075081351413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59168197810958766775135217 44376148358219075081351413)
                    ·
                      refine ⟨4160263908583038288876695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44376148358219075081351413 4160263908583038288876695)
                      ·
                        rfl

theorem cell23_8102085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_8102085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102085 prefixEnd_8102085 := by exact prefixLift 8102085
  have htrace : WordTrace (prefixWord ++ tailWord_8102085) baseStart_8102085 baseEnd_8102085 := by
    simpa [prefixWord, tailWord_8102085, baseEnd_8102085] using wordTrace_append hprefix tailTrace_8102085
  have hstable : (prefixWord ++ tailWord_8102085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102085).length < 2 ^ (prefixWord ++ tailWord_8102085).sum := by decide
  have hdescent : baseEnd_8102085 < baseStart_8102085 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102095 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 4]
def baseStart_8102095 : Nat := 118140960795 + 8102095 * 2 ^ 59
def prefixEnd_8102095 : Nat := 4983230072969 + 3 ^ 40 * 8102095 * 2
def baseEnd_8102095 : Nat := 4160269043389583249751649

theorem tailTrace_8102095 : CollatzResearch.WordTrace tailWord_8102095 prefixEnd_8102095 4160269043389583249751649 := by
  unfold tailWord_8102095
  simp only [CollatzResearch.WordTrace]
  refine ⟨295507681582501017506923739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197005121055000678337949159 295507681582501017506923739)
  ·
    refine ⟨443261522373751526260385609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295507681582501017506923739 443261522373751526260385609)
    ·
      refine ⟨332446141780313644695289207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443261522373751526260385609 332446141780313644695289207)
      ·
        refine ⟨498669212670470467042933811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332446141780313644695289207 498669212670470467042933811)
        ·
          refine ⟨748003819005705700564400717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498669212670470467042933811 748003819005705700564400717)
          ·
            refine ⟨280501432127139637711650269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 748003819005705700564400717 280501432127139637711650269)
            ·
              refine ⟨105188037047677364141868851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280501432127139637711650269 105188037047677364141868851)
              ·
                refine ⟨157782055571516046212803277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105188037047677364141868851 157782055571516046212803277)
                ·
                  refine ⟨59168270839318517329801229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157782055571516046212803277 59168270839318517329801229)
                  ·
                    refine ⟨22188101564744443998675461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59168270839318517329801229 22188101564744443998675461)
                    ·
                      refine ⟨4160269043389583249751649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22188101564744443998675461 4160269043389583249751649)
                      ·
                        rfl

theorem cell23_8102095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 4].length) (baseStart_8102095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102095 prefixEnd_8102095 := by exact prefixLift 8102095
  have htrace : WordTrace (prefixWord ++ tailWord_8102095) baseStart_8102095 baseEnd_8102095 := by
    simpa [prefixWord, tailWord_8102095, baseEnd_8102095] using wordTrace_append hprefix tailTrace_8102095
  have hstable : (prefixWord ++ tailWord_8102095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102095).length < 2 ^ (prefixWord ++ tailWord_8102095).sum := by decide
  have hdescent : baseEnd_8102095 < baseStart_8102095 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102112 : List Nat := [2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 4]
def baseStart_8102112 : Nat := 118140960795 + 8102112 * 2 ^ 59
def prefixEnd_8102112 : Nat := 4983230072969 + 3 ^ 40 * 8102112 * 2
def baseEnd_8102112 : Nat := 4160277772560709683239071

theorem tailTrace_8102112 : CollatzResearch.WordTrace tailWord_8102112 prefixEnd_8102112 4160277772560709683239071 := by
  unfold tailWord_8102112
  simp only [CollatzResearch.WordTrace]
  refine ⟨147754150811719714705146295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197005534415626286273528393 147754150811719714705146295)
  ·
    refine ⟨221631226217579572057719443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147754150811719714705146295 221631226217579572057719443)
    ·
      refine ⟨332446839326369358086579165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221631226217579572057719443 332446839326369358086579165)
      ·
        refine ⟨124667564747388509282467187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332446839326369358086579165 124667564747388509282467187)
        ·
          refine ⟨187001347121082763923700781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124667564747388509282467187 187001347121082763923700781)
          ·
            refine ⟨70125505170406036471387793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187001347121082763923700781 70125505170406036471387793)
            ·
              refine ⟨52594128877804527353540845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70125505170406036471387793 52594128877804527353540845)
              ·
                refine ⟨19722798329176697757577817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52594128877804527353540845 19722798329176697757577817)
                ·
                  refine ⟨14792098746882523318183363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19722798329176697757577817 14792098746882523318183363)
                  ·
                    refine ⟨22188148120323784977275045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14792098746882523318183363 22188148120323784977275045)
                    ·
                      refine ⟨4160277772560709683239071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22188148120323784977275045 4160277772560709683239071)
                      ·
                        rfl

theorem cell23_8102112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_8102112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102112 prefixEnd_8102112 := by exact prefixLift 8102112
  have htrace : WordTrace (prefixWord ++ tailWord_8102112) baseStart_8102112 baseEnd_8102112 := by
    simpa [prefixWord, tailWord_8102112, baseEnd_8102112] using wordTrace_append hprefix tailTrace_8102112
  have hstable : (prefixWord ++ tailWord_8102112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102112).length < 2 ^ (prefixWord ++ tailWord_8102112).sum := by decide
  have hdescent : baseEnd_8102112 < baseStart_8102112 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102186 : List Nat := [3, 1, 4, 2, 2, 1, 2, 2, 6]
def baseStart_8102186 : Nat := 118140960795 + 8102186 * 2 ^ 59
def prefixEnd_8102186 : Nat := 4983230072969 + 3 ^ 40 * 8102186 * 2
def baseEnd_8102186 : Nat := 462257307792126932634859

theorem tailTrace_8102186 : CollatzResearch.WordTrace tailWord_8102186 prefixEnd_8102186 462257307792126932634859 := by
  unfold tailWord_8102186
  simp only [CollatzResearch.WordTrace]
  refine ⟨73877750156292835012121603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197007333750114226698990941 73877750156292835012121603)
  ·
    refine ⟨110816625234439252518182405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73877750156292835012121603 110816625234439252518182405)
    ·
      refine ⟨20778117231457359847159201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110816625234439252518182405 20778117231457359847159201)
      ·
        refine ⟨15583587923593019885369401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20778117231457359847159201 15583587923593019885369401)
        ·
          refine ⟨11687690942694764914027051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15583587923593019885369401 11687690942694764914027051)
          ·
            refine ⟨17531536414042147371040577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11687690942694764914027051 17531536414042147371040577)
            ·
              refine ⟨13148652310531610528280433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17531536414042147371040577 13148652310531610528280433)
              ·
                refine ⟨9861489232898707896210325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13148652310531610528280433 9861489232898707896210325)
                ·
                  refine ⟨462257307792126932634859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9861489232898707896210325 462257307792126932634859)
                  ·
                    rfl

theorem cell23_8102186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 6].length) (baseStart_8102186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102186 prefixEnd_8102186 := by exact prefixLift 8102186
  have htrace : WordTrace (prefixWord ++ tailWord_8102186) baseStart_8102186 baseEnd_8102186 := by
    simpa [prefixWord, tailWord_8102186, baseEnd_8102186] using wordTrace_append hprefix tailTrace_8102186
  have hstable : (prefixWord ++ tailWord_8102186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102186).length < 2 ^ (prefixWord ++ tailWord_8102186).sum := by decide
  have hdescent : baseEnd_8102186 < baseStart_8102186 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102190 : List Nat := [4, 1, 3, 3, 1, 1, 1, 4, 1, 4]
def baseStart_8102190 : Nat := 118140960795 + 8102190 * 2 ^ 59
def prefixEnd_8102190 : Nat := 4983230072969 + 3 ^ 40 * 8102190 * 2
def baseEnd_8102190 : Nat := 1386772608017253459354571

theorem tailTrace_8102190 : CollatzResearch.WordTrace tailWord_8102190 prefixEnd_8102190 1386772608017253459354571 := by
  unfold tailWord_8102190
  simp only [CollatzResearch.WordTrace]
  refine ⟨36938893314644606091454003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197007431011437899154421349 36938893314644606091454003)
  ·
    refine ⟨55408339971966909137181005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36938893314644606091454003 55408339971966909137181005)
    ·
      refine ⟨20778127489487590926442877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55408339971966909137181005 20778127489487590926442877)
      ·
        refine ⟨7791797808557846597416079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20778127489487590926442877 7791797808557846597416079)
        ·
          refine ⟨11687696712836769896124119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7791797808557846597416079 11687696712836769896124119)
          ·
            refine ⟨17531545069255154844186179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11687696712836769896124119 17531545069255154844186179)
            ·
              refine ⟨26297317603882732266279269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17531545069255154844186179 26297317603882732266279269)
              ·
                refine ⟨4930747050728012299927363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26297317603882732266279269 4930747050728012299927363)
                ·
                  refine ⟨7396120576092018449891045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4930747050728012299927363 7396120576092018449891045)
                  ·
                    refine ⟨1386772608017253459354571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7396120576092018449891045 1386772608017253459354571)
                    ·
                      rfl

theorem cell23_8102190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_8102190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102190 prefixEnd_8102190 := by exact prefixLift 8102190
  have htrace : WordTrace (prefixWord ++ tailWord_8102190) baseStart_8102190 baseEnd_8102190 := by
    simpa [prefixWord, tailWord_8102190, baseEnd_8102190] using wordTrace_append hprefix tailTrace_8102190
  have hstable : (prefixWord ++ tailWord_8102190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102190).length < 2 ^ (prefixWord ++ tailWord_8102190).sum := by decide
  have hdescent : baseEnd_8102190 < baseStart_8102190 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102222 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5]
def baseStart_8102222 : Nat := 118140960795 + 8102222 * 2 ^ 59
def prefixEnd_8102222 : Nat := 4983230072969 + 3 ^ 40 * 8102222 * 2
def baseEnd_8102222 : Nat := 4160334255432704252863565

theorem tailTrace_8102222 : CollatzResearch.WordTrace tailWord_8102222 prefixEnd_8102222 4160334255432704252863565 := by
  unfold tailWord_8102222
  simp only [CollatzResearch.WordTrace]
  refine ⟨36939039206630114774599615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197008209102027278797864613 36939039206630114774599615)
  ·
    refine ⟨55408558809945172161899423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36939039206630114774599615 55408558809945172161899423)
    ·
      refine ⟨83112838214917758242849135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55408558809945172161899423 83112838214917758242849135)
      ·
        refine ⟨124669257322376637364273703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83112838214917758242849135 124669257322376637364273703)
        ·
          refine ⟨187003885983564956046410555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124669257322376637364273703 187003885983564956046410555)
          ·
            refine ⟨280505828975347434069615833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187003885983564956046410555 280505828975347434069615833)
            ·
              refine ⟨210379371731510575552211875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280505828975347434069615833 210379371731510575552211875)
              ·
                refine ⟨315569057597265863328317813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210379371731510575552211875 315569057597265863328317813)
                ·
                  refine ⟨29584599149743674687029795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 315569057597265863328317813 29584599149743674687029795)
                  ·
                    refine ⟨44376898724615512030544693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29584599149743674687029795 44376898724615512030544693)
                    ·
                      refine ⟨4160334255432704252863565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44376898724615512030544693 4160334255432704252863565)
                      ·
                        rfl

theorem cell23_8102222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_8102222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102222 prefixEnd_8102222 := by exact prefixLift 8102222
  have htrace : WordTrace (prefixWord ++ tailWord_8102222) baseStart_8102222 baseEnd_8102222 := by
    simpa [prefixWord, tailWord_8102222, baseEnd_8102222] using wordTrace_append hprefix tailTrace_8102222
  have hstable : (prefixWord ++ tailWord_8102222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102222).length < 2 ^ (prefixWord ++ tailWord_8102222).sum := by decide
  have hdescent : baseEnd_8102222 < baseStart_8102222 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102232 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 3, 2, 4]
def baseStart_8102232 : Nat := 118140960795 + 8102232 * 2 ^ 59
def prefixEnd_8102232 : Nat := 4983230072969 + 3 ^ 40 * 8102232 * 2
def baseEnd_8102232 : Nat := 4160339390239249213738519

theorem tailTrace_8102232 : CollatzResearch.WordTrace tailWord_8102232 prefixEnd_8102232 4160339390239249213738519 := by
  unfold tailWord_8102232
  simp only [CollatzResearch.WordTrace]
  refine ⟨147756339191502344952330475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197008452255336459936440633 147756339191502344952330475)
  ·
    refine ⟨221634508787253517428495713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147756339191502344952330475 221634508787253517428495713)
    ·
      refine ⟨166225881590440138071371785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221634508787253517428495713 166225881590440138071371785)
      ·
        refine ⟨124669411192830103553528839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166225881590440138071371785 124669411192830103553528839)
        ·
          refine ⟨187004116789245155330293259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124669411192830103553528839 187004116789245155330293259)
          ·
            refine ⟨280506175183867732995439889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187004116789245155330293259 280506175183867732995439889)
            ·
              refine ⟨210379631387900799746579917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280506175183867732995439889 210379631387900799746579917)
              ·
                refine ⟨78892361770462799904967469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210379631387900799746579917 78892361770462799904967469)
                ·
                  refine ⟨29584635663923549964362801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78892361770462799904967469 29584635663923549964362801)
                  ·
                    refine ⟨22188476747942662473272101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29584635663923549964362801 22188476747942662473272101)
                    ·
                      refine ⟨4160339390239249213738519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22188476747942662473272101 4160339390239249213738519)
                      ·
                        rfl

theorem cell23_8102232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_8102232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102232 prefixEnd_8102232 := by exact prefixLift 8102232
  have htrace : WordTrace (prefixWord ++ tailWord_8102232) baseStart_8102232 baseEnd_8102232 := by
    simpa [prefixWord, tailWord_8102232, baseEnd_8102232] using wordTrace_append hprefix tailTrace_8102232
  have hstable : (prefixWord ++ tailWord_8102232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102232).length < 2 ^ (prefixWord ++ tailWord_8102232).sum := by decide
  have hdescent : baseEnd_8102232 < baseStart_8102232 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102253 : List Nat := [1, 5, 1, 1, 1, 2, 4, 1, 3, 2, 2]
def baseStart_8102253 : Nat := 118140960795 + 8102253 * 2 ^ 59
def prefixEnd_8102253 : Nat := 4983230072969 + 3 ^ 40 * 8102253 * 2
def baseEnd_8102253 : Nat := 4160350173332993631575923

theorem tailTrace_8102253 : CollatzResearch.WordTrace tailWord_8102253 prefixEnd_8102253 4160350173332993631575923 := by
  unfold tailWord_8102253
  simp only [CollatzResearch.WordTrace]
  refine ⟨295513444315928610491175413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197008962877285740327450275 295513444315928610491175413)
  ·
    refine ⟨27704385404618307233547695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 295513444315928610491175413 27704385404618307233547695)
    ·
      refine ⟨41556578106927460850321543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27704385404618307233547695 41556578106927460850321543)
      ·
        refine ⟨62334867160391191275482315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41556578106927460850321543 62334867160391191275482315)
        ·
          refine ⟨93502300740586786913223473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62334867160391191275482315 93502300740586786913223473)
          ·
            refine ⟨70126725555440090184917605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93502300740586786913223473 70126725555440090184917605)
            ·
              refine ⟨13148761041645016909672051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70126725555440090184917605 13148761041645016909672051)
              ·
                refine ⟨19723141562467525364508077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13148761041645016909672051 19723141562467525364508077)
                ·
                  refine ⟨7396178085925322011690529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19723141562467525364508077 7396178085925322011690529)
                  ·
                    refine ⟨5547133564443991508767897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7396178085925322011690529 5547133564443991508767897)
                    ·
                      refine ⟨4160350173332993631575923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5547133564443991508767897 4160350173332993631575923)
                      ·
                        rfl

theorem cell23_8102253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_8102253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102253 prefixEnd_8102253 := by exact prefixLift 8102253
  have htrace : WordTrace (prefixWord ++ tailWord_8102253) baseStart_8102253 baseEnd_8102253 := by
    simpa [prefixWord, tailWord_8102253, baseEnd_8102253] using wordTrace_append hprefix tailTrace_8102253
  have hstable : (prefixWord ++ tailWord_8102253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102253).length < 2 ^ (prefixWord ++ tailWord_8102253).sum := by decide
  have hdescent : baseEnd_8102253 < baseStart_8102253 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102273 : List Nat := [1, 2, 4, 3, 1, 2, 2, 2, 1, 2, 3]
def baseStart_8102273 : Nat := 118140960795 + 8102273 * 2 ^ 59
def prefixEnd_8102273 : Nat := 4983230072969 + 3 ^ 40 * 8102273 * 2
def baseEnd_8102273 : Nat := 4160360442946083553325831

theorem tailTrace_8102273 : CollatzResearch.WordTrace tailWord_8102273 prefixEnd_8102273 4160360442946083553325831 := by
  unfold tailWord_8102273
  simp only [CollatzResearch.WordTrace]
  refine ⟨295514173775856153906903473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197009449183904102604602315 295514173775856153906903473)
  ·
    refine ⟨221635630331892115430177605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295514173775856153906903473 221635630331892115430177605)
    ·
      refine ⟨41556680687229771643158301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221635630331892115430177605 41556680687229771643158301)
      ·
        refine ⟨15583755257711164366184363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41556680687229771643158301 15583755257711164366184363)
        ·
          refine ⟨23375632886566746549276545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15583755257711164366184363 23375632886566746549276545)
          ·
            refine ⟨17531724664925059911957409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23375632886566746549276545 17531724664925059911957409)
            ·
              refine ⟨13148793498693794933968057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17531724664925059911957409 13148793498693794933968057)
              ·
                refine ⟨9861595124020346200476043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13148793498693794933968057 9861595124020346200476043)
                ·
                  refine ⟨14792392686030519300714065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9861595124020346200476043 14792392686030519300714065)
                  ·
                    refine ⟨11094294514522889475535549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14792392686030519300714065 11094294514522889475535549)
                    ·
                      refine ⟨4160360442946083553325831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11094294514522889475535549 4160360442946083553325831)
                      ·
                        rfl

theorem cell23_8102273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_8102273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102273 prefixEnd_8102273 := by exact prefixLift 8102273
  have htrace : WordTrace (prefixWord ++ tailWord_8102273) baseStart_8102273 baseEnd_8102273 := by
    simpa [prefixWord, tailWord_8102273, baseEnd_8102273] using wordTrace_append hprefix tailTrace_8102273
  have hstable : (prefixWord ++ tailWord_8102273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102273).length < 2 ^ (prefixWord ++ tailWord_8102273).sum := by decide
  have hdescent : baseEnd_8102273 < baseStart_8102273 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102314 : List Nat := [3, 1, 6, 1, 1, 2, 2, 1, 2, 4]
def baseStart_8102314 : Nat := 118140960795 + 8102314 * 2 ^ 59
def prefixEnd_8102314 : Nat := 4983230072969 + 3 ^ 40 * 8102314 * 2
def baseEnd_8102314 : Nat := 1386793831884305964304381

theorem tailTrace_8102314 : CollatzResearch.WordTrace tailWord_8102314 prefixEnd_8102314 1386793831884305964304381 := by
  unfold tailWord_8102314
  simp only [CollatzResearch.WordTrace]
  refine ⟨73878917292176904477286499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197010446112471745272763997 73878917292176904477286499)
  ·
    refine ⟨110818375938265356715929749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73878917292176904477286499 110818375938265356715929749)
    ·
      refine ⟨5194611372106188596059207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 110818375938265356715929749 5194611372106188596059207)
      ·
        refine ⟨7791917058159282894088811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5194611372106188596059207 7791917058159282894088811)
        ·
          refine ⟨11687875587238924341133217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7791917058159282894088811 11687875587238924341133217)
          ·
            refine ⟨8765906690429193255849913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11687875587238924341133217 8765906690429193255849913)
            ·
              refine ⟨6574430017821894941887435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8765906690429193255849913 6574430017821894941887435)
              ·
                refine ⟨9861645026732842412831153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6574430017821894941887435 9861645026732842412831153)
                ·
                  refine ⟨7396233770049631809623365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9861645026732842412831153 7396233770049631809623365)
                  ·
                    refine ⟨1386793831884305964304381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7396233770049631809623365 1386793831884305964304381)
                    ·
                      rfl

theorem cell23_8102314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_8102314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102314 prefixEnd_8102314 := by exact prefixLift 8102314
  have htrace : WordTrace (prefixWord ++ tailWord_8102314) baseStart_8102314 baseEnd_8102314 := by
    simpa [prefixWord, tailWord_8102314, baseEnd_8102314] using wordTrace_append hprefix tailTrace_8102314
  have hstable : (prefixWord ++ tailWord_8102314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102314).length < 2 ^ (prefixWord ++ tailWord_8102314).sum := by decide
  have hdescent : baseEnd_8102314 < baseStart_8102314 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102324 : List Nat := [2, 5, 2, 2, 2, 1, 1, 2, 1, 2, 3]
def baseStart_8102324 : Nat := 118140960795 + 8102324 * 2 ^ 59
def prefixEnd_8102324 : Nat := 4983230072969 + 3 ^ 40 * 8102324 * 2
def baseEnd_8102324 : Nat := 4160386630459462853788097

theorem tailTrace_8102324 : CollatzResearch.WordTrace tailWord_8102324 prefixEnd_8102324 4160386630459462853788097 := by
  unfold tailWord_8102324
  simp only [CollatzResearch.WordTrace]
  refine ⟨147758016949335694808505013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197010689265780926411340017 147758016949335694808505013)
  ·
    refine ⟨13852314089000221388297345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147758016949335694808505013 13852314089000221388297345)
    ·
      refine ⟨10389235566750166041223009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13852314089000221388297345 10389235566750166041223009)
      ·
        refine ⟨7791926675062624530917257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10389235566750166041223009 7791926675062624530917257)
        ·
          refine ⟨5843945006296968398187943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7791926675062624530917257 5843945006296968398187943)
          ·
            refine ⟨8765917509445452597281915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5843945006296968398187943 8765917509445452597281915)
            ·
              refine ⟨13148876264168178895922873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8765917509445452597281915 13148876264168178895922873)
              ·
                refine ⟨9861657198126134171942155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13148876264168178895922873 9861657198126134171942155)
                ·
                  refine ⟨14792485797189201257913233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9861657198126134171942155 14792485797189201257913233)
                  ·
                    refine ⟨11094364347891900943434925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14792485797189201257913233 11094364347891900943434925)
                    ·
                      refine ⟨4160386630459462853788097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11094364347891900943434925 4160386630459462853788097)
                      ·
                        rfl

theorem cell23_8102324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_8102324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102324 prefixEnd_8102324 := by exact prefixLift 8102324
  have htrace : WordTrace (prefixWord ++ tailWord_8102324) baseStart_8102324 baseEnd_8102324 := by
    simpa [prefixWord, tailWord_8102324, baseEnd_8102324] using wordTrace_append hprefix tailTrace_8102324
  have hstable : (prefixWord ++ tailWord_8102324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102324).length < 2 ^ (prefixWord ++ tailWord_8102324).sum := by decide
  have hdescent : baseEnd_8102324 < baseStart_8102324 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102329 : List Nat := [1, 2, 1, 4, 3, 1, 1, 2, 2, 1, 5]
def baseStart_8102329 : Nat := 118140960795 + 8102329 * 2 ^ 59
def prefixEnd_8102329 : Nat := 4983230072969 + 3 ^ 40 * 8102329 * 2
def baseEnd_8102329 : Nat := 4160389197862735334225573

theorem tailTrace_8102329 : CollatzResearch.WordTrace tailWord_8102329 prefixEnd_8102329 4160389197862735334225573 := by
  unfold tailWord_8102329
  simp only [CollatzResearch.WordTrace]
  refine ⟨295516216263653275470942041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197010810842435516980628027 295516216263653275470942041)
  ·
    refine ⟨221637162197739956603206531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295516216263653275470942041 221637162197739956603206531)
    ·
      refine ⟨332455743296609934904809797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221637162197739956603206531 332455743296609934904809797)
      ·
        refine ⟨62335451868114362794651837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 332455743296609934904809797 62335451868114362794651837)
        ·
          refine ⟨23375794450542886047994439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62335451868114362794651837 23375794450542886047994439)
          ·
            refine ⟨35063691675814329071991659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23375794450542886047994439 35063691675814329071991659)
            ·
              refine ⟨52595537513721493607987489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35063691675814329071991659 52595537513721493607987489)
              ·
                refine ⟨39446653135291120205990617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52595537513721493607987489 39446653135291120205990617)
                ·
                  refine ⟨29584989851468340154492963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39446653135291120205990617 29584989851468340154492963)
                  ·
                    refine ⟨44377484777202510231739445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29584989851468340154492963 44377484777202510231739445)
                    ·
                      refine ⟨4160389197862735334225573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44377484777202510231739445 4160389197862735334225573)
                      ·
                        rfl

theorem cell23_8102329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_8102329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102329 prefixEnd_8102329 := by exact prefixLift 8102329
  have htrace : WordTrace (prefixWord ++ tailWord_8102329) baseStart_8102329 baseEnd_8102329 := by
    simpa [prefixWord, tailWord_8102329, baseEnd_8102329] using wordTrace_append hprefix tailTrace_8102329
  have hstable : (prefixWord ++ tailWord_8102329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102329).length < 2 ^ (prefixWord ++ tailWord_8102329).sum := by decide
  have hdescent : baseEnd_8102329 < baseStart_8102329 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102352 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 6]
def baseStart_8102352 : Nat := 118140960795 + 8102352 * 2 ^ 59
def prefixEnd_8102352 : Nat := 4983230072969 + 3 ^ 40 * 8102352 * 2
def baseEnd_8102352 : Nat := 4160401007917788744237967

theorem tailTrace_8102352 : CollatzResearch.WordTrace tailWord_8102352 prefixEnd_8102352 4160401007917788744237967 := by
  unfold tailWord_8102352
  simp only [CollatzResearch.WordTrace]
  refine ⟨147758527571284975199514655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197011370095046633599352873 147758527571284975199514655)
  ·
    refine ⟨221637791356927462799271983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147758527571284975199514655 221637791356927462799271983)
    ·
      refine ⟨332456687035391194198907975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221637791356927462799271983 332456687035391194198907975)
      ·
        refine ⟨498685030553086791298361963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332456687035391194198907975 498685030553086791298361963)
        ·
          refine ⟨748027545829630186947542945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498685030553086791298361963 748027545829630186947542945)
          ·
            refine ⟨561020659372222640210657209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 748027545829630186947542945 561020659372222640210657209)
            ·
              refine ⟨420765494529166980157992907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 561020659372222640210657209 420765494529166980157992907)
              ·
                refine ⟨631148241793750470236989361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420765494529166980157992907 631148241793750470236989361)
                ·
                  refine ⟨473361181345312852677742021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 631148241793750470236989361 473361181345312852677742021)
                  ·
                    refine ⟨88755221502246159877076629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 473361181345312852677742021 88755221502246159877076629)
                    ·
                      refine ⟨4160401007917788744237967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88755221502246159877076629 4160401007917788744237967)
                      ·
                        rfl

theorem cell23_8102352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 6].length) (baseStart_8102352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102352 prefixEnd_8102352 := by exact prefixLift 8102352
  have htrace : WordTrace (prefixWord ++ tailWord_8102352) baseStart_8102352 baseEnd_8102352 := by
    simpa [prefixWord, tailWord_8102352, baseEnd_8102352] using wordTrace_append hprefix tailTrace_8102352
  have hstable : (prefixWord ++ tailWord_8102352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102352).length < 2 ^ (prefixWord ++ tailWord_8102352).sum := by decide
  have hdescent : baseEnd_8102352 < baseStart_8102352 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102376 : List Nat := [2, 1, 4, 1, 1, 4, 1, 1, 2, 3, 3]
def baseStart_8102376 : Nat := 118140960795 + 8102376 * 2 ^ 59
def prefixEnd_8102376 : Nat := 4983230072969 + 3 ^ 40 * 8102376 * 2
def baseEnd_8102376 : Nat := 4160413331453496650337857

theorem tailTrace_8102376 : CollatzResearch.WordTrace tailWord_8102376 prefixEnd_8102376 4160413331453496650337857 := by
  unfold tailWord_8102376
  simp only [CollatzResearch.WordTrace]
  refine ⟨147758965247241501248951491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197011953662988668331935321 147758965247241501248951491)
  ·
    refine ⟨221638447870862251873427237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147758965247241501248951491 221638447870862251873427237)
    ·
      refine ⟨41557208975786672226267607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221638447870862251873427237 41557208975786672226267607)
      ·
        refine ⟨62335813463680008339401411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41557208975786672226267607 62335813463680008339401411)
        ·
          refine ⟨93503720195520012509102117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62335813463680008339401411 93503720195520012509102117)
          ·
            refine ⟨17531947536660002345456647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93503720195520012509102117 17531947536660002345456647)
            ·
              refine ⟨26297921304990003518184971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17531947536660002345456647 26297921304990003518184971)
              ·
                refine ⟨39446881957485005277277457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26297921304990003518184971 39446881957485005277277457)
                ·
                  refine ⟨29585161468113753957958093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39446881957485005277277457 29585161468113753957958093)
                  ·
                    refine ⟨11094435550542657734234285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29585161468113753957958093 11094435550542657734234285)
                    ·
                      refine ⟨4160413331453496650337857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11094435550542657734234285 4160413331453496650337857)
                      ·
                        rfl

theorem cell23_8102376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_8102376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102376 prefixEnd_8102376 := by exact prefixLift 8102376
  have htrace : WordTrace (prefixWord ++ tailWord_8102376) baseStart_8102376 baseEnd_8102376 := by
    simpa [prefixWord, tailWord_8102376, baseEnd_8102376] using wordTrace_append hprefix tailTrace_8102376
  have hstable : (prefixWord ++ tailWord_8102376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102376).length < 2 ^ (prefixWord ++ tailWord_8102376).sum := by decide
  have hdescent : baseEnd_8102376 < baseStart_8102376 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102399 : List Nat := [1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 4]
def baseStart_8102399 : Nat := 118140960795 + 8102399 * 2 ^ 59
def prefixEnd_8102399 : Nat := 4983230072969 + 3 ^ 40 * 8102399 * 2
def baseEnd_8102399 : Nat := 4160425141508550060350251

theorem tailTrace_8102399 : CollatzResearch.WordTrace tailWord_8102399 prefixEnd_8102399 4160425141508550060350251 := by
  unfold tailWord_8102399
  simp only [CollatzResearch.WordTrace]
  refine ⟨295518769373399677425990251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197012512915599784950660167 295518769373399677425990251)
  ·
    refine ⟨443278154060099516138985377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295518769373399677425990251 443278154060099516138985377)
    ·
      refine ⟨332458615545074637104239033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443278154060099516138985377 332458615545074637104239033)
      ·
        refine ⟨249343961658805977828179275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332458615545074637104239033 249343961658805977828179275)
        ·
          refine ⟨374015942488208966742268913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249343961658805977828179275 374015942488208966742268913)
          ·
            refine ⟨280511956866156725056701685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374015942488208966742268913 280511956866156725056701685)
            ·
              refine ⟨26297995956202192974065783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 280511956866156725056701685 26297995956202192974065783)
              ·
                refine ⟨39446993934303289461098675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26297995956202192974065783 39446993934303289461098675)
                ·
                  refine ⟨59170490901454934191648013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39446993934303289461098675 59170490901454934191648013)
                  ·
                    refine ⟨22188934088045600321868005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59170490901454934191648013 22188934088045600321868005)
                    ·
                      refine ⟨4160425141508550060350251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22188934088045600321868005 4160425141508550060350251)
                      ·
                        rfl

theorem cell23_8102399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_8102399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102399 prefixEnd_8102399 := by exact prefixLift 8102399
  have htrace : WordTrace (prefixWord ++ tailWord_8102399) baseStart_8102399 baseEnd_8102399 := by
    simpa [prefixWord, tailWord_8102399, baseEnd_8102399] using wordTrace_append hprefix tailTrace_8102399
  have hstable : (prefixWord ++ tailWord_8102399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102399).length < 2 ^ (prefixWord ++ tailWord_8102399).sum := by decide
  have hdescent : baseEnd_8102399 < baseStart_8102399 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102426 : List Nat := [3, 1, 1, 3, 1, 1, 3, 3, 3, 4]
def baseStart_8102426 : Nat := 118140960795 + 8102426 * 2 ^ 59
def prefixEnd_8102426 : Nat := 4983230072969 + 3 ^ 40 * 8102426 * 2
def baseEnd_8102426 : Nat := 1386813001828740484904209

theorem tailTrace_8102426 : CollatzResearch.WordTrace tailWord_8102426 prefixEnd_8102426 1386813001828740484904209 := by
  unfold tailWord_8102426
  simp only [CollatzResearch.WordTrace]
  refine ⟨73879938536075465259305783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197013169429534574024815421 73879938536075465259305783)
  ·
    refine ⟨110819907804113197888958675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73879938536075465259305783 110819907804113197888958675)
    ·
      refine ⟨166229861706169796833438013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110819907804113197888958675 166229861706169796833438013)
      ·
        refine ⟨62336198139813673812539255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166229861706169796833438013 62336198139813673812539255)
        ·
          refine ⟨93504297209720510718808883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62336198139813673812539255 93504297209720510718808883)
          ·
            refine ⟨140256445814580766078213325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93504297209720510718808883 140256445814580766078213325)
            ·
              refine ⟨52596167180467787279329997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140256445814580766078213325 52596167180467787279329997)
              ·
                refine ⟨19723562692675420229748749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52596167180467787279329997 19723562692675420229748749)
                ·
                  refine ⟨7396336009753282586155781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19723562692675420229748749 7396336009753282586155781)
                  ·
                    refine ⟨1386813001828740484904209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7396336009753282586155781 1386813001828740484904209)
                    ·
                      rfl

theorem cell23_8102426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 3, 4].length) (baseStart_8102426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102426 prefixEnd_8102426 := by exact prefixLift 8102426
  have htrace : WordTrace (prefixWord ++ tailWord_8102426) baseStart_8102426 baseEnd_8102426 := by
    simpa [prefixWord, tailWord_8102426, baseEnd_8102426] using wordTrace_append hprefix tailTrace_8102426
  have hstable : (prefixWord ++ tailWord_8102426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102426).length < 2 ^ (prefixWord ++ tailWord_8102426).sum := by decide
  have hdescent : baseEnd_8102426 < baseStart_8102426 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102460 : List Nat := [2, 2, 2, 2, 3, 1, 3, 3, 1, 4]
def baseStart_8102460 : Nat := 118140960795 + 8102460 * 2 ^ 59
def prefixEnd_8102460 : Nat := 4983230072969 + 3 ^ 40 * 8102460 * 2
def baseEnd_8102460 : Nat := 1386818821276158107229157

theorem tailTrace_8102460 : CollatzResearch.WordTrace tailWord_8102460 prefixEnd_8102460 1386818821276158107229157 := by
  unfold tailWord_8102460
  simp only [CollatzResearch.WordTrace]
  refine ⟨147760497113089342421980417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197013996150785789895973889 147760497113089342421980417)
  ·
    refine ⟨110820372834817006816485313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147760497113089342421980417 110820372834817006816485313)
    ·
      refine ⟨83115279626112755112363985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110820372834817006816485313 83115279626112755112363985)
      ·
        refine ⟨62336459719584566334272989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83115279626112755112363985 62336459719584566334272989)
        ·
          refine ⟨23376172394844212375352371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62336459719584566334272989 23376172394844212375352371)
          ·
            refine ⟨35064258592266318563028557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23376172394844212375352371 35064258592266318563028557)
            ·
              refine ⟨13149096972099869461135709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35064258592266318563028557 13149096972099869461135709)
              ·
                refine ⟨4930911364537451047925891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13149096972099869461135709 4930911364537451047925891)
                ·
                  refine ⟨7396367046806176571888837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4930911364537451047925891 7396367046806176571888837)
                  ·
                    refine ⟨1386818821276158107229157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7396367046806176571888837 1386818821276158107229157)
                    ·
                      rfl

theorem cell23_8102460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_8102460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102460 prefixEnd_8102460 := by exact prefixLift 8102460
  have htrace : WordTrace (prefixWord ++ tailWord_8102460) baseStart_8102460 baseEnd_8102460 := by
    simpa [prefixWord, tailWord_8102460, baseEnd_8102460] using wordTrace_append hprefix tailTrace_8102460
  have hstable : (prefixWord ++ tailWord_8102460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102460).length < 2 ^ (prefixWord ++ tailWord_8102460).sum := by decide
  have hdescent : baseEnd_8102460 < baseStart_8102460 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102470 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3]
def baseStart_8102470 : Nat := 118140960795 + 8102470 * 2 ^ 59
def prefixEnd_8102470 : Nat := 4983230072969 + 3 ^ 40 * 8102470 * 2
def baseEnd_8102470 : Nat := 4160461598635019282562425

theorem tailTrace_8102470 : CollatzResearch.WordTrace tailWord_8102470 prefixEnd_8102470 4160461598635019282562425 := by
  unfold tailWord_8102470
  simp only [CollatzResearch.WordTrace]
  refine ⟨9235042467379451767244527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 197014239304094971034549909 9235042467379451767244527)
  ·
    refine ⟨13852563701069177650866791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9235042467379451767244527 13852563701069177650866791)
    ·
      refine ⟨20778845551603766476300187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13852563701069177650866791 20778845551603766476300187)
      ·
        refine ⟨31168268327405649714450281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20778845551603766476300187 31168268327405649714450281)
        ·
          refine ⟨23376201245554237285837711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31168268327405649714450281 23376201245554237285837711)
          ·
            refine ⟨35064301868331355928756567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23376201245554237285837711 35064301868331355928756567)
            ·
              refine ⟨52596452802497033893134851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35064301868331355928756567 52596452802497033893134851)
              ·
                refine ⟨78894679203745550839702277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52596452802497033893134851 78894679203745550839702277)
                ·
                  refine ⟨14792752350702290782444177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78894679203745550839702277 14792752350702290782444177)
                  ·
                    refine ⟨11094564263026718086833133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14792752350702290782444177 11094564263026718086833133)
                    ·
                      refine ⟨4160461598635019282562425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11094564263026718086833133 4160461598635019282562425)
                      ·
                        rfl

theorem cell23_8102470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_8102470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102470 prefixEnd_8102470 := by exact prefixLift 8102470
  have htrace : WordTrace (prefixWord ++ tailWord_8102470) baseStart_8102470 baseEnd_8102470 := by
    simpa [prefixWord, tailWord_8102470, baseEnd_8102470] using wordTrace_append hprefix tailTrace_8102470
  have hstable : (prefixWord ++ tailWord_8102470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102470).length < 2 ^ (prefixWord ++ tailWord_8102470).sum := by decide
  have hdescent : baseEnd_8102470 < baseStart_8102470 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102489 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 1, 7, 4]
def baseStart_8102489 : Nat := 118140960795 + 8102489 * 2 ^ 59
def prefixEnd_8102489 : Nat := 4983230072969 + 3 ^ 40 * 8102489 * 2
def baseEnd_8102489 : Nat := 4160471354767454708224837

theorem tailTrace_8102489 : CollatzResearch.WordTrace tailWord_8102489 prefixEnd_8102489 4160471354767454708224837 := by
  unfold tailWord_8102489
  simp only [CollatzResearch.WordTrace]
  refine ⟨295522051943073622796766521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197014701295382415197844347 295522051943073622796766521)
  ·
    refine ⟨221641538957305217097574891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295522051943073622796766521 221641538957305217097574891)
    ·
      refine ⟨332462308435957825646362337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221641538957305217097574891 332462308435957825646362337)
      ·
        refine ⟨249346731326968369234771753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332462308435957825646362337 249346731326968369234771753)
        ·
          refine ⟨187010048495226276926078815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249346731326968369234771753 187010048495226276926078815)
          ·
            refine ⟨280515072742839415389118223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187010048495226276926078815 280515072742839415389118223)
            ·
              refine ⟨420772609114259123083677335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280515072742839415389118223 420772609114259123083677335)
              ·
                refine ⟨631158913671388684625516003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420772609114259123083677335 631158913671388684625516003)
                ·
                  refine ⟨946738370507083026938274005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 631158913671388684625516003 946738370507083026938274005)
                  ·
                    refine ⟨22189180558759758443865797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 946738370507083026938274005 22189180558759758443865797)
                    ·
                      refine ⟨4160471354767454708224837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22189180558759758443865797 4160471354767454708224837)
                      ·
                        rfl

theorem cell23_8102489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_8102489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102489 prefixEnd_8102489 := by exact prefixLift 8102489
  have htrace : WordTrace (prefixWord ++ tailWord_8102489) baseStart_8102489 baseEnd_8102489 := by
    simpa [prefixWord, tailWord_8102489, baseEnd_8102489] using wordTrace_append hprefix tailTrace_8102489
  have hstable : (prefixWord ++ tailWord_8102489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102489).length < 2 ^ (prefixWord ++ tailWord_8102489).sum := by decide
  have hdescent : baseEnd_8102489 < baseStart_8102489 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102510 : List Nat := [4, 1, 2, 2, 2, 1, 1, 3, 2, 3, 2]
def baseStart_8102510 : Nat := 118140960795 + 8102510 * 2 ^ 59
def prefixEnd_8102510 : Nat := 4983230072969 + 3 ^ 40 * 8102510 * 2
def baseEnd_8102510 : Nat := 4160482137861199126062241

theorem tailTrace_8102510 : CollatzResearch.WordTrace tailWord_8102510 prefixEnd_8102510 4160482137861199126062241 := by
  unfold tailWord_8102510
  simp only [CollatzResearch.WordTrace]
  refine ⟨36940352234499692922910123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197015211917331695588853989 36940352234499692922910123)
  ·
    refine ⟨55410528351749539384365185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36940352234499692922910123 55410528351749539384365185)
    ·
      refine ⟨41557896263812154538273889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55410528351749539384365185 41557896263812154538273889)
      ·
        refine ⟨31168422197859115903705417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41557896263812154538273889 31168422197859115903705417)
        ·
          refine ⟨23376316648394336927779063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31168422197859115903705417 23376316648394336927779063)
          ·
            refine ⟨35064474972591505391668595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23376316648394336927779063 35064474972591505391668595)
            ·
              refine ⟨52596712458887258087502893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35064474972591505391668595 52596712458887258087502893)
              ·
                refine ⟨19723767172082721782813585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52596712458887258087502893 19723767172082721782813585)
                ·
                  refine ⟨14792825379062041337110189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19723767172082721782813585 14792825379062041337110189)
                  ·
                    refine ⟨5547309517148265501416321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14792825379062041337110189 5547309517148265501416321)
                    ·
                      refine ⟨4160482137861199126062241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5547309517148265501416321 4160482137861199126062241)
                      ·
                        rfl

theorem cell23_8102510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_8102510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102510 prefixEnd_8102510 := by exact prefixLift 8102510
  have htrace : WordTrace (prefixWord ++ tailWord_8102510) baseStart_8102510 baseEnd_8102510 := by
    simpa [prefixWord, tailWord_8102510, baseEnd_8102510] using wordTrace_append hprefix tailTrace_8102510
  have hstable : (prefixWord ++ tailWord_8102510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102510).length < 2 ^ (prefixWord ++ tailWord_8102510).sum := by decide
  have hdescent : baseEnd_8102510 < baseStart_8102510 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102523 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 7, 2, 2]
def baseStart_8102523 : Nat := 118140960795 + 8102523 * 2 ^ 59
def prefixEnd_8102523 : Nat := 4983230072969 + 3 ^ 40 * 8102523 * 2
def baseEnd_8102523 : Nat := 4160488813109707575199681

theorem tailTrace_8102523 : CollatzResearch.WordTrace tailWord_8102523 prefixEnd_8102523 4160488813109707575199681 := by
  unfold tailWord_8102523
  simp only [CollatzResearch.WordTrace]
  refine ⟨295523292024950446603504223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197015528016633631069002815 295523292024950446603504223)
  ·
    refine ⟨443284938037425669905256335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295523292024950446603504223 443284938037425669905256335)
    ·
      refine ⟨664927407056138504857884503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443284938037425669905256335 664927407056138504857884503)
      ·
        refine ⟨997391110584207757286826755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664927407056138504857884503 997391110584207757286826755)
        ·
          refine ⟨1496086665876311635930240133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 997391110584207757286826755 1496086665876311635930240133)
          ·
            refine ⟨280516249851808431736920025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1496086665876311635930240133 280516249851808431736920025)
            ·
              refine ⟨210387187388856323802690019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280516249851808431736920025 210387187388856323802690019)
              ·
                refine ⟨315580781083284485704035029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210387187388856323802690019 315580781083284485704035029)
                ·
                  refine ⟨7396424556639480133688321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 315580781083284485704035029 7396424556639480133688321)
                  ·
                    refine ⟨5547318417479610100266241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7396424556639480133688321 5547318417479610100266241)
                    ·
                      refine ⟨4160488813109707575199681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5547318417479610100266241 4160488813109707575199681)
                      ·
                        rfl

theorem cell23_8102523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 7, 2, 2].length) (baseStart_8102523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102523 prefixEnd_8102523 := by exact prefixLift 8102523
  have htrace : WordTrace (prefixWord ++ tailWord_8102523) baseStart_8102523 baseEnd_8102523 := by
    simpa [prefixWord, tailWord_8102523, baseEnd_8102523] using wordTrace_append hprefix tailTrace_8102523
  have hstable : (prefixWord ++ tailWord_8102523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102523).length < 2 ^ (prefixWord ++ tailWord_8102523).sum := by decide
  have hdescent : baseEnd_8102523 < baseStart_8102523 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102533 : List Nat := [1, 3, 1, 1, 4, 2, 1, 4, 2, 4]
def baseStart_8102533 : Nat := 118140960795 + 8102533 * 2 ^ 59
def prefixEnd_8102533 : Nat := 4983230072969 + 3 ^ 40 * 8102533 * 2
def baseEnd_8102533 : Nat := 1386831315972084178691545

theorem tailTrace_8102533 : CollatzResearch.WordTrace tailWord_8102533 prefixEnd_8102533 1386831315972084178691545 := by
  unfold tailWord_8102533
  simp only [CollatzResearch.WordTrace]
  refine ⟨295523656754914218311368253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197015771169942812207578835 295523656754914218311368253)
  ·
    refine ⟨110821371283092831866763095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295523656754914218311368253 110821371283092831866763095)
    ·
      refine ⟨166232056924639247800144643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110821371283092831866763095 166232056924639247800144643)
      ·
        refine ⟨249348085386958871700216965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166232056924639247800144643 249348085386958871700216965)
        ·
          refine ⟨46752766010054788443790681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249348085386958871700216965 46752766010054788443790681)
          ·
            refine ⟨35064574507541091332843011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46752766010054788443790681 35064574507541091332843011)
            ·
              refine ⟨52596861761311636999264517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35064574507541091332843011 52596861761311636999264517)
              ·
                refine ⟨9861911580245931937362097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52596861761311636999264517 9861911580245931937362097)
                ·
                  refine ⟨7396433685184448953021573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9861911580245931937362097 7396433685184448953021573)
                  ·
                    refine ⟨1386831315972084178691545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7396433685184448953021573 1386831315972084178691545)
                    ·
                      rfl

theorem cell23_8102533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 2, 4].length) (baseStart_8102533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102533 prefixEnd_8102533 := by exact prefixLift 8102533
  have htrace : WordTrace (prefixWord ++ tailWord_8102533) baseStart_8102533 baseEnd_8102533 := by
    simpa [prefixWord, tailWord_8102533, baseEnd_8102533] using wordTrace_append hprefix tailTrace_8102533
  have hstable : (prefixWord ++ tailWord_8102533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102533).length < 2 ^ (prefixWord ++ tailWord_8102533).sum := by decide
  have hdescent : baseEnd_8102533 < baseStart_8102533 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102539 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 7]
def baseStart_8102539 : Nat := 118140960795 + 8102539 * 2 ^ 59
def prefixEnd_8102539 : Nat := 4983230072969 + 3 ^ 40 * 8102539 * 2
def baseEnd_8102539 : Nat := 4160497028800179512599607

theorem tailTrace_8102539 : CollatzResearch.WordTrace tailWord_8102539 prefixEnd_8102539 4160497028800179512599607 := by
  unfold tailWord_8102539
  simp only [CollatzResearch.WordTrace]
  refine ⟨295523875592892481336086671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197015917061928320890724447 295523875592892481336086671)
  ·
    refine ⟨443285813389338722004130007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295523875592892481336086671 443285813389338722004130007)
    ·
      refine ⟨664928720084008083006195011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443285813389338722004130007 664928720084008083006195011)
      ·
        refine ⟨997393080126012124509292517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664928720084008083006195011 997393080126012124509292517)
        ·
          refine ⟨187011202523627273345492347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 997393080126012124509292517 187011202523627273345492347)
          ·
            refine ⟨280516803785440910018238521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187011202523627273345492347 280516803785440910018238521)
            ·
              refine ⟨210387602839080682513678891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280516803785440910018238521 210387602839080682513678891)
              ·
                refine ⟨315581404258621023770518337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210387602839080682513678891 315581404258621023770518337)
                ·
                  refine ⟨236686053193965767827888753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 315581404258621023770518337 236686053193965767827888753)
                  ·
                    refine ⟨177514539895474325870916565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 236686053193965767827888753 177514539895474325870916565)
                    ·
                      refine ⟨4160497028800179512599607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177514539895474325870916565 4160497028800179512599607)
                      ·
                        rfl

theorem cell23_8102539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 7].length) (baseStart_8102539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102539 prefixEnd_8102539 := by exact prefixLift 8102539
  have htrace : WordTrace (prefixWord ++ tailWord_8102539) baseStart_8102539 baseEnd_8102539 := by
    simpa [prefixWord, tailWord_8102539, baseEnd_8102539] using wordTrace_append hprefix tailTrace_8102539
  have hstable : (prefixWord ++ tailWord_8102539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102539).length < 2 ^ (prefixWord ++ tailWord_8102539).sum := by decide
  have hdescent : baseEnd_8102539 < baseStart_8102539 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102574 : List Nat := [4, 1, 4, 1, 1, 3, 2, 1, 1, 1, 4]
def baseStart_8102574 : Nat := 118140960795 + 8102574 * 2 ^ 59
def prefixEnd_8102574 : Nat := 4983230072969 + 3 ^ 40 * 8102574 * 2
def baseEnd_8102574 : Nat := 4160515000623086875661947

theorem tailTrace_8102574 : CollatzResearch.WordTrace tailWord_8102574 prefixEnd_8102574 4160515000623086875661947 := by
  unfold tailWord_8102574
  simp only [CollatzResearch.WordTrace]
  refine ⟨36940644018470710289201347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197016768098510454875740517 36940644018470710289201347)
  ·
    refine ⟨55410966027706065433802021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36940644018470710289201347 55410966027706065433802021)
    ·
      refine ⟨10389556130194887268837879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55410966027706065433802021 10389556130194887268837879)
      ·
        refine ⟨15584334195292330903256819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10389556130194887268837879 15584334195292330903256819)
        ·
          refine ⟨23376501292938496354885229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15584334195292330903256819 23376501292938496354885229)
          ·
            refine ⟨8766187984851936133081961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23376501292938496354885229 8766187984851936133081961)
            ·
              refine ⟨6574640988638952099811471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8766187984851936133081961 6574640988638952099811471)
              ·
                refine ⟨9861961482958428149717207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6574640988638952099811471 9861961482958428149717207)
                ·
                  refine ⟨14792942224437642224575811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9861961482958428149717207 14792942224437642224575811)
                  ·
                    refine ⟨22189413336656463336863717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14792942224437642224575811 22189413336656463336863717)
                    ·
                      refine ⟨4160515000623086875661947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22189413336656463336863717 4160515000623086875661947)
                      ·
                        rfl

theorem cell23_8102574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_8102574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102574 prefixEnd_8102574 := by exact prefixLift 8102574
  have htrace : WordTrace (prefixWord ++ tailWord_8102574) baseStart_8102574 baseEnd_8102574 := by
    simpa [prefixWord, tailWord_8102574, baseEnd_8102574] using wordTrace_append hprefix tailTrace_8102574
  have hstable : (prefixWord ++ tailWord_8102574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102574).length < 2 ^ (prefixWord ++ tailWord_8102574).sum := by decide
  have hdescent : baseEnd_8102574 < baseStart_8102574 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102577 : List Nat := [1, 2, 2, 6, 1, 1, 1, 3, 1, 2, 3]
def baseStart_8102577 : Nat := 118140960795 + 8102577 * 2 ^ 59
def prefixEnd_8102577 : Nat := 4983230072969 + 3 ^ 40 * 8102577 * 2
def baseEnd_8102577 : Nat := 4160516541065050363924433

theorem tailTrace_8102577 : CollatzResearch.WordTrace tailWord_8102577 prefixEnd_8102577 4160516541065050363924433 := by
  unfold tailWord_8102577
  simp only [CollatzResearch.WordTrace]
  refine ⟨295525261566754813825969985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197016841044503209217313323 295525261566754813825969985)
  ·
    refine ⟨221643946175066110369477489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295525261566754813825969985 221643946175066110369477489)
    ·
      refine ⟨166232959631299582777108117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221643946175066110369477489 166232959631299582777108117)
      ·
        refine ⟨7792169982717167942676943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 166232959631299582777108117 7792169982717167942676943)
        ·
          refine ⟨11688254974075751914015415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7792169982717167942676943 11688254974075751914015415)
          ·
            refine ⟨17532382461113627871023123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11688254974075751914015415 17532382461113627871023123)
            ·
              refine ⟨26298573691670441806534685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17532382461113627871023123 26298573691670441806534685)
              ·
                refine ⟨9861965134376415677450507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26298573691670441806534685 9861965134376415677450507)
                ·
                  refine ⟨14792947701564623516175761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9861965134376415677450507 14792947701564623516175761)
                  ·
                    refine ⟨11094710776173467637131821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14792947701564623516175761 11094710776173467637131821)
                    ·
                      refine ⟨4160516541065050363924433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11094710776173467637131821 4160516541065050363924433)
                      ·
                        rfl

theorem cell23_8102577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_8102577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102577 prefixEnd_8102577 := by exact prefixLift 8102577
  have htrace : WordTrace (prefixWord ++ tailWord_8102577) baseStart_8102577 baseEnd_8102577 := by
    simpa [prefixWord, tailWord_8102577, baseEnd_8102577] using wordTrace_append hprefix tailTrace_8102577
  have hstable : (prefixWord ++ tailWord_8102577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102577).length < 2 ^ (prefixWord ++ tailWord_8102577).sum := by decide
  have hdescent : baseEnd_8102577 < baseStart_8102577 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102590 : List Nat := [4, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3]
def baseStart_8102590 : Nat := 118140960795 + 8102590 * 2 ^ 59
def prefixEnd_8102590 : Nat := 4983230072969 + 3 ^ 40 * 8102590 * 2
def baseEnd_8102590 : Nat := 4160523216313558813061873

theorem tailTrace_8102590 : CollatzResearch.WordTrace tailWord_8102590 prefixEnd_8102590 4160523216313558813061873 := by
  unfold tailWord_8102590
  simp only [CollatzResearch.WordTrace]
  refine ⟨36940716964463464630774153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197017157143805144697462149 36940716964463464630774153)
  ·
    refine ⟨27705537723347598473080615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36940716964463464630774153 27705537723347598473080615)
    ·
      refine ⟨41558306585021397709620923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27705537723347598473080615 41558306585021397709620923)
      ·
        refine ⟨62337459877532096564431385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41558306585021397709620923 62337459877532096564431385)
        ·
          refine ⟨46753094908149072423323539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62337459877532096564431385 46753094908149072423323539)
          ·
            refine ⟨70129642362223608634985309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46753094908149072423323539 70129642362223608634985309)
            ·
              refine ⟨26298615885833853238119491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70129642362223608634985309 26298615885833853238119491)
              ·
                refine ⟨39447923828750779857179237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26298615885833853238119491 39447923828750779857179237)
                ·
                  refine ⟨7396485717890771223221107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39447923828750779857179237 7396485717890771223221107)
                  ·
                    refine ⟨11094728576836156834831661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7396485717890771223221107 11094728576836156834831661)
                    ·
                      refine ⟨4160523216313558813061873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11094728576836156834831661 4160523216313558813061873)
                      ·
                        rfl

theorem cell23_8102590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_8102590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102590 prefixEnd_8102590 := by exact prefixLift 8102590
  have htrace : WordTrace (prefixWord ++ tailWord_8102590) baseStart_8102590 baseEnd_8102590 := by
    simpa [prefixWord, tailWord_8102590, baseEnd_8102590] using wordTrace_append hprefix tailTrace_8102590
  have hstable : (prefixWord ++ tailWord_8102590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102590).length < 2 ^ (prefixWord ++ tailWord_8102590).sum := by decide
  have hdescent : baseEnd_8102590 < baseStart_8102590 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102664 : List Nat := [2, 1, 3, 2, 2, 2, 4, 1, 2, 2, 2]
def baseStart_8102664 : Nat := 118140960795 + 8102664 * 2 ^ 59
def prefixEnd_8102664 : Nat := 4983230072969 + 3 ^ 40 * 8102664 * 2
def baseEnd_8102664 : Nat := 4160561213881991523536533

theorem tailTrace_8102664 : CollatzResearch.WordTrace tailWord_8102664 prefixEnd_8102664 4160561213881991523536533 := by
  unfold tailWord_8102664
  simp only [CollatzResearch.WordTrace]
  refine ⟨147764217358719813842193523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197018956478293085122924697 147764217358719813842193523)
  ·
    refine ⟨221646326038079720763290285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147764217358719813842193523 221646326038079720763290285)
    ·
      refine ⟨83117372264279895286233857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221646326038079720763290285 83117372264279895286233857)
      ·
        refine ⟨62338029198209921464675393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83117372264279895286233857 62338029198209921464675393)
        ·
          refine ⟨46753521898657441098506545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62338029198209921464675393 46753521898657441098506545)
          ·
            refine ⟨35065141423993080823879909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46753521898657441098506545 35065141423993080823879909)
            ·
              refine ⟨6574714016998702654477483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35065141423993080823879909 6574714016998702654477483)
              ·
                refine ⟨9862071025498053981716225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6574714016998702654477483 9862071025498053981716225)
                ·
                  refine ⟨7396553269123540486287169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9862071025498053981716225 7396553269123540486287169)
                  ·
                    refine ⟨5547414951842655364715377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7396553269123540486287169 5547414951842655364715377)
                    ·
                      refine ⟨4160561213881991523536533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5547414951842655364715377 4160561213881991523536533)
                      ·
                        rfl

theorem cell23_8102664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_8102664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102664 prefixEnd_8102664 := by exact prefixLift 8102664
  have htrace : WordTrace (prefixWord ++ tailWord_8102664) baseStart_8102664 baseEnd_8102664 := by
    simpa [prefixWord, tailWord_8102664, baseEnd_8102664] using wordTrace_append hprefix tailTrace_8102664
  have hstable : (prefixWord ++ tailWord_8102664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102664).length < 2 ^ (prefixWord ++ tailWord_8102664).sum := by decide
  have hdescent : baseEnd_8102664 < baseStart_8102664 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102723 : List Nat := [1, 1, 1, 3, 1, 4, 2, 2, 1, 4, 3]
def baseStart_8102723 : Nat := 118140960795 + 8102723 * 2 ^ 59
def prefixEnd_8102723 : Nat := 4983230072969 + 3 ^ 40 * 8102723 * 2
def baseEnd_8102723 : Nat := 4160591509240606792698761

theorem tailTrace_8102723 : CollatzResearch.WordTrace tailWord_8102723 prefixEnd_8102723 4160591509240606792698761 := by
  unfold tailWord_8102723
  simp only [CollatzResearch.WordTrace]
  refine ⟨295530586624225880760784823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197020391082817253840523215 295530586624225880760784823)
  ·
    refine ⟨443295879936338821141177235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295530586624225880760784823 443295879936338821141177235)
    ·
      refine ⟨664943819904508231711765853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443295879936338821141177235 664943819904508231711765853)
      ·
        refine ⟨249353932464190586891912195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 664943819904508231711765853 249353932464190586891912195)
        ·
          refine ⟨374030898696285880337868293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249353932464190586891912195 374030898696285880337868293)
          ·
            refine ⟨70130793505553602563350305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 374030898696285880337868293 70130793505553602563350305)
            ·
              refine ⟨52598095129165201922512729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70130793505553602563350305 52598095129165201922512729)
              ·
                refine ⟨39448571346873901441884547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52598095129165201922512729 39448571346873901441884547)
                ·
                  refine ⟨59172857020310852162826821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39448571346873901441884547 59172857020310852162826821)
                  ·
                    refine ⟨11094910691308284780530029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59172857020310852162826821 11094910691308284780530029)
                    ·
                      refine ⟨4160591509240606792698761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11094910691308284780530029 4160591509240606792698761)
                      ·
                        rfl

theorem cell23_8102723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 4, 3].length) (baseStart_8102723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102723 prefixEnd_8102723 := by exact prefixLift 8102723
  have htrace : WordTrace (prefixWord ++ tailWord_8102723) baseStart_8102723 baseEnd_8102723 := by
    simpa [prefixWord, tailWord_8102723, baseEnd_8102723] using wordTrace_append hprefix tailTrace_8102723
  have hstable : (prefixWord ++ tailWord_8102723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102723).length < 2 ^ (prefixWord ++ tailWord_8102723).sum := by decide
  have hdescent : baseEnd_8102723 < baseStart_8102723 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102737 : List Nat := [1, 2, 2, 1, 6, 2, 1, 1, 2, 1, 4]
def baseStart_8102737 : Nat := 118140960795 + 8102737 * 2 ^ 59
def prefixEnd_8102737 : Nat := 4983230072969 + 3 ^ 40 * 8102737 * 2
def baseEnd_8102737 : Nat := 4160598697969769737923697

theorem tailTrace_8102737 : CollatzResearch.WordTrace tailWord_8102737 prefixEnd_8102737 4160598697969769737923697 := by
  unfold tailWord_8102737
  simp only [CollatzResearch.WordTrace]
  refine ⟨295531097246175161151794465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197020731497450107434529643 295531097246175161151794465)
  ·
    refine ⟨221648322934631370863845849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295531097246175161151794465 221648322934631370863845849)
    ·
      refine ⟨166236242200973528147884387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221648322934631370863845849 166236242200973528147884387)
      ·
        refine ⟨249354363301460292221826581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166236242200973528147884387 249354363301460292221826581)
        ·
          refine ⟨11688485779755951197898121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 249354363301460292221826581 11688485779755951197898121)
          ·
            refine ⟨8766364334816963398423591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11688485779755951197898121 8766364334816963398423591)
            ·
              refine ⟨13149546502225445097635387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8766364334816963398423591 13149546502225445097635387)
              ·
                refine ⟨19724319753338167646453081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13149546502225445097635387 19724319753338167646453081)
                ·
                  refine ⟨14793239815003625734839811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19724319753338167646453081 14793239815003625734839811)
                  ·
                    refine ⟨22189859722505438602259717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14793239815003625734839811 22189859722505438602259717)
                    ·
                      refine ⟨4160598697969769737923697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22189859722505438602259717 4160598697969769737923697)
                      ·
                        rfl

theorem cell23_8102737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 1, 4].length) (baseStart_8102737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102737 prefixEnd_8102737 := by exact prefixLift 8102737
  have htrace : WordTrace (prefixWord ++ tailWord_8102737) baseStart_8102737 baseEnd_8102737 := by
    simpa [prefixWord, tailWord_8102737, baseEnd_8102737] using wordTrace_append hprefix tailTrace_8102737
  have hstable : (prefixWord ++ tailWord_8102737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102737).length < 2 ^ (prefixWord ++ tailWord_8102737).sum := by decide
  have hdescent : baseEnd_8102737 < baseStart_8102737 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102760 : List Nat := [2, 1, 4, 2, 1, 2, 3, 2, 6]
def baseStart_8102760 : Nat := 118140960795 + 8102760 * 2 ^ 59
def prefixEnd_8102760 : Nat := 4983230072969 + 3 ^ 40 * 8102760 * 2
def baseEnd_8102760 : Nat := 462290056447202571992899

theorem tailTrace_8102760 : CollatzResearch.WordTrace tailWord_8102760 prefixEnd_8102760 462290056447202571992899 := by
  unfold tailWord_8102760
  simp only [CollatzResearch.WordTrace]
  refine ⟨147765968062545918039940867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197021290750061224053254489 147765968062545918039940867)
  ·
    refine ⟨221648952093818877059911301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147765968062545918039940867 221648952093818877059911301)
    ·
      refine ⟨41559178517591039448733369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221648952093818877059911301 41559178517591039448733369)
      ·
        refine ⟨31169383888193279586550027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41559178517591039448733369 31169383888193279586550027)
        ·
          refine ⟨46754075832289919379825041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31169383888193279586550027 46754075832289919379825041)
          ·
            refine ⟨35065556874217439534868781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46754075832289919379825041 35065556874217439534868781)
            ·
              refine ⟨13149583827831539825575793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35065556874217439534868781 13149583827831539825575793)
              ·
                refine ⟨9862187870873654869181845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13149583827831539825575793 9862187870873654869181845)
                ·
                  refine ⟨462290056447202571992899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9862187870873654869181845 462290056447202571992899)
                  ·
                    rfl

theorem cell23_8102760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 6].length) (baseStart_8102760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102760 prefixEnd_8102760 := by exact prefixLift 8102760
  have htrace : WordTrace (prefixWord ++ tailWord_8102760) baseStart_8102760 baseEnd_8102760 := by
    simpa [prefixWord, tailWord_8102760, baseEnd_8102760] using wordTrace_append hprefix tailTrace_8102760
  have hstable : (prefixWord ++ tailWord_8102760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102760).length < 2 ^ (prefixWord ++ tailWord_8102760).sum := by decide
  have hdescent : baseEnd_8102760 < baseStart_8102760 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102820 : List Nat := [2, 3, 1, 2, 1, 2, 1, 3, 4, 4]
def baseStart_8102820 : Nat := 118140960795 + 8102820 * 2 ^ 59
def prefixEnd_8102820 : Nat := 4983230072969 + 3 ^ 40 * 8102820 * 2
def baseEnd_8102820 : Nat := 1386880438954697637728605

theorem tailTrace_8102820 : CollatzResearch.WordTrace tailWord_8102820 prefixEnd_8102820 1386880438954697637728605 := by
  unfold tailWord_8102820
  simp only [CollatzResearch.WordTrace]
  refine ⟨147767062252437233163532957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197022749669916310884710609 147767062252437233163532957)
  ·
    refine ⟨55412648344663962436324859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147767062252437233163532957 55412648344663962436324859)
    ·
      refine ⟨83118972516995943654487289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55412648344663962436324859 83118972516995943654487289)
      ·
        refine ⟨62339229387746957740865467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83118972516995943654487289 62339229387746957740865467)
        ·
          refine ⟨93508844081620436611298201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62339229387746957740865467 93508844081620436611298201)
          ·
            refine ⟨70131633061215327458473651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93508844081620436611298201 70131633061215327458473651)
            ·
              refine ⟨105197449591822991187710477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70131633061215327458473651 105197449591822991187710477)
              ·
                refine ⟨39449043596933621695391429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105197449591822991187710477 39449043596933621695391429)
                ·
                  refine ⟨7396695674425054067885893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39449043596933621695391429 7396695674425054067885893)
                  ·
                    refine ⟨1386880438954697637728605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7396695674425054067885893 1386880438954697637728605)
                    ·
                      rfl

theorem cell23_8102820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_8102820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102820 prefixEnd_8102820 := by exact prefixLift 8102820
  have htrace : WordTrace (prefixWord ++ tailWord_8102820) baseStart_8102820 baseEnd_8102820 := by
    simpa [prefixWord, tailWord_8102820, baseEnd_8102820] using wordTrace_append hprefix tailTrace_8102820
  have hstable : (prefixWord ++ tailWord_8102820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102820).length < 2 ^ (prefixWord ++ tailWord_8102820).sum := by decide
  have hdescent : baseEnd_8102820 < baseStart_8102820 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102837 : List Nat := [1, 3, 3, 2, 1, 1, 3, 3, 2, 4]
def baseStart_8102837 : Nat := 118140960795 + 8102837 * 2 ^ 59
def prefixEnd_8102837 : Nat := 4983230072969 + 3 ^ 40 * 8102837 * 2
def baseEnd_8102837 : Nat := 1386883348678406448891079

theorem tailTrace_8102837 : CollatzResearch.WordTrace tailWord_8102837 prefixEnd_8102837 1386883348678406448891079 := by
  unfold tailWord_8102837
  simp only [CollatzResearch.WordTrace]
  refine ⟨295534744545812878230434765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197023163030541918820289843 295534744545812878230434765)
  ·
    refine ⟨110825529204679829336413037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295534744545812878230434765 110825529204679829336413037)
    ·
      refine ⟨41559573451754936001154889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110825529204679829336413037 41559573451754936001154889)
      ·
        refine ⟨31169680088816202000866167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41559573451754936001154889 31169680088816202000866167)
        ·
          refine ⟨46754520133224303001299251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31169680088816202000866167 46754520133224303001299251)
          ·
            refine ⟨70131780199836454501948877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46754520133224303001299251 70131780199836454501948877)
            ·
              refine ⟨26299417574938670438230829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70131780199836454501948877 26299417574938670438230829)
              ·
                refine ⟨9862281590602001414336561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26299417574938670438230829 9862281590602001414336561)
                ·
                  refine ⟨7396711192951501060752421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9862281590602001414336561 7396711192951501060752421)
                  ·
                    refine ⟨1386883348678406448891079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7396711192951501060752421 1386883348678406448891079)
                    ·
                      rfl

theorem cell23_8102837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_8102837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102837 prefixEnd_8102837 := by exact prefixLift 8102837
  have htrace : WordTrace (prefixWord ++ tailWord_8102837) baseStart_8102837 baseEnd_8102837 := by
    simpa [prefixWord, tailWord_8102837, baseEnd_8102837] using wordTrace_append hprefix tailTrace_8102837
  have hstable : (prefixWord ++ tailWord_8102837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102837).length < 2 ^ (prefixWord ++ tailWord_8102837).sum := by decide
  have hdescent : baseEnd_8102837 < baseStart_8102837 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102894 : List Nat := [4, 1, 2, 1, 4, 1, 2, 1, 1, 3, 3]
def baseStart_8102894 : Nat := 118140960795 + 8102894 * 2 ^ 59
def prefixEnd_8102894 : Nat := 4983230072969 + 3 ^ 40 * 8102894 * 2
def baseEnd_8102894 : Nat := 4160679314432525623660475

theorem tailTrace_8102894 : CollatzResearch.WordTrace tailWord_8102894 prefixEnd_8102894 4160679314432525623660475 := by
  unfold tailWord_8102894
  simp only [CollatzResearch.WordTrace]
  refine ⟨36942102938325797120657467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197024549004404251310173157 36942102938325797120657467)
  ·
    refine ⟨55413154407488695680986201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36942102938325797120657467 55413154407488695680986201)
    ·
      refine ⟨41559865805616521760739651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55413154407488695680986201 41559865805616521760739651)
      ·
        refine ⟨62339798708424782641109477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41559865805616521760739651 62339798708424782641109477)
        ·
          refine ⟨11688712257829646745208027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62339798708424782641109477 11688712257829646745208027)
          ·
            refine ⟨17533068386744470117812041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11688712257829646745208027 17533068386744470117812041)
            ·
              refine ⟨13149801290058352588359031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17533068386744470117812041 13149801290058352588359031)
              ·
                refine ⟨19724701935087528882538547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13149801290058352588359031 19724701935087528882538547)
                ·
                  refine ⟨29587052902631293323807821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19724701935087528882538547 29587052902631293323807821)
                  ·
                    refine ⟨11095144838486734996427933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29587052902631293323807821 11095144838486734996427933)
                    ·
                      refine ⟨4160679314432525623660475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11095144838486734996427933 4160679314432525623660475)
                      ·
                        rfl

theorem cell23_8102894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_8102894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102894 prefixEnd_8102894 := by exact prefixLift 8102894
  have htrace : WordTrace (prefixWord ++ tailWord_8102894) baseStart_8102894 baseEnd_8102894 := by
    simpa [prefixWord, tailWord_8102894, baseEnd_8102894] using wordTrace_append hprefix tailTrace_8102894
  have hstable : (prefixWord ++ tailWord_8102894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102894).length < 2 ^ (prefixWord ++ tailWord_8102894).sum := by decide
  have hdescent : baseEnd_8102894 < baseStart_8102894 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102917 : List Nat := [1, 3, 1, 1, 2, 3, 1, 4, 1, 4, 2]
def baseStart_8102917 : Nat := 118140960795 + 8102917 * 2 ^ 59
def prefixEnd_8102917 : Nat := 4983230072969 + 3 ^ 40 * 8102917 * 2
def baseEnd_8102917 : Nat := 4160691124487579033672869

theorem tailTrace_8102917 : CollatzResearch.WordTrace tailWord_8102917 prefixEnd_8102917 4160691124487579033672869 := by
  unfold tailWord_8102917
  simp only [CollatzResearch.WordTrace]
  refine ⟨295537662385523051893347005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197025108257015367928898003 295537662385523051893347005)
  ·
    refine ⟨110826623394571144460005127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295537662385523051893347005 110826623394571144460005127)
    ·
      refine ⟨166239935091856716690007691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110826623394571144460005127 166239935091856716690007691)
      ·
        refine ⟨249359902637785075035011537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166239935091856716690007691 249359902637785075035011537)
        ·
          refine ⟨187019926978338806276258653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249359902637785075035011537 187019926978338806276258653)
          ·
            refine ⟨70132472616877052353596995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187019926978338806276258653 70132472616877052353596995)
            ·
              refine ⟨105198708925315578530395493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70132472616877052353596995 105198708925315578530395493)
              ·
                refine ⟨19724757923496670974449155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105198708925315578530395493 19724757923496670974449155)
                ·
                  refine ⟨29587136885245006461673733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19724757923496670974449155 29587136885245006461673733)
                  ·
                    refine ⟨5547588165983438711563825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29587136885245006461673733 5547588165983438711563825)
                    ·
                      refine ⟨4160691124487579033672869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5547588165983438711563825 4160691124487579033672869)
                      ·
                        rfl

theorem cell23_8102917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 4, 2].length) (baseStart_8102917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102917 prefixEnd_8102917 := by exact prefixLift 8102917
  have htrace : WordTrace (prefixWord ++ tailWord_8102917) baseStart_8102917 baseEnd_8102917 := by
    simpa [prefixWord, tailWord_8102917, baseEnd_8102917] using wordTrace_append hprefix tailTrace_8102917
  have hstable : (prefixWord ++ tailWord_8102917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102917).length < 2 ^ (prefixWord ++ tailWord_8102917).sum := by decide
  have hdescent : baseEnd_8102917 < baseStart_8102917 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102951 : List Nat := [1, 1, 7, 1, 1, 1, 3, 1, 1, 4, 2]
def baseStart_8102951 : Nat := 118140960795 + 8102951 * 2 ^ 59
def prefixEnd_8102951 : Nat := 4983230072969 + 3 ^ 40 * 8102951 * 2
def baseEnd_8102951 : Nat := 4160708582829831900647713

theorem tailTrace_8102951 : CollatzResearch.WordTrace tailWord_8102951 prefixEnd_8102951 4160708582829831900647713 := by
  unfold tailWord_8102951
  simp only [CollatzResearch.WordTrace]
  refine ⟨295538902467399875700084707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197025934978266583800056471 295538902467399875700084707)
  ·
    refine ⟨443308353701099813550127061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295538902467399875700084707 443308353701099813550127061)
    ·
      refine ⟨10390039539869526880081103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 443308353701099813550127061 10390039539869526880081103)
      ·
        refine ⟨15585059309804290320121655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10390039539869526880081103 15585059309804290320121655)
        ·
          refine ⟨23377588964706435480182483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15585059309804290320121655 23377588964706435480182483)
          ·
            refine ⟨35066383447059653220273725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23377588964706435480182483 35066383447059653220273725)
            ·
              refine ⟨13149893792647369957602647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35066383447059653220273725 13149893792647369957602647)
              ·
                refine ⟨19724840688971054936403971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13149893792647369957602647 19724840688971054936403971)
                ·
                  refine ⟨29587261033456582404605957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19724840688971054936403971 29587261033456582404605957)
                  ·
                    refine ⟨5547611443773109200863617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29587261033456582404605957 5547611443773109200863617)
                    ·
                      refine ⟨4160708582829831900647713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5547611443773109200863617 4160708582829831900647713)
                      ·
                        rfl

theorem cell23_8102951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_8102951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102951 prefixEnd_8102951 := by exact prefixLift 8102951
  have htrace : WordTrace (prefixWord ++ tailWord_8102951) baseStart_8102951 baseEnd_8102951 := by
    simpa [prefixWord, tailWord_8102951, baseEnd_8102951] using wordTrace_append hprefix tailTrace_8102951
  have hstable : (prefixWord ++ tailWord_8102951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102951).length < 2 ^ (prefixWord ++ tailWord_8102951).sum := by decide
  have hdescent : baseEnd_8102951 < baseStart_8102951 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8102970 : List Nat := [3, 1, 1, 1, 3, 1, 4, 1, 1, 7]
def baseStart_8102970 : Nat := 118140960795 + 8102970 * 2 ^ 59
def prefixEnd_8102970 : Nat := 4983230072969 + 3 ^ 40 * 8102970 * 2
def baseEnd_8102970 : Nat := 1386906112987422442103375

theorem tailTrace_8102970 : CollatzResearch.WordTrace tailWord_8102970 prefixEnd_8102970 1386906112987422442103375 := by
  unfold tailWord_8102970
  simp only [CollatzResearch.WordTrace]
  refine ⟨73884898863582760486256591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197026396969554027963350909 73884898863582760486256591)
  ·
    refine ⟨110827348295374140729384887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73884898863582760486256591 110827348295374140729384887)
    ·
      refine ⟨166241022443061211094077331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110827348295374140729384887 166241022443061211094077331)
      ·
        refine ⟨249361533664591816641115997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166241022443061211094077331 249361533664591816641115997)
        ·
          refine ⟨93510575124221931240418499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249361533664591816641115997 93510575124221931240418499)
          ·
            refine ⟨140265862686332896860627749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93510575124221931240418499 140265862686332896860627749)
            ·
              refine ⟨26299849253687418161367703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140265862686332896860627749 26299849253687418161367703)
              ·
                refine ⟨39449773880531127242051555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26299849253687418161367703 39449773880531127242051555)
                ·
                  refine ⟨59174660820796690863077333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39449773880531127242051555 59174660820796690863077333)
                  ·
                    refine ⟨1386906112987422442103375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59174660820796690863077333 1386906112987422442103375)
                    ·
                      rfl

theorem cell23_8102970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 1, 7].length) (baseStart_8102970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8102970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8102970 prefixEnd_8102970 := by exact prefixLift 8102970
  have htrace : WordTrace (prefixWord ++ tailWord_8102970) baseStart_8102970 baseEnd_8102970 := by
    simpa [prefixWord, tailWord_8102970, baseEnd_8102970] using wordTrace_append hprefix tailTrace_8102970
  have hstable : (prefixWord ++ tailWord_8102970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8102970).length < 2 ^ (prefixWord ++ tailWord_8102970).sum := by decide
  have hdescent : baseEnd_8102970 < baseStart_8102970 := by decide
  rcases family_descends (prefixWord ++ tailWord_8102970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103007 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 1, 6, 2]
def baseStart_8103007 : Nat := 118140960795 + 8103007 * 2 ^ 59
def prefixEnd_8103007 : Nat := 4983230072969 + 3 ^ 40 * 8103007 * 2
def baseEnd_8103007 : Nat := 4160737337746483681547455

theorem tailTrace_8103007 : CollatzResearch.WordTrace tailWord_8103007 prefixEnd_8103007 4160737337746483681547455 := by
  unfold tailWord_8103007
  simp only [CollatzResearch.WordTrace]
  refine ⟨295540944955196997264123275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197027296636797998176082183 295540944955196997264123275)
  ·
    refine ⟨443311417432795495896184913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295540944955196997264123275 443311417432795495896184913)
    ·
      refine ⟨332483563074596621922138685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443311417432795495896184913 332483563074596621922138685)
      ·
        refine ⟨124681336152973733220802007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332483563074596621922138685 124681336152973733220802007)
        ·
          refine ⟨187022004229460599831203011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124681336152973733220802007 187022004229460599831203011)
          ·
            refine ⟨280533006344190899746804517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187022004229460599831203011 280533006344190899746804517)
            ·
              refine ⟨52599938689535793702525847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 280533006344190899746804517 52599938689535793702525847)
              ·
                refine ⟨78899908034303690553788771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52599938689535793702525847 78899908034303690553788771)
                ·
                  refine ⟨118349862051455535830683157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78899908034303690553788771 118349862051455535830683157)
                  ·
                    refine ⟨5547649783661978242063273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118349862051455535830683157 5547649783661978242063273)
                    ·
                      refine ⟨4160737337746483681547455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5547649783661978242063273 4160737337746483681547455)
                      ·
                        rfl

theorem cell23_8103007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 6, 2].length) (baseStart_8103007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103007 prefixEnd_8103007 := by exact prefixLift 8103007
  have htrace : WordTrace (prefixWord ++ tailWord_8103007) baseStart_8103007 baseEnd_8103007 := by
    simpa [prefixWord, tailWord_8103007, baseEnd_8103007] using wordTrace_append hprefix tailTrace_8103007
  have hstable : (prefixWord ++ tailWord_8103007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103007).length < 2 ^ (prefixWord ++ tailWord_8103007).sum := by decide
  have hdescent : baseEnd_8103007 < baseStart_8103007 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103044 : List Nat := [2, 3, 2, 1, 2, 2, 2, 2, 2, 2, 3]
def baseStart_8103044 : Nat := 118140960795 + 8103044 * 2 ^ 59
def prefixEnd_8103044 : Nat := 4983230072969 + 3 ^ 40 * 8103044 * 2
def baseEnd_8103044 : Nat := 4160756336530700036784785

theorem tailTrace_8103044 : CollatzResearch.WordTrace tailWord_8103044 prefixEnd_8103044 4160756336530700036784785 := by
  unfold tailWord_8103044
  simp only [CollatzResearch.WordTrace]
  refine ⟨147771147228031476291610093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197028196304041968388813457 147771147228031476291610093)
  ·
    refine ⟨55414180210511803609353785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147771147228031476291610093 55414180210511803609353785)
    ·
      refine ⟨41560635157883852707015339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55414180210511803609353785 41560635157883852707015339)
      ·
        refine ⟨62340952736825779060523009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41560635157883852707015339 62340952736825779060523009)
        ·
          refine ⟨46755714552619334295392257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62340952736825779060523009 46755714552619334295392257)
          ·
            refine ⟨35066785914464500721544193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46755714552619334295392257 35066785914464500721544193)
            ·
              refine ⟨26300089435848375541158145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35066785914464500721544193 26300089435848375541158145)
              ·
                refine ⟨19725067076886281655868609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26300089435848375541158145 19725067076886281655868609)
                ·
                  refine ⟨14793800307664711241901457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19725067076886281655868609 14793800307664711241901457)
                  ·
                    refine ⟨11095350230748533431426093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14793800307664711241901457 11095350230748533431426093)
                    ·
                      refine ⟨4160756336530700036784785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11095350230748533431426093 4160756336530700036784785)
                      ·
                        rfl

theorem cell23_8103044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_8103044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103044 prefixEnd_8103044 := by exact prefixLift 8103044
  have htrace : WordTrace (prefixWord ++ tailWord_8103044) baseStart_8103044 baseEnd_8103044 := by
    simpa [prefixWord, tailWord_8103044, baseEnd_8103044] using wordTrace_append hprefix tailTrace_8103044
  have hstable : (prefixWord ++ tailWord_8103044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103044).length < 2 ^ (prefixWord ++ tailWord_8103044).sum := by decide
  have hdescent : baseEnd_8103044 < baseStart_8103044 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103077 : List Nat := [1, 3, 1, 2, 1, 4, 2, 1, 3, 5]
def baseStart_8103077 : Nat := 118140960795 + 8103077 * 2 ^ 59
def prefixEnd_8103077 : Nat := 4983230072969 + 3 ^ 40 * 8103077 * 2
def baseEnd_8103077 : Nat := 1386924427130766135890711

theorem tailTrace_8103077 : CollatzResearch.WordTrace tailWord_8103077 prefixEnd_8103077 1386924427130766135890711 := by
  unfold tailWord_8103077
  simp only [CollatzResearch.WordTrace]
  refine ⟨295543498064943399219171485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197028998709962266146114323 295543498064943399219171485)
  ·
    refine ⟨110828811774353774707189307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295543498064943399219171485 110828811774353774707189307)
    ·
      refine ⟨166243217661530662060783961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110828811774353774707189307 166243217661530662060783961)
      ·
        refine ⟨124682413246147996545587971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166243217661530662060783961 124682413246147996545587971)
        ·
          refine ⟨187023619869221994818381957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124682413246147996545587971 187023619869221994818381957)
          ·
            refine ⟨35066928725479124028446617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187023619869221994818381957 35066928725479124028446617)
            ·
              refine ⟨26300196544109343021334963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35066928725479124028446617 26300196544109343021334963)
              ·
                refine ⟨39450294816164014532002445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26300196544109343021334963 39450294816164014532002445)
                ·
                  refine ⟨14793860556061505449500917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39450294816164014532002445 14793860556061505449500917)
                  ·
                    refine ⟨1386924427130766135890711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14793860556061505449500917 1386924427130766135890711)
                    ·
                      rfl

theorem cell23_8103077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 5].length) (baseStart_8103077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103077 prefixEnd_8103077 := by exact prefixLift 8103077
  have htrace : WordTrace (prefixWord ++ tailWord_8103077) baseStart_8103077 baseEnd_8103077 := by
    simpa [prefixWord, tailWord_8103077, baseEnd_8103077] using wordTrace_append hprefix tailTrace_8103077
  have hstable : (prefixWord ++ tailWord_8103077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103077).length < 2 ^ (prefixWord ++ tailWord_8103077).sum := by decide
  have hdescent : baseEnd_8103077 < baseStart_8103077 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103084 : List Nat := [2, 2, 1, 1, 1, 1, 1, 7, 2, 3, 2]
def baseStart_8103084 : Nat := 118140960795 + 8103084 * 2 ^ 59
def prefixEnd_8103084 : Nat := 4983230072969 + 3 ^ 40 * 8103084 * 2
def baseEnd_8103084 : Nat := 4160776875756879880284601

theorem tailTrace_8103084 : CollatzResearch.WordTrace tailWord_8103084 prefixEnd_8103084 4160776875756879880284601 := by
  unfold tailWord_8103084
  simp only [CollatzResearch.WordTrace]
  refine ⟨147771876687959019707338153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197029168917278692943117537 147771876687959019707338153)
  ·
    refine ⟨110828907515969264780503615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147771876687959019707338153 110828907515969264780503615)
    ·
      refine ⟨166243361273953897170755423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110828907515969264780503615 166243361273953897170755423)
      ·
        refine ⟨249365041910930845756133135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166243361273953897170755423 249365041910930845756133135)
        ·
          refine ⟨374047562866396268634199703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249365041910930845756133135 374047562866396268634199703)
          ·
            refine ⟨561071344299594402951299555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374047562866396268634199703 561071344299594402951299555)
            ·
              refine ⟨841607016449391604426949333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561071344299594402951299555 841607016449391604426949333)
              ·
                refine ⟨19725164448032615728756625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 841607016449391604426949333 19725164448032615728756625)
                ·
                  refine ⟨14793873336024461796567469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19725164448032615728756625 14793873336024461796567469)
                  ·
                    refine ⟨5547702501009173173712801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14793873336024461796567469 5547702501009173173712801)
                    ·
                      refine ⟨4160776875756879880284601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5547702501009173173712801 4160776875756879880284601)
                      ·
                        rfl

theorem cell23_8103084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 3, 2].length) (baseStart_8103084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103084 prefixEnd_8103084 := by exact prefixLift 8103084
  have htrace : WordTrace (prefixWord ++ tailWord_8103084) baseStart_8103084 baseEnd_8103084 := by
    simpa [prefixWord, tailWord_8103084, baseEnd_8103084] using wordTrace_append hprefix tailTrace_8103084
  have hstable : (prefixWord ++ tailWord_8103084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103084).length < 2 ^ (prefixWord ++ tailWord_8103084).sum := by decide
  have hdescent : baseEnd_8103084 < baseStart_8103084 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103091 : List Nat := [1, 1, 1, 2, 3, 2, 3, 5, 1, 1, 3]
def baseStart_8103091 : Nat := 118140960795 + 8103091 * 2 ^ 59
def prefixEnd_8103091 : Nat := 4983230072969 + 3 ^ 40 * 8103091 * 2
def baseEnd_8103091 : Nat := 4160780470121461352897069

theorem tailTrace_8103091 : CollatzResearch.WordTrace tailWord_8103091 prefixEnd_8103091 4160780470121461352897069 := by
  unfold tailWord_8103091
  simp only [CollatzResearch.WordTrace]
  refine ⟨295544008686892679610181127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197029339124595119740120751 295544008686892679610181127)
  ·
    refine ⟨443316013030339019415271691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295544008686892679610181127 443316013030339019415271691)
    ·
      refine ⟨664974019545508529122907537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443316013030339019415271691 664974019545508529122907537)
      ·
        refine ⟨498730514659131396842180653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 664974019545508529122907537 498730514659131396842180653)
        ·
          refine ⟨187023942997174273815817745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 498730514659131396842180653 187023942997174273815817745)
          ·
            refine ⟨140267957247880705361863309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187023942997174273815817745 140267957247880705361863309)
            ·
              refine ⟨52600483967955264510698741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140267957247880705361863309 52600483967955264510698741)
              ·
                refine ⟨4931295371995806047878007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52600483967955264510698741 4931295371995806047878007)
                ·
                  refine ⟨7396943057993709071817011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4931295371995806047878007 7396943057993709071817011)
                  ·
                    refine ⟨11095414586990563607725517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7396943057993709071817011 11095414586990563607725517)
                    ·
                      refine ⟨4160780470121461352897069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11095414586990563607725517 4160780470121461352897069)
                      ·
                        rfl

theorem cell23_8103091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 5, 1, 1, 3].length) (baseStart_8103091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103091 prefixEnd_8103091 := by exact prefixLift 8103091
  have htrace : WordTrace (prefixWord ++ tailWord_8103091) baseStart_8103091 baseEnd_8103091 := by
    simpa [prefixWord, tailWord_8103091, baseEnd_8103091] using wordTrace_append hprefix tailTrace_8103091
  have hstable : (prefixWord ++ tailWord_8103091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103091).length < 2 ^ (prefixWord ++ tailWord_8103091).sum := by decide
  have hdescent : baseEnd_8103091 < baseStart_8103091 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103108 : List Nat := [2, 3, 3, 1, 3, 1, 2, 1, 3, 1, 3]
def baseStart_8103108 : Nat := 118140960795 + 8103108 * 2 ^ 59
def prefixEnd_8103108 : Nat := 4983230072969 + 3 ^ 40 * 8103108 * 2
def baseEnd_8103108 : Nat := 4160789199292587786384491

theorem tailTrace_8103108 : CollatzResearch.WordTrace tailWord_8103108 prefixEnd_8103108 4160789199292587786384491 := by
  unfold tailWord_8103108
  simp only [CollatzResearch.WordTrace]
  refine ⟨147772314363915545756774989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197029752485220727675699985 147772314363915545756774989)
  ·
    refine ⟨55414617886468329658790621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147772314363915545756774989 55414617886468329658790621)
    ·
      refine ⟨20780481707425623622046483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55414617886468329658790621 20780481707425623622046483)
      ·
        refine ⟨31170722561138435433069725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20780481707425623622046483 31170722561138435433069725)
        ·
          refine ⟨11689020960426913287401147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31170722561138435433069725 11689020960426913287401147)
          ·
            refine ⟨17533531440640369931101721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11689020960426913287401147 17533531440640369931101721)
            ·
              refine ⟨13150148580480277448326291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17533531440640369931101721 13150148580480277448326291)
              ·
                refine ⟨19725222870720416172489437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13150148580480277448326291 19725222870720416172489437)
                ·
                  refine ⟨7396958576520156064683539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19725222870720416172489437 7396958576520156064683539)
                  ·
                    refine ⟨11095437864780234097025309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7396958576520156064683539 11095437864780234097025309)
                    ·
                      refine ⟨4160789199292587786384491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11095437864780234097025309 4160789199292587786384491)
                      ·
                        rfl

theorem cell23_8103108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_8103108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103108 prefixEnd_8103108 := by exact prefixLift 8103108
  have htrace : WordTrace (prefixWord ++ tailWord_8103108) baseStart_8103108 baseEnd_8103108 := by
    simpa [prefixWord, tailWord_8103108, baseEnd_8103108] using wordTrace_append hprefix tailTrace_8103108
  have hstable : (prefixWord ++ tailWord_8103108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103108).length < 2 ^ (prefixWord ++ tailWord_8103108).sum := by decide
  have hdescent : baseEnd_8103108 < baseStart_8103108 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103137 : List Nat := [1, 2, 3, 1, 3, 3, 1, 9]
def baseStart_8103137 : Nat := 118140960795 + 8103137 * 2 ^ 59
def prefixEnd_8103137 : Nat := 4983230072969 + 3 ^ 40 * 8103137 * 2
def baseEnd_8103137 : Nat := 154103855193761784182291

theorem tailTrace_8103137 : CollatzResearch.WordTrace tailWord_8103137 prefixEnd_8103137 154103855193761784182291 := by
  unfold tailWord_8103137
  simp only [CollatzResearch.WordTrace]
  refine ⟨295545686444726029466355665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197030457629817352977570443 295545686444726029466355665)
  ·
    refine ⟨221659264833544522099766749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295545686444726029466355665 221659264833544522099766749)
    ·
      refine ⟨83122224312579195787412531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221659264833544522099766749 83122224312579195787412531)
      ·
        refine ⟨124683336468868793681118797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83122224312579195787412531 124683336468868793681118797)
        ·
          refine ⟨46756251175825797630419549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124683336468868793681118797 46756251175825797630419549)
          ·
            refine ⟨17533594190934674111407331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46756251175825797630419549 17533594190934674111407331)
            ·
              refine ⟨26300391286402011167110997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17533594190934674111407331 26300391286402011167110997)
              ·
                refine ⟨154103855193761784182291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26300391286402011167110997 154103855193761784182291)
                ·
                  rfl

theorem cell23_8103137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 9].length) (baseStart_8103137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103137 prefixEnd_8103137 := by exact prefixLift 8103137
  have htrace : WordTrace (prefixWord ++ tailWord_8103137) baseStart_8103137 baseEnd_8103137 := by
    simpa [prefixWord, tailWord_8103137, baseEnd_8103137] using wordTrace_append hprefix tailTrace_8103137
  have hstable : (prefixWord ++ tailWord_8103137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103137).length < 2 ^ (prefixWord ++ tailWord_8103137).sum := by decide
  have hdescent : baseEnd_8103137 < baseStart_8103137 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103154 : List Nat := [3, 2, 1, 3, 3, 2, 9]
def baseStart_8103154 : Nat := 118140960795 + 8103154 * 2 ^ 59
def prefixEnd_8103154 : Nat := 4983230072969 + 3 ^ 40 * 8103154 * 2
def baseEnd_8103154 : Nat := 51368059498798698844559

theorem tailTrace_8103154 : CollatzResearch.WordTrace tailWord_8103154 prefixEnd_8103154 51368059498798698844559 := by
  unfold tailWord_8103154
  simp only [CollatzResearch.WordTrace]
  refine ⟨73886576621416110342431129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197030870990442960913149677 73886576621416110342431129)
  ·
    refine ⟨55414932466062082756823347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73886576621416110342431129 55414932466062082756823347)
    ·
      refine ⟨83122398699093124135235021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55414932466062082756823347 83122398699093124135235021)
      ·
        refine ⟨31170899512159921550713133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83122398699093124135235021 31170899512159921550713133)
        ·
          refine ⟨11689087317059970581517425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31170899512159921550713133 11689087317059970581517425)
          ·
            refine ⟨8766815487794977936138069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11689087317059970581517425 8766815487794977936138069)
            ·
              refine ⟨51368059498798698844559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8766815487794977936138069 51368059498798698844559)
              ·
                rfl

theorem cell23_8103154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 9].length) (baseStart_8103154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103154 prefixEnd_8103154 := by exact prefixLift 8103154
  have htrace : WordTrace (prefixWord ++ tailWord_8103154) baseStart_8103154 baseEnd_8103154 := by
    simpa [prefixWord, tailWord_8103154, baseEnd_8103154] using wordTrace_append hprefix tailTrace_8103154
  have hstable : (prefixWord ++ tailWord_8103154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103154).length < 2 ^ (prefixWord ++ tailWord_8103154).sum := by decide
  have hdescent : baseEnd_8103154 < baseStart_8103154 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103191 : List Nat := [1, 1, 3, 4, 1, 1, 3, 1, 3, 3, 2]
def baseStart_8103191 : Nat := 118140960795 + 8103191 * 2 ^ 59
def prefixEnd_8103191 : Nat := 4983230072969 + 3 ^ 40 * 8103191 * 2
def baseEnd_8103191 : Nat := 4160831818186910961646609

theorem tailTrace_8103191 : CollatzResearch.WordTrace tailWord_8103191 prefixEnd_8103191 4160831818186910961646609 := by
  unfold tailWord_8103191
  simp only [CollatzResearch.WordTrace]
  refine ⟨295547655986530396688821427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197031770657686931125880951 295547655986530396688821427)
  ·
    refine ⟨443321483979795595033232141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295547655986530396688821427 443321483979795595033232141)
    ·
      refine ⟨166245556492423348137462053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 443321483979795595033232141 166245556492423348137462053)
      ·
        refine ⟨31171041842329377775774135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166245556492423348137462053 31171041842329377775774135)
        ·
          refine ⟨46756562763494066663661203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31171041842329377775774135 46756562763494066663661203)
          ·
            refine ⟨70134844145241099995491805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46756562763494066663661203 70134844145241099995491805)
            ·
              refine ⟨26300566554465412498309427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70134844145241099995491805 26300566554465412498309427)
              ·
                refine ⟨39450849831698118747464141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26300566554465412498309427 39450849831698118747464141)
                ·
                  refine ⟨14794068686886794530299053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39450849831698118747464141 14794068686886794530299053)
                  ·
                    refine ⟨5547775757582547948862145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14794068686886794530299053 5547775757582547948862145)
                    ·
                      refine ⟨4160831818186910961646609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5547775757582547948862145 4160831818186910961646609)
                      ·
                        rfl

theorem cell23_8103191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_8103191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103191 prefixEnd_8103191 := by exact prefixLift 8103191
  have htrace : WordTrace (prefixWord ++ tailWord_8103191) baseStart_8103191 baseEnd_8103191 := by
    simpa [prefixWord, tailWord_8103191, baseEnd_8103191] using wordTrace_append hprefix tailTrace_8103191
  have hstable : (prefixWord ++ tailWord_8103191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103191).length < 2 ^ (prefixWord ++ tailWord_8103191).sum := by decide
  have hdescent : baseEnd_8103191 < baseStart_8103191 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103244 : List Nat := [2, 2, 1, 3, 2, 3, 1, 2, 7]
def baseStart_8103244 : Nat := 118140960795 + 8103244 * 2 ^ 59
def prefixEnd_8103244 : Nat := 4983230072969 + 3 ^ 40 * 8103244 * 2
def baseEnd_8103244 : Nat := 462317670295733250475985

theorem tailTrace_8103244 : CollatzResearch.WordTrace tailWord_8103244 prefixEnd_8103244 462317670295733250475985 := by
  unfold tailWord_8103244
  simp only [CollatzResearch.WordTrace]
  refine ⟨147774794527669193370250393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197033059370225591160333857 147774794527669193370250393)
  ·
    refine ⟨110831095895751895027687795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147774794527669193370250393 110831095895751895027687795)
    ·
      refine ⟨166246643843627842541531693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110831095895751895027687795 166246643843627842541531693)
      ·
        refine ⟨62342491441360440953074385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166246643843627842541531693 62342491441360440953074385)
        ·
          refine ⟨46756868581020330714805789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62342491441360440953074385 46756868581020330714805789)
          ·
            refine ⟨17533825717882624018052171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46756868581020330714805789 17533825717882624018052171)
            ·
              refine ⟨26300738576823936027078257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17533825717882624018052171 26300738576823936027078257)
              ·
                refine ⟨19725553932617952020308693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26300738576823936027078257 19725553932617952020308693)
                ·
                  refine ⟨462317670295733250475985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19725553932617952020308693 462317670295733250475985)
                  ·
                    rfl

theorem cell23_8103244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 7].length) (baseStart_8103244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103244 prefixEnd_8103244 := by exact prefixLift 8103244
  have htrace : WordTrace (prefixWord ++ tailWord_8103244) baseStart_8103244 baseEnd_8103244 := by
    simpa [prefixWord, tailWord_8103244, baseEnd_8103244] using wordTrace_append hprefix tailTrace_8103244
  have hstable : (prefixWord ++ tailWord_8103244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103244).length < 2 ^ (prefixWord ++ tailWord_8103244).sum := by decide
  have hdescent : baseEnd_8103244 < baseStart_8103244 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103272 : List Nat := [2, 1, 4, 2, 3, 2, 1, 2, 2, 2, 2]
def baseStart_8103272 : Nat := 118140960795 + 8103272 * 2 ^ 59
def prefixEnd_8103272 : Nat := 4983230072969 + 3 ^ 40 * 8103272 * 2
def baseEnd_8103272 : Nat := 4160873410119925144733737

theorem tailTrace_8103272 : CollatzResearch.WordTrace tailWord_8103272 prefixEnd_8103272 4160873410119925144733737 := by
  unfold tailWord_8103272
  simp only [CollatzResearch.WordTrace]
  refine ⟨147775305149618473761260035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197033740199491298348346713 147775305149618473761260035)
  ·
    refine ⟨221662957724427710641890053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147775305149618473761260035 221662957724427710641890053)
    ·
      refine ⟨41561804573330195745354385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221662957724427710641890053 41561804573330195745354385)
      ·
        refine ⟨31171353429997646809015789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41561804573330195745354385 31171353429997646809015789)
        ·
          refine ⟨11689257536249117553380921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31171353429997646809015789 11689257536249117553380921)
          ·
            refine ⟨8766943152186838165035691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11689257536249117553380921 8766943152186838165035691)
            ·
              refine ⟨13150414728280257247553537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8766943152186838165035691 13150414728280257247553537)
              ·
                refine ⟨9862811046210192935665153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13150414728280257247553537 9862811046210192935665153)
                ·
                  refine ⟨7397108284657644701748865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9862811046210192935665153 7397108284657644701748865)
                  ·
                    refine ⟨5547831213493233526311649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7397108284657644701748865 5547831213493233526311649)
                    ·
                      refine ⟨4160873410119925144733737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5547831213493233526311649 4160873410119925144733737)
                      ·
                        rfl

theorem cell23_8103272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_8103272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103272 prefixEnd_8103272 := by exact prefixLift 8103272
  have htrace : WordTrace (prefixWord ++ tailWord_8103272) baseStart_8103272 baseEnd_8103272 := by
    simpa [prefixWord, tailWord_8103272, baseEnd_8103272] using wordTrace_append hprefix tailTrace_8103272
  have hstable : (prefixWord ++ tailWord_8103272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103272).length < 2 ^ (prefixWord ++ tailWord_8103272).sum := by decide
  have hdescent : baseEnd_8103272 < baseStart_8103272 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103278 : List Nat := [4, 1, 2, 4, 1, 1, 2, 1, 7]
def baseStart_8103278 : Nat := 118140960795 + 8103278 * 2 ^ 59
def prefixEnd_8103278 : Nat := 4983230072969 + 3 ^ 40 * 8103278 * 2
def baseEnd_8103278 : Nat := 462319610111539124584301

theorem tailTrace_8103278 : CollatzResearch.WordTrace tailWord_8103278 prefixEnd_8103278 462319610111539124584301 := by
  unfold tailWord_8103278
  simp only [CollatzResearch.WordTrace]
  refine ⟨36943853642151901318404811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197033886091476807031492325 36943853642151901318404811)
  ·
    refine ⟨55415780463227851977607217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36943853642151901318404811 55415780463227851977607217)
    ·
      refine ⟨41561835347420888983205413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55415780463227851977607217 41561835347420888983205413)
      ·
        refine ⟨7792844127641416684351015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41561835347420888983205413 7792844127641416684351015)
        ·
          refine ⟨11689266191462125026526523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7792844127641416684351015 11689266191462125026526523)
          ·
            refine ⟨17533899287193187539789785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11689266191462125026526523 17533899287193187539789785)
            ·
              refine ⟨13150424465394890654842339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17533899287193187539789785 13150424465394890654842339)
              ·
                refine ⟨19725636698092335982263509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13150424465394890654842339 19725636698092335982263509)
                ·
                  refine ⟨462319610111539124584301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19725636698092335982263509 462319610111539124584301)
                  ·
                    rfl

theorem cell23_8103278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 7].length) (baseStart_8103278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103278 prefixEnd_8103278 := by exact prefixLift 8103278
  have htrace : WordTrace (prefixWord ++ tailWord_8103278) baseStart_8103278 baseEnd_8103278 := by
    simpa [prefixWord, tailWord_8103278, baseEnd_8103278] using wordTrace_append hprefix tailTrace_8103278
  have hstable : (prefixWord ++ tailWord_8103278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103278).length < 2 ^ (prefixWord ++ tailWord_8103278).sum := by decide
  have hdescent : baseEnd_8103278 < baseStart_8103278 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103331 : List Nat := [1, 1, 1, 4, 1, 3, 3, 2, 2, 2, 3]
def baseStart_8103331 : Nat := 118140960795 + 8103331 * 2 ^ 59
def prefixEnd_8103331 : Nat := 4983230072969 + 3 ^ 40 * 8103331 * 2
def baseEnd_8103331 : Nat := 4160903705478540413895965

theorem tailTrace_8103331 : CollatzResearch.WordTrace tailWord_8103331 prefixEnd_8103331 4160903705478540413895965 := by
  unfold tailWord_8103331
  simp only [CollatzResearch.WordTrace]
  refine ⟨295552762206023200598917847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197035174804015467065945231 295552762206023200598917847)
  ·
    refine ⟨443329143309034800898376771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295552762206023200598917847 443329143309034800898376771)
    ·
      refine ⟨664993714963552201347565157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443329143309034800898376771 664993714963552201347565157)
      ·
        refine ⟨124686321555666037752668467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 664993714963552201347565157 124686321555666037752668467)
        ·
          refine ⟨187029482333499056629002701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124686321555666037752668467 187029482333499056629002701)
          ·
            refine ⟨70136055875062146235876013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187029482333499056629002701 70136055875062146235876013)
            ·
              refine ⟨26301020953148304838453505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70136055875062146235876013 26301020953148304838453505)
              ·
                refine ⟨19725765714861228628840129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26301020953148304838453505 19725765714861228628840129)
                ·
                  refine ⟨14794324286145921471630097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19725765714861228628840129 14794324286145921471630097)
                  ·
                    refine ⟨11095743214609441103722573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14794324286145921471630097 11095743214609441103722573)
                    ·
                      refine ⟨4160903705478540413895965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11095743214609441103722573 4160903705478540413895965)
                      ·
                        rfl

theorem cell23_8103331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_8103331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103331 prefixEnd_8103331 := by exact prefixLift 8103331
  have htrace : WordTrace (prefixWord ++ tailWord_8103331) baseStart_8103331 baseEnd_8103331 := by
    simpa [prefixWord, tailWord_8103331, baseEnd_8103331] using wordTrace_append hprefix tailTrace_8103331
  have hstable : (prefixWord ++ tailWord_8103331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103331).length < 2 ^ (prefixWord ++ tailWord_8103331).sum := by decide
  have hdescent : baseEnd_8103331 < baseStart_8103331 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103344 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 3]
def baseStart_8103344 : Nat := 118140960795 + 8103344 * 2 ^ 59
def prefixEnd_8103344 : Nat := 4983230072969 + 3 ^ 40 * 8103344 * 2
def baseEnd_8103344 : Nat := 4160910380727048863033405

theorem tailTrace_8103344 : CollatzResearch.WordTrace tailWord_8103344 prefixEnd_8103344 4160910380727048863033405 := by
  unfold tailWord_8103344
  simp only [CollatzResearch.WordTrace]
  refine ⟨147776618177488051909570543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197035490903317402546094057 147776618177488051909570543)
  ·
    refine ⟨221664927266232077864355815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147776618177488051909570543 221664927266232077864355815)
    ·
      refine ⟨332497390899348116796533723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221664927266232077864355815 332497390899348116796533723)
      ·
        refine ⟨498746086349022175194800585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332497390899348116796533723 498746086349022175194800585)
        ·
          refine ⟨374059564761766631396100439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498746086349022175194800585 374059564761766631396100439)
          ·
            refine ⟨561089347142649947094150659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374059564761766631396100439 561089347142649947094150659)
            ·
              refine ⟨841634020713974920641225989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561089347142649947094150659 841634020713974920641225989)
              ·
                refine ⟨157806378883870297620229873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 841634020713974920641225989 157806378883870297620229873)
                ·
                  refine ⟨118354784162902723215172405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157806378883870297620229873 118354784162902723215172405)
                  ·
                    refine ⟨11095761015272130301422413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118354784162902723215172405 11095761015272130301422413)
                    ·
                      refine ⟨4160910380727048863033405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11095761015272130301422413 4160910380727048863033405)
                      ·
                        rfl

theorem cell23_8103344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 3].length) (baseStart_8103344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103344 prefixEnd_8103344 := by exact prefixLift 8103344
  have htrace : WordTrace (prefixWord ++ tailWord_8103344) baseStart_8103344 baseEnd_8103344 := by
    simpa [prefixWord, tailWord_8103344, baseEnd_8103344] using wordTrace_append hprefix tailTrace_8103344
  have hstable : (prefixWord ++ tailWord_8103344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103344).length < 2 ^ (prefixWord ++ tailWord_8103344).sum := by decide
  have hdescent : baseEnd_8103344 < baseStart_8103344 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103371 : List Nat := [1, 1, 1, 1, 3, 3, 2, 3, 1, 5, 2]
def baseStart_8103371 : Nat := 118140960795 + 8103371 * 2 ^ 59
def prefixEnd_8103371 : Nat := 4983230072969 + 3 ^ 40 * 8103371 * 2
def baseEnd_8103371 : Nat := 4160924244704720257395781

theorem tailTrace_8103371 : CollatzResearch.WordTrace tailWord_8103371 prefixEnd_8103371 4160924244704720257395781 := by
  unfold tailWord_8103371
  simp only [CollatzResearch.WordTrace]
  refine ⟨295554221125878287430373967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197036147417252191620249311 295554221125878287430373967)
  ·
    refine ⟨443331331688817431145560951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295554221125878287430373967 443331331688817431145560951)
    ·
      refine ⟨664996997533226146718341427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443331331688817431145560951 664996997533226146718341427)
      ·
        refine ⟨997495496299839220077512141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664996997533226146718341427 997495496299839220077512141)
        ·
          refine ⟨374060811112439707529067053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 997495496299839220077512141 374060811112439707529067053)
          ·
            refine ⟨140272804167164890323400145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374060811112439707529067053 140272804167164890323400145)
            ·
              refine ⟨105204603125373667742550109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140272804167164890323400145 105204603125373667742550109)
              ·
                refine ⟨39451726172015125403456291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105204603125373667742550109 39451726172015125403456291)
                ·
                  refine ⟨59177589258022688105184437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39451726172015125403456291 59177589258022688105184437)
                  ·
                    refine ⟨5547898992939627009861041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59177589258022688105184437 5547898992939627009861041)
                    ·
                      refine ⟨4160924244704720257395781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5547898992939627009861041 4160924244704720257395781)
                      ·
                        rfl

theorem cell23_8103371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 5, 2].length) (baseStart_8103371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103371 prefixEnd_8103371 := by exact prefixLift 8103371
  have htrace : WordTrace (prefixWord ++ tailWord_8103371) baseStart_8103371 baseEnd_8103371 := by
    simpa [prefixWord, tailWord_8103371, baseEnd_8103371] using wordTrace_append hprefix tailTrace_8103371
  have hstable : (prefixWord ++ tailWord_8103371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103371).length < 2 ^ (prefixWord ++ tailWord_8103371).sum := by decide
  have hdescent : baseEnd_8103371 < baseStart_8103371 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103422 : List Nat := [4, 2, 2, 3, 1, 1, 1, 1, 1, 5, 2]
def baseStart_8103422 : Nat := 118140960795 + 8103422 * 2 ^ 59
def prefixEnd_8103422 : Nat := 4983230072969 + 3 ^ 40 * 8103422 * 2
def baseEnd_8103422 : Nat := 4160950432218099557858047

theorem tailTrace_8103422 : CollatzResearch.WordTrace tailWord_8103422 prefixEnd_8103422 4160950432218099557858047 := by
  unfold tailWord_8103422
  simp only [CollatzResearch.WordTrace]
  refine ⟨36944510156086690392560065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197037387499129015426987013 36944510156086690392560065)
  ·
    refine ⟨27708382617065017794420049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36944510156086690392560065 27708382617065017794420049)
    ·
      refine ⟨20781286962798763345815037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27708382617065017794420049 20781286962798763345815037)
      ·
        refine ⟨7792982611049536254680639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20781286962798763345815037 7792982611049536254680639)
        ·
          refine ⟨11689473916574304382020959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7792982611049536254680639 11689473916574304382020959)
          ·
            refine ⟨17534210874861456573031439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11689473916574304382020959 17534210874861456573031439)
            ·
              refine ⟨26301316312292184859547159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17534210874861456573031439 26301316312292184859547159)
              ·
                refine ⟨39451974468438277289320739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26301316312292184859547159 39451974468438277289320739)
                ·
                  refine ⟨59177961702657415933981109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39451974468438277289320739 59177961702657415933981109)
                  ·
                    refine ⟨5547933909624132743810729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59177961702657415933981109 5547933909624132743810729)
                    ·
                      refine ⟨4160950432218099557858047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5547933909624132743810729 4160950432218099557858047)
                      ·
                        rfl

theorem cell23_8103422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_8103422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103422 prefixEnd_8103422 := by exact prefixLift 8103422
  have htrace : WordTrace (prefixWord ++ tailWord_8103422) baseStart_8103422 baseEnd_8103422 := by
    simpa [prefixWord, tailWord_8103422, baseEnd_8103422] using wordTrace_append hprefix tailTrace_8103422
  have hstable : (prefixWord ++ tailWord_8103422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103422).length < 2 ^ (prefixWord ++ tailWord_8103422).sum := by decide
  have hdescent : baseEnd_8103422 < baseStart_8103422 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103445 : List Nat := [1, 3, 2, 1, 3, 4, 1, 2, 2, 4]
def baseStart_8103445 : Nat := 118140960795 + 8103445 * 2 ^ 59
def prefixEnd_8103445 : Nat := 4983230072969 + 3 ^ 40 * 8103445 * 2
def baseEnd_8103445 : Nat := 1386987414091050989290147

theorem tailTrace_8103445 : CollatzResearch.WordTrace tailWord_8103445 prefixEnd_8103445 1386987414091050989290147 := by
  unfold tailWord_8103445
  simp only [CollatzResearch.WordTrace]
  refine ⟨295556920127610198068567789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197037946751740132045711859 295556920127610198068567789)
  ·
    refine ⟨110833845047853824275712921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295556920127610198068567789 110833845047853824275712921)
    ·
      refine ⟨83125383785890368206784691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110833845047853824275712921 83125383785890368206784691)
      ·
        refine ⟨124688075678835552310177037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83125383785890368206784691 124688075678835552310177037)
        ·
          refine ⟨46758028379563332116316389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124688075678835552310177037 46758028379563332116316389)
          ·
            refine ⟨8767130321168124771809323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46758028379563332116316389 8767130321168124771809323)
            ·
              refine ⟨13150695481752187157713985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8767130321168124771809323 13150695481752187157713985)
              ·
                refine ⟨9863021611314140368285489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13150695481752187157713985 9863021611314140368285489)
                ·
                  refine ⟨7397266208485605276214117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9863021611314140368285489 7397266208485605276214117)
                  ·
                    refine ⟨1386987414091050989290147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7397266208485605276214117 1386987414091050989290147)
                    ·
                      rfl

theorem cell23_8103445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_8103445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103445 prefixEnd_8103445 := by exact prefixLift 8103445
  have htrace : WordTrace (prefixWord ++ tailWord_8103445) baseStart_8103445 baseEnd_8103445 := by
    simpa [prefixWord, tailWord_8103445, baseEnd_8103445] using wordTrace_append hprefix tailTrace_8103445
  have hstable : (prefixWord ++ tailWord_8103445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103445).length < 2 ^ (prefixWord ++ tailWord_8103445).sum := by decide
  have hdescent : baseEnd_8103445 < baseStart_8103445 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103452 : List Nat := [2, 2, 3, 1, 2, 1, 1, 6, 1, 2, 2]
def baseStart_8103452 : Nat := 118140960795 + 8103452 * 2 ^ 59
def prefixEnd_8103452 : Nat := 4983230072969 + 3 ^ 40 * 8103452 * 2
def baseEnd_8103452 : Nat := 4160965836637734440482909

theorem tailTrace_8103452 : CollatzResearch.WordTrace tailWord_8103452 prefixEnd_8103452 4160965836637734440482909 := by
  unfold tailWord_8103452
  simp only [CollatzResearch.WordTrace]
  refine ⟨147778587719292419132036305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197038116959056558842715073 147778587719292419132036305)
  ·
    refine ⟨110833940789469314349027229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147778587719292419132036305 110833940789469314349027229)
    ·
      refine ⟨41562727796050992880885211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110833940789469314349027229 41562727796050992880885211)
      ·
        refine ⟨62344091694076489321327817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41562727796050992880885211 62344091694076489321327817)
        ·
          refine ⟨46758068770557366990995863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62344091694076489321327817 46758068770557366990995863)
          ·
            refine ⟨70137103155836050486493795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46758068770557366990995863 70137103155836050486493795)
            ·
              refine ⟨105205654733754075729740693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70137103155836050486493795 105205654733754075729740693)
              ·
                refine ⟨4931515065644722299831595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105205654733754075729740693 4931515065644722299831595)
                ·
                  refine ⟨7397272598467083449747393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4931515065644722299831595 7397272598467083449747393)
                  ·
                    refine ⟨5547954448850312587310545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7397272598467083449747393 5547954448850312587310545)
                    ·
                      refine ⟨4160965836637734440482909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5547954448850312587310545 4160965836637734440482909)
                      ·
                        rfl

theorem cell23_8103452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_8103452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103452 prefixEnd_8103452 := by exact prefixLift 8103452
  have htrace : WordTrace (prefixWord ++ tailWord_8103452) baseStart_8103452 baseEnd_8103452 := by
    simpa [prefixWord, tailWord_8103452, baseEnd_8103452] using wordTrace_append hprefix tailTrace_8103452
  have hstable : (prefixWord ++ tailWord_8103452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103452).length < 2 ^ (prefixWord ++ tailWord_8103452).sum := by decide
  have hdescent : baseEnd_8103452 < baseStart_8103452 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103481 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 2, 2, 5]
def baseStart_8103481 : Nat := 118140960795 + 8103481 * 2 ^ 59
def prefixEnd_8103481 : Nat := 4983230072969 + 3 ^ 40 * 8103481 * 2
def baseEnd_8103481 : Nat := 4160980727576714827020275

theorem tailTrace_8103481 : CollatzResearch.WordTrace tailWord_8103481 prefixEnd_8103481 4160980727576714827020275 := by
  unfold tailWord_8103481
  simp only [CollatzResearch.WordTrace]
  refine ⟨295558233155479776216878297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197038822103653184144585531 295558233155479776216878297)
  ·
    refine ⟨221668674866609832162658723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295558233155479776216878297 221668674866609832162658723)
    ·
      refine ⟨332503012299914748243988085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221668674866609832162658723 332503012299914748243988085)
      ·
        refine ⟨31172157403117007647873883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 332503012299914748243988085 31172157403117007647873883)
        ·
          refine ⟨46758236104675511471810825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31172157403117007647873883 46758236104675511471810825)
          ·
            refine ⟨35068677078506633603858119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46758236104675511471810825 35068677078506633603858119)
            ·
              refine ⟨52603015617759950405787179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35068677078506633603858119 52603015617759950405787179)
              ·
                refine ⟨78904523426639925608680769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52603015617759950405787179 78904523426639925608680769)
                ·
                  refine ⟨59178392569979944206510577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78904523426639925608680769 59178392569979944206510577)
                  ·
                    refine ⟨44383794427484958154882933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59178392569979944206510577 44383794427484958154882933)
                    ·
                      refine ⟨4160980727576714827020275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44383794427484958154882933 4160980727576714827020275)
                      ·
                        rfl

theorem cell23_8103481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_8103481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103481 prefixEnd_8103481 := by exact prefixLift 8103481
  have htrace : WordTrace (prefixWord ++ tailWord_8103481) baseStart_8103481 baseEnd_8103481 := by
    simpa [prefixWord, tailWord_8103481, baseEnd_8103481] using wordTrace_append hprefix tailTrace_8103481
  have hstable : (prefixWord ++ tailWord_8103481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103481).length < 2 ^ (prefixWord ++ tailWord_8103481).sum := by decide
  have hdescent : baseEnd_8103481 < baseStart_8103481 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103521 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 1, 4, 4]
def baseStart_8103521 : Nat := 118140960795 + 8103521 * 2 ^ 59
def prefixEnd_8103521 : Nat := 4983230072969 + 3 ^ 40 * 8103521 * 2
def baseEnd_8103521 : Nat := 4161001266802894670520091

theorem tailTrace_8103521 : CollatzResearch.WordTrace tailWord_8103521 prefixEnd_8103521 4161001266802894670520091 := by
  unfold tailWord_8103521
  simp only [CollatzResearch.WordTrace]
  refine ⟨295559692075334863048334417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197039794716889908698889611 295559692075334863048334417)
  ·
    refine ⟨221669769056501147286250813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295559692075334863048334417 221669769056501147286250813)
    ·
      refine ⟨83126163396187930232344055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221669769056501147286250813 83126163396187930232344055)
      ·
        refine ⟨124689245094281895348516083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83126163396187930232344055 124689245094281895348516083)
        ·
          refine ⟨187033867641422843022774125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124689245094281895348516083 187033867641422843022774125)
          ·
            refine ⟨70137700365533566133540297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187033867641422843022774125 70137700365533566133540297)
            ·
              refine ⟨52603275274150174600155223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70137700365533566133540297 52603275274150174600155223)
              ·
                refine ⟨78904912911225261900232835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52603275274150174600155223 78904912911225261900232835)
                ·
                  refine ⟨118357369366837892850349253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78904912911225261900232835 118357369366837892850349253)
                  ·
                    refine ⟨22192006756282104909440485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 118357369366837892850349253 22192006756282104909440485)
                    ·
                      refine ⟨4161001266802894670520091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22192006756282104909440485 4161001266802894670520091)
                      ·
                        rfl

theorem cell23_8103521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_8103521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103521 prefixEnd_8103521 := by exact prefixLift 8103521
  have htrace : WordTrace (prefixWord ++ tailWord_8103521) baseStart_8103521 baseEnd_8103521 := by
    simpa [prefixWord, tailWord_8103521, baseEnd_8103521] using wordTrace_append hprefix tailTrace_8103521
  have hstable : (prefixWord ++ tailWord_8103521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103521).length < 2 ^ (prefixWord ++ tailWord_8103521).sum := by decide
  have hdescent : baseEnd_8103521 < baseStart_8103521 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103528 : List Nat := [2, 1, 4, 3, 1, 1, 1, 2, 2, 1, 5]
def baseStart_8103528 : Nat := 118140960795 + 8103528 * 2 ^ 59
def prefixEnd_8103528 : Nat := 4983230072969 + 3 ^ 40 * 8103528 * 2
def baseEnd_8103528 : Nat := 4161004861167476143132559

theorem tailTrace_8103528 : CollatzResearch.WordTrace tailWord_8103528 prefixEnd_8103528 4161004861167476143132559 := by
  unfold tailWord_8103528
  simp only [CollatzResearch.WordTrace]
  refine ⟨147779973693154751621919619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197039964924206335495892825 147779973693154751621919619)
  ·
    refine ⟨221669960539732127432879429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147779973693154751621919619 221669960539732127432879429)
    ·
      refine ⟨41563117601199773893664893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221669960539732127432879429 41563117601199773893664893)
      ·
        refine ⟨15586169100449915210124335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41563117601199773893664893 15586169100449915210124335)
        ·
          refine ⟨23379253650674872815186503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15586169100449915210124335 23379253650674872815186503)
          ·
            refine ⟨35068880476012309222779755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23379253650674872815186503 35068880476012309222779755)
            ·
              refine ⟨52603320714018463834169633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35068880476012309222779755 52603320714018463834169633)
              ·
                refine ⟨39452490535513847875627225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52603320714018463834169633 39452490535513847875627225)
                ·
                  refine ⟨29589367901635385906720419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39452490535513847875627225 29589367901635385906720419)
                  ·
                    refine ⟨44384051852453078860080629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29589367901635385906720419 44384051852453078860080629)
                    ·
                      refine ⟨4161004861167476143132559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44384051852453078860080629 4161004861167476143132559)
                      ·
                        rfl

theorem cell23_8103528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_8103528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103528 prefixEnd_8103528 := by exact prefixLift 8103528
  have htrace : WordTrace (prefixWord ++ tailWord_8103528) baseStart_8103528 baseEnd_8103528 := by
    simpa [prefixWord, tailWord_8103528, baseEnd_8103528] using wordTrace_append hprefix tailTrace_8103528
  have hstable : (prefixWord ++ tailWord_8103528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103528).length < 2 ^ (prefixWord ++ tailWord_8103528).sum := by decide
  have hdescent : baseEnd_8103528 < baseStart_8103528 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103542 : List Nat := [5, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2]
def baseStart_8103542 : Nat := 118140960795 + 8103542 * 2 ^ 59
def prefixEnd_8103542 : Nat := 4983230072969 + 3 ^ 40 * 8103542 * 2
def baseEnd_8103542 : Nat := 4161012049896639088357495

theorem tailTrace_8103542 : CollatzResearch.WordTrace tailWord_8103542 prefixEnd_8103542 4161012049896639088357495 := by
  unfold tailWord_8103542
  simp only [CollatzResearch.WordTrace]
  refine ⟨18472528625516173977178055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197040305338839189089899253 18472528625516173977178055)
  ·
    refine ⟨27708792938274260965767083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18472528625516173977178055 27708792938274260965767083)
    ·
      refine ⟨41563189407411391448650625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27708792938274260965767083 41563189407411391448650625)
      ·
        refine ⟨31172392055558543586487969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41563189407411391448650625 31172392055558543586487969)
        ·
          refine ⟨23379294041668907689865977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31172392055558543586487969 23379294041668907689865977)
          ·
            refine ⟨17534470531251680767399483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23379294041668907689865977 17534470531251680767399483)
            ·
              refine ⟨26301705796877521151099225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17534470531251680767399483 26301705796877521151099225)
              ·
                refine ⟨19726279347658140863324419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26301705796877521151099225 19726279347658140863324419)
                ·
                  refine ⟨29589419021487211294986629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19726279347658140863324419 29589419021487211294986629)
                  ·
                    refine ⟨5548016066528852117809993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29589419021487211294986629 5548016066528852117809993)
                    ·
                      refine ⟨4161012049896639088357495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5548016066528852117809993 4161012049896639088357495)
                      ·
                        rfl

theorem cell23_8103542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_8103542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103542 prefixEnd_8103542 := by exact prefixLift 8103542
  have htrace : WordTrace (prefixWord ++ tailWord_8103542) baseStart_8103542 baseEnd_8103542 := by
    simpa [prefixWord, tailWord_8103542, baseEnd_8103542] using wordTrace_append hprefix tailTrace_8103542
  have hstable : (prefixWord ++ tailWord_8103542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103542).length < 2 ^ (prefixWord ++ tailWord_8103542).sum := by decide
  have hdescent : baseEnd_8103542 < baseStart_8103542 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103548 : List Nat := [2, 2, 2, 1, 1, 2, 1, 7, 5]
def baseStart_8103548 : Nat := 118140960795 + 8103548 * 2 ^ 59
def prefixEnd_8103548 : Nat := 4983230072969 + 3 ^ 40 * 8103548 * 2
def baseEnd_8103548 : Nat := 462335014531174007209163

theorem tailTrace_8103548 : CollatzResearch.WordTrace tailWord_8103548 prefixEnd_8103548 462335014531174007209163 := by
  unfold tailWord_8103548
  simp only [CollatzResearch.WordTrace]
  refine ⟨147780338423118523329783649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197040451230824697773044865 147780338423118523329783649)
  ·
    refine ⟨110835253817338892497337737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147780338423118523329783649 110835253817338892497337737)
    ·
      refine ⟨83126440363004169373003303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110835253817338892497337737 83126440363004169373003303)
      ·
        refine ⟨124689660544506254059504955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83126440363004169373003303 124689660544506254059504955)
        ·
          refine ⟨187034490816759381089257433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124689660544506254059504955 187034490816759381089257433)
          ·
            refine ⟨140275868112569535816943075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187034490816759381089257433 140275868112569535816943075)
            ·
              refine ⟨210413802168854303725414613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140275868112569535816943075 210413802168854303725414613)
              ·
                refine ⟨4931573488332522743564405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 210413802168854303725414613 4931573488332522743564405)
                ·
                  refine ⟨462335014531174007209163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4931573488332522743564405 462335014531174007209163)
                  ·
                    rfl

theorem cell23_8103548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 7, 5].length) (baseStart_8103548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103548 prefixEnd_8103548 := by exact prefixLift 8103548
  have htrace : WordTrace (prefixWord ++ tailWord_8103548) baseStart_8103548 baseEnd_8103548 := by
    simpa [prefixWord, tailWord_8103548, baseEnd_8103548] using wordTrace_append hprefix tailTrace_8103548
  have hstable : (prefixWord ++ tailWord_8103548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103548).length < 2 ^ (prefixWord ++ tailWord_8103548).sum := by decide
  have hdescent : baseEnd_8103548 < baseStart_8103548 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103611 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 4]
def baseStart_8103611 : Nat := 118140960795 + 8103611 * 2 ^ 59
def prefixEnd_8103611 : Nat := 4983230072969 + 3 ^ 40 * 8103611 * 2
def baseEnd_8103611 : Nat := 4161047480061799318394677

theorem tailTrace_8103611 : CollatzResearch.WordTrace tailWord_8103611 prefixEnd_8103611 4161047480061799318394677 := by
  unfold tailWord_8103611
  simp only [CollatzResearch.WordTrace]
  refine ⟨295562974645008808419110687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197041983096672538946073791 295562974645008808419110687)
  ·
    refine ⟨443344461967513212628666031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295562974645008808419110687 443344461967513212628666031)
    ·
      refine ⟨665016692951269818942999047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443344461967513212628666031 665016692951269818942999047)
      ·
        refine ⟨997525039426904728414498571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665016692951269818942999047 997525039426904728414498571)
        ·
          refine ⟨1496287559140357092621747857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 997525039426904728414498571 1496287559140357092621747857)
          ·
            refine ⟨1122215669355267819466310893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1496287559140357092621747857 1122215669355267819466310893)
            ·
              refine ⟨420830876008225432299866585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1122215669355267819466310893 420830876008225432299866585)
              ·
                refine ⟨315623157006169074224899939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 420830876008225432299866585 315623157006169074224899939)
                ·
                  refine ⟨473434735509253611337349909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 315623157006169074224899939 473434735509253611337349909)
                  ·
                    refine ⟨22192253226996263031438277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 473434735509253611337349909 22192253226996263031438277)
                    ·
                      refine ⟨4161047480061799318394677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22192253226996263031438277 4161047480061799318394677)
                      ·
                        rfl

theorem cell23_8103611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 4].length) (baseStart_8103611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103611 prefixEnd_8103611 := by exact prefixLift 8103611
  have htrace : WordTrace (prefixWord ++ tailWord_8103611) baseStart_8103611 baseEnd_8103611 := by
    simpa [prefixWord, tailWord_8103611, baseEnd_8103611] using wordTrace_append hprefix tailTrace_8103611
  have hstable : (prefixWord ++ tailWord_8103611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103611).length < 2 ^ (prefixWord ++ tailWord_8103611).sum := by decide
  have hdescent : baseEnd_8103611 < baseStart_8103611 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103621 : List Nat := [1, 3, 1, 1, 1, 1, 2, 5, 8]
def baseStart_8103621 : Nat := 118140960795 + 8103621 * 2 ^ 59
def prefixEnd_8103621 : Nat := 4983230072969 + 3 ^ 40 * 8103621 * 2
def baseEnd_8103621 : Nat := 462339179429816031029959

theorem tailTrace_8103621 : CollatzResearch.WordTrace tailWord_8103621 prefixEnd_8103621 462339179429816031029959 := by
  unfold tailWord_8103621
  simp only [CollatzResearch.WordTrace]
  refine ⟨295563339374972580126974717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197042226249981720084649811 295563339374972580126974717)
  ·
    refine ⟨110836252265614717547615519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295563339374972580126974717 110836252265614717547615519)
    ·
      refine ⟨166254378398422076321423279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110836252265614717547615519 166254378398422076321423279)
      ·
        refine ⟨249381567597633114482134919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166254378398422076321423279 249381567597633114482134919)
        ·
          refine ⟨374072351396449671723202379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249381567597633114482134919 374072351396449671723202379)
          ·
            refine ⟨561108527094674507584803569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374072351396449671723202379 561108527094674507584803569)
            ·
              refine ⟨420831395321005880688602677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 561108527094674507584803569 420831395321005880688602677)
              ·
                refine ⟨39452943311344301314556501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 420831395321005880688602677 39452943311344301314556501)
                ·
                  refine ⟨462339179429816031029959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39452943311344301314556501 462339179429816031029959)
                  ·
                    rfl

theorem cell23_8103621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 8].length) (baseStart_8103621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103621 prefixEnd_8103621 := by exact prefixLift 8103621
  have htrace : WordTrace (prefixWord ++ tailWord_8103621) baseStart_8103621 baseEnd_8103621 := by
    simpa [prefixWord, tailWord_8103621, baseEnd_8103621] using wordTrace_append hprefix tailTrace_8103621
  have hstable : (prefixWord ++ tailWord_8103621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103621).length < 2 ^ (prefixWord ++ tailWord_8103621).sum := by decide
  have hdescent : baseEnd_8103621 < baseStart_8103621 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103733 : List Nat := [1, 3, 3, 1, 4, 2, 2, 2, 1, 1, 3]
def baseStart_8103733 : Nat := 118140960795 + 8103733 * 2 ^ 59
def prefixEnd_8103733 : Nat := 4983230072969 + 3 ^ 40 * 8103733 * 2
def baseEnd_8103733 : Nat := 4161110124701647841069117

theorem tailTrace_8103733 : CollatzResearch.WordTrace tailWord_8103733 prefixEnd_8103733 4161110124701647841069117 := by
  unfold tailWord_8103733
  simp only [CollatzResearch.WordTrace]
  refine ⟨295567424350566823255051853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197044949567044548836701235 295567424350566823255051853)
  ·
    refine ⟨110837784131462558720644445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295567424350566823255051853 110837784131462558720644445)
    ·
      refine ⟨41564169049298459520241667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110837784131462558720644445 41564169049298459520241667)
      ·
        refine ⟨62346253573947689280362501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41564169049298459520241667 62346253573947689280362501)
        ·
          refine ⟨11689922545115191740067969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62346253573947689280362501 11689922545115191740067969)
          ·
            refine ⟨8767441908836393805050977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11689922545115191740067969 8767441908836393805050977)
            ·
              refine ⟨6575581431627295353788233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8767441908836393805050977 6575581431627295353788233)
              ·
                refine ⟨4931686073720471515341175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6575581431627295353788233 4931686073720471515341175)
                ·
                  refine ⟨7397529110580707273011763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4931686073720471515341175 7397529110580707273011763)
                  ·
                    refine ⟨11096293665871060909517645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7397529110580707273011763 11096293665871060909517645)
                    ·
                      refine ⟨4161110124701647841069117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11096293665871060909517645 4161110124701647841069117)
                      ·
                        rfl

theorem cell23_8103733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_8103733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103733 prefixEnd_8103733 := by exact prefixLift 8103733
  have htrace : WordTrace (prefixWord ++ tailWord_8103733) baseStart_8103733 baseEnd_8103733 := by
    simpa [prefixWord, tailWord_8103733, baseEnd_8103733] using wordTrace_append hprefix tailTrace_8103733
  have hstable : (prefixWord ++ tailWord_8103733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103733).length < 2 ^ (prefixWord ++ tailWord_8103733).sum := by decide
  have hdescent : baseEnd_8103733 < baseStart_8103733 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103742 : List Nat := [4, 2, 1, 2, 2, 1, 1, 2, 3, 2, 3]
def baseStart_8103742 : Nat := 118140960795 + 8103742 * 2 ^ 59
def prefixEnd_8103742 : Nat := 4983230072969 + 3 ^ 40 * 8103742 * 2
def baseEnd_8103742 : Nat := 4161114746027538305856575

theorem tailTrace_8103742 : CollatzResearch.WordTrace tailWord_8103742 prefixEnd_8103742 4161114746027538305856575 := by
  unfold tailWord_8103742
  simp only [CollatzResearch.WordTrace]
  refine ⟨36945969075941777224016185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197045168405022811861419653 36945969075941777224016185)
  ·
    refine ⟨27709476806956332918012139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36945969075941777224016185 27709476806956332918012139)
    ·
      refine ⟨41564215210434499377018209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27709476806956332918012139 41564215210434499377018209)
      ·
        refine ⟨31173161407825874532763657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41564215210434499377018209 31173161407825874532763657)
        ·
          refine ⟨23379871055869405899572743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31173161407825874532763657 23379871055869405899572743)
          ·
            refine ⟨35069806583804108849359115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23379871055869405899572743 35069806583804108849359115)
            ·
              refine ⟨52604709875706163274038673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35069806583804108849359115 52604709875706163274038673)
              ·
                refine ⟨39453532406779622455529005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52604709875706163274038673 39453532406779622455529005)
                ·
                  refine ⟨14795074652542358420823377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39453532406779622455529005 14795074652542358420823377)
                  ·
                    refine ⟨11096305989406768815617533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14795074652542358420823377 11096305989406768815617533)
                    ·
                      refine ⟨4161114746027538305856575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11096305989406768815617533 4161114746027538305856575)
                      ·
                        rfl

theorem cell23_8103742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_8103742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103742 prefixEnd_8103742 := by exact prefixLift 8103742
  have htrace : WordTrace (prefixWord ++ tailWord_8103742) baseStart_8103742 baseEnd_8103742 := by
    simpa [prefixWord, tailWord_8103742, baseEnd_8103742] using wordTrace_append hprefix tailTrace_8103742
  have hstable : (prefixWord ++ tailWord_8103742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103742).length < 2 ^ (prefixWord ++ tailWord_8103742).sum := by decide
  have hdescent : baseEnd_8103742 < baseStart_8103742 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103789 : List Nat := [1, 5, 1, 1, 1, 1, 5, 2, 2, 1, 3]
def baseStart_8103789 : Nat := 118140960795 + 8103789 * 2 ^ 59
def prefixEnd_8103789 : Nat := 4983230072969 + 3 ^ 40 * 8103789 * 2
def baseEnd_8103789 : Nat := 4161138879618299621968859

theorem tailTrace_8103789 : CollatzResearch.WordTrace tailWord_8103789 prefixEnd_8103789 4161138879618299621968859 := by
  unfold tailWord_8103789
  simp only [CollatzResearch.WordTrace]
  refine ⟨295569466838363944819090421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197046311225575963212726947 295569466838363944819090421)
  ·
    refine ⟨27709637516096619826789727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 295569466838363944819090421 27709637516096619826789727)
    ·
      refine ⟨41564456274144929740184591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27709637516096619826789727 41564456274144929740184591)
      ·
        refine ⟨62346684411217394610276887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41564456274144929740184591 62346684411217394610276887)
        ·
          refine ⟨93520026616826091915415331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62346684411217394610276887 93520026616826091915415331)
          ·
            refine ⟨140280039925239137873122997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93520026616826091915415331 140280039925239137873122997)
            ·
              refine ⟨13151253742991169175605281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140280039925239137873122997 13151253742991169175605281)
              ·
                refine ⟨9863440307243376881703961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13151253742991169175605281 9863440307243376881703961)
                ·
                  refine ⟨7397580230432532661277971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9863440307243376881703961 7397580230432532661277971)
                  ·
                    refine ⟨11096370345648798991916957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7397580230432532661277971 11096370345648798991916957)
                    ·
                      refine ⟨4161138879618299621968859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11096370345648798991916957 4161138879618299621968859)
                      ·
                        rfl

theorem cell23_8103789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_8103789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103789 prefixEnd_8103789 := by exact prefixLift 8103789
  have htrace : WordTrace (prefixWord ++ tailWord_8103789) baseStart_8103789 baseEnd_8103789 := by
    simpa [prefixWord, tailWord_8103789, baseEnd_8103789] using wordTrace_append hprefix tailTrace_8103789
  have hstable : (prefixWord ++ tailWord_8103789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103789).length < 2 ^ (prefixWord ++ tailWord_8103789).sum := by decide
  have hdescent : baseEnd_8103789 < baseStart_8103789 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103806 : List Nat := [4, 2, 3, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_8103806 : Nat := 118140960795 + 8103806 * 2 ^ 59
def prefixEnd_8103806 : Nat := 4983230072969 + 3 ^ 40 * 8103806 * 2
def baseEnd_8103806 : Nat := 4161147608789426055456281

theorem tailTrace_8103806 : CollatzResearch.WordTrace tailWord_8103806 prefixEnd_8103806 4161147608789426055456281 := by
  unfold tailWord_8103806
  simp only [CollatzResearch.WordTrace]
  refine ⟨36946260859912794590307409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197046724586201571148306181 36946260859912794590307409)
  ·
    refine ⟨27709695644934595942730557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36946260859912794590307409 27709695644934595942730557)
    ·
      refine ⟨10391135866850473478523959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27709695644934595942730557 10391135866850473478523959)
      ·
        refine ⟨15586703800275710217785939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10391135866850473478523959 15586703800275710217785939)
        ·
          refine ⟨23380055700413565326678909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15586703800275710217785939 23380055700413565326678909)
          ·
            refine ⟨8767520887655086997504591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23380055700413565326678909 8767520887655086997504591)
            ·
              refine ⟨13151281331482630496256887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8767520887655086997504591 13151281331482630496256887)
              ·
                refine ⟨19726921997223945744385331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13151281331482630496256887 19726921997223945744385331)
                ·
                  refine ⟨29590382995835918616577997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19726921997223945744385331 29590382995835918616577997)
                  ·
                    refine ⟨11096393623438469481216749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29590382995835918616577997 11096393623438469481216749)
                    ·
                      refine ⟨4161147608789426055456281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11096393623438469481216749 4161147608789426055456281)
                      ·
                        rfl

theorem cell23_8103806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_8103806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103806 prefixEnd_8103806 := by exact prefixLift 8103806
  have htrace : WordTrace (prefixWord ++ tailWord_8103806) baseStart_8103806 baseEnd_8103806 := by
    simpa [prefixWord, tailWord_8103806, baseEnd_8103806] using wordTrace_append hprefix tailTrace_8103806
  have hstable : (prefixWord ++ tailWord_8103806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103806).length < 2 ^ (prefixWord ++ tailWord_8103806).sum := by decide
  have hdescent : baseEnd_8103806 < baseStart_8103806 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103816 : List Nat := [2, 1, 3, 3, 3, 1, 2, 2, 1, 3, 2]
def baseStart_8103816 : Nat := 118140960795 + 8103816 * 2 ^ 59
def prefixEnd_8103816 : Nat := 4983230072969 + 3 ^ 40 * 8103816 * 2
def baseEnd_8103816 : Nat := 4161152743595971016331235

theorem tailTrace_8103816 : CollatzResearch.WordTrace tailWord_8103816 prefixEnd_8103816 4161152743595971016331235 := by
  unfold tailWord_8103816
  simp only [CollatzResearch.WordTrace]
  refine ⟨147785225804633064215161651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197046967739510752286882201 147785225804633064215161651)
  ·
    refine ⟨221677838706949596322742477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147785225804633064215161651 221677838706949596322742477)
    ·
      refine ⟨83129189515106098621028429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221677838706949596322742477 83129189515106098621028429)
      ·
        refine ⟨31173446068164786982885661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83129189515106098621028429 31173446068164786982885661)
        ·
          refine ⟨11690042275561795118582123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31173446068164786982885661 11690042275561795118582123)
          ·
            refine ⟨17535063413342692677873185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11690042275561795118582123 17535063413342692677873185)
            ·
              refine ⟨13151297560007019508404889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17535063413342692677873185 13151297560007019508404889)
              ·
                refine ⟨9863473170005264631303667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13151297560007019508404889 9863473170005264631303667)
                ·
                  refine ⟨14795209755007896946955501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9863473170005264631303667 14795209755007896946955501)
                  ·
                    refine ⟨5548203658127961355108313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14795209755007896946955501 5548203658127961355108313)
                    ·
                      refine ⟨4161152743595971016331235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5548203658127961355108313 4161152743595971016331235)
                      ·
                        rfl

theorem cell23_8103816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_8103816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103816 prefixEnd_8103816 := by exact prefixLift 8103816
  have htrace : WordTrace (prefixWord ++ tailWord_8103816) baseStart_8103816 baseEnd_8103816 := by
    simpa [prefixWord, tailWord_8103816, baseEnd_8103816] using wordTrace_append hprefix tailTrace_8103816
  have hstable : (prefixWord ++ tailWord_8103816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103816).length < 2 ^ (prefixWord ++ tailWord_8103816).sum := by decide
  have hdescent : baseEnd_8103816 < baseStart_8103816 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103845 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 4, 3, 3]
def baseStart_8103845 : Nat := 118140960795 + 8103845 * 2 ^ 59
def prefixEnd_8103845 : Nat := 4983230072969 + 3 ^ 40 * 8103845 * 2
def baseEnd_8103845 : Nat := 4161167634534951402868601

theorem tailTrace_8103845 : CollatzResearch.WordTrace tailWord_8103845 prefixEnd_8103845 4161167634534951402868601 := by
  unfold tailWord_8103845
  simp only [CollatzResearch.WordTrace]
  refine ⟨295571509326161066383128989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197047672884107377588752659 295571509326161066383128989)
  ·
    refine ⟨110839315997310399893673371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295571509326161066383128989 110839315997310399893673371)
    ·
      refine ⟨166258973995965599840510057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110839315997310399893673371 166258973995965599840510057)
      ·
        refine ⟨124694230496974199880382543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166258973995965599840510057 124694230496974199880382543)
        ·
          refine ⟨187041345745461299820573815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124694230496974199880382543 187041345745461299820573815)
          ·
            refine ⟨280562018618191949730860723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187041345745461299820573815 280562018618191949730860723)
            ·
              refine ⟨420843027927287924596291085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280562018618191949730860723 420843027927287924596291085)
              ·
                refine ⟨157816135472732971723609157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 420843027927287924596291085 157816135472732971723609157)
                ·
                  refine ⟨29590525401137432198176717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157816135472732971723609157 29590525401137432198176717)
                  ·
                    refine ⟨11096447025426537074316269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29590525401137432198176717 11096447025426537074316269)
                    ·
                      refine ⟨4161167634534951402868601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11096447025426537074316269 4161167634534951402868601)
                      ·
                        rfl

theorem cell23_8103845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_8103845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103845 prefixEnd_8103845 := by exact prefixLift 8103845
  have htrace : WordTrace (prefixWord ++ tailWord_8103845) baseStart_8103845 baseEnd_8103845 := by
    simpa [prefixWord, tailWord_8103845, baseEnd_8103845] using wordTrace_append hprefix tailTrace_8103845
  have hstable : (prefixWord ++ tailWord_8103845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103845).length < 2 ^ (prefixWord ++ tailWord_8103845).sum := by decide
  have hdescent : baseEnd_8103845 < baseStart_8103845 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103865 : List Nat := [1, 2, 1, 4, 2, 1, 1, 2, 4, 5]
def baseStart_8103865 : Nat := 118140960795 + 8103865 * 2 ^ 59
def prefixEnd_8103865 : Nat := 4983230072969 + 3 ^ 40 * 8103865 * 2
def baseEnd_8103865 : Nat := 1387059301382680441539503

theorem tailTrace_8103865 : CollatzResearch.WordTrace tailWord_8103865 prefixEnd_8103865 1387059301382680441539503 := by
  unfold tailWord_8103865
  simp only [CollatzResearch.WordTrace]
  refine ⟨295572238786088609798857049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197048159190725739865904699 295572238786088609798857049)
  ·
    refine ⟨221679179089566457349142787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295572238786088609798857049 221679179089566457349142787)
    ·
      refine ⟨332518768634349686023714181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221679179089566457349142787 332518768634349686023714181)
      ·
        refine ⟨62347269118940566129446409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 332518768634349686023714181 62347269118940566129446409)
        ·
          refine ⟨46760451839205424597084807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62347269118940566129446409 46760451839205424597084807)
          ·
            refine ⟨70140677758808136895627211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46760451839205424597084807 70140677758808136895627211)
            ·
              refine ⟨105211016638212205343440817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70140677758808136895627211 105211016638212205343440817)
              ·
                refine ⟨78908262478659154007580613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105211016638212205343440817 78908262478659154007580613)
                ·
                  refine ⟨14795299214748591376421365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78908262478659154007580613 14795299214748591376421365)
                  ·
                    refine ⟨1387059301382680441539503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14795299214748591376421365 1387059301382680441539503)
                    ·
                      rfl

theorem cell23_8103865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 5].length) (baseStart_8103865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103865 prefixEnd_8103865 := by exact prefixLift 8103865
  have htrace : WordTrace (prefixWord ++ tailWord_8103865) baseStart_8103865 baseEnd_8103865 := by
    simpa [prefixWord, tailWord_8103865, baseEnd_8103865] using wordTrace_append hprefix tailTrace_8103865
  have hstable : (prefixWord ++ tailWord_8103865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103865).length < 2 ^ (prefixWord ++ tailWord_8103865).sum := by decide
  have hdescent : baseEnd_8103865 < baseStart_8103865 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8103912 : List Nat := [2, 1, 4, 1, 1, 1, 1, 5, 3, 4]
def baseStart_8103912 : Nat := 118140960795 + 8103912 * 2 ^ 59
def prefixEnd_8103912 : Nat := 4983230072969 + 3 ^ 40 * 8103912 * 2
def baseEnd_8103912 : Nat := 1387067345912934213576931

theorem tailTrace_8103912 : CollatzResearch.WordTrace tailWord_8103912 prefixEnd_8103912 1387067345912934213576931 := by
  unfold tailWord_8103912
  simp only [CollatzResearch.WordTrace]
  refine ⟨147786976508459168412908995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197049302011278891217211993 147786976508459168412908995)
  ·
    refine ⟨221680464762688752619363493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147786976508459168412908995 221680464762688752619363493)
    ·
      refine ⟨41565087143004141116130655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221680464762688752619363493 41565087143004141116130655)
      ·
        refine ⟨62347630714506211674195983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41565087143004141116130655 62347630714506211674195983)
        ·
          refine ⟨93521446071759317511293975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62347630714506211674195983 93521446071759317511293975)
          ·
            refine ⟨140282169107638976266940963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93521446071759317511293975 140282169107638976266940963)
            ·
              refine ⟨210423253661458464400411445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140282169107638976266940963 210423253661458464400411445)
              ·
                refine ⟨19727180030761731037538573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 210423253661458464400411445 19727180030761731037538573)
                ·
                  refine ⟨7397692511535649139076965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19727180030761731037538573 7397692511535649139076965)
                  ·
                    refine ⟨1387067345912934213576931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7397692511535649139076965 1387067345912934213576931)
                    ·
                      rfl

theorem cell23_8103912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_8103912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8103912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8103912 prefixEnd_8103912 := by exact prefixLift 8103912
  have htrace : WordTrace (prefixWord ++ tailWord_8103912) baseStart_8103912 baseEnd_8103912 := by
    simpa [prefixWord, tailWord_8103912, baseEnd_8103912] using wordTrace_append hprefix tailTrace_8103912
  have hstable : (prefixWord ++ tailWord_8103912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8103912).length < 2 ^ (prefixWord ++ tailWord_8103912).sum := by decide
  have hdescent : baseEnd_8103912 < baseStart_8103912 := by decide
  rcases family_descends (prefixWord ++ tailWord_8103912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104006 : List Nat := [6, 1, 1, 1, 1, 1, 1, 5, 1, 5]
def baseStart_8104006 : Nat := 118140960795 + 8104006 * 2 ^ 59
def prefixEnd_8104006 : Nat := 4983230072969 + 3 ^ 40 * 8104006 * 2
def baseEnd_8104006 : Nat := 1387083434973441757651787

theorem tailTrace_8104006 : CollatzResearch.WordTrace tailWord_8104006 prefixEnd_8104006 1387083434973441757651787 := by
  unfold tailWord_8104006
  simp only [CollatzResearch.WordTrace]
  refine ⟨9236793171205555964991871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 197051587652385193919826581 9236793171205555964991871)
  ·
    refine ⟨13855189756808333947487807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9236793171205555964991871 13855189756808333947487807)
    ·
      refine ⟨20782784635212500921231711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13855189756808333947487807 20782784635212500921231711)
      ·
        refine ⟨31174176952818751381847567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20782784635212500921231711 31174176952818751381847567)
        ·
          refine ⟨46761265429228127072771351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31174176952818751381847567 46761265429228127072771351)
          ·
            refine ⟨70141898143842190609157027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46761265429228127072771351 70141898143842190609157027)
            ·
              refine ⟨105212847215763285913735541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70141898143842190609157027 105212847215763285913735541)
              ·
                refine ⟨9863704426477808054412707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105212847215763285913735541 9863704426477808054412707)
                ·
                  refine ⟨14795556639716712081619061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9863704426477808054412707 14795556639716712081619061)
                  ·
                    refine ⟨1387083434973441757651787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14795556639716712081619061 1387083434973441757651787)
                    ·
                      rfl

theorem cell23_8104006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_8104006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104006 prefixEnd_8104006 := by exact prefixLift 8104006
  have htrace : WordTrace (prefixWord ++ tailWord_8104006) baseStart_8104006 baseEnd_8104006 := by
    simpa [prefixWord, tailWord_8104006, baseEnd_8104006] using wordTrace_append hprefix tailTrace_8104006
  have hstable : (prefixWord ++ tailWord_8104006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104006).length < 2 ^ (prefixWord ++ tailWord_8104006).sum := by decide
  have hdescent : baseEnd_8104006 < baseStart_8104006 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104012 : List Nat := [2, 2, 1, 3, 1, 1, 3, 3, 1, 1, 5]
def baseStart_8104012 : Nat := 118140960795 + 8104012 * 2 ^ 59
def prefixEnd_8104012 : Nat := 4983230072969 + 3 ^ 40 * 8104012 * 2
def baseEnd_8104012 : Nat := 4161253385804252249480333

theorem tailTrace_8104012 : CollatzResearch.WordTrace tailWord_8104012 prefixEnd_8104012 4161253385804252249480333 := by
  unfold tailWord_8104012
  simp only [CollatzResearch.WordTrace]
  refine ⟨147788800158278026952229145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197051733544370702602972193 147788800158278026952229145)
  ·
    refine ⟨110841600118708520214171859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147788800158278026952229145 110841600118708520214171859)
    ·
      refine ⟨166262400178062780321257789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110841600118708520214171859 166262400178062780321257789)
      ·
        refine ⟨62348400066773542620471671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166262400178062780321257789 62348400066773542620471671)
        ·
          refine ⟨93522600100160313930707507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62348400066773542620471671 93522600100160313930707507)
          ·
            refine ⟨140283900150240470896061261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93522600100160313930707507 140283900150240470896061261)
            ·
              refine ⟨52606462556340176586022973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140283900150240470896061261 52606462556340176586022973)
              ·
                refine ⟨19727423458627566219758615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52606462556340176586022973 19727423458627566219758615)
                ·
                  refine ⟨29591135187941349329637923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19727423458627566219758615 29591135187941349329637923)
                  ·
                    refine ⟨44386702781912023994456885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29591135187941349329637923 44386702781912023994456885)
                    ·
                      refine ⟨4161253385804252249480333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44386702781912023994456885 4161253385804252249480333)
                      ·
                        rfl

theorem cell23_8104012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_8104012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104012 prefixEnd_8104012 := by exact prefixLift 8104012
  have htrace : WordTrace (prefixWord ++ tailWord_8104012) baseStart_8104012 baseEnd_8104012 := by
    simpa [prefixWord, tailWord_8104012, baseEnd_8104012] using wordTrace_append hprefix tailTrace_8104012
  have hstable : (prefixWord ++ tailWord_8104012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104012).length < 2 ^ (prefixWord ++ tailWord_8104012).sum := by decide
  have hdescent : baseEnd_8104012 < baseStart_8104012 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104032 : List Nat := [2, 1, 1, 3, 2, 4, 2, 8]
def baseStart_8104032 : Nat := 118140960795 + 8104032 * 2 ^ 59
def prefixEnd_8104032 : Nat := 4983230072969 + 3 ^ 40 * 8104032 * 2
def baseEnd_8104032 : Nat := 154120876126568228564083

theorem tailTrace_8104032 : CollatzResearch.WordTrace tailWord_8104032 prefixEnd_8104032 154120876126568228564083 := by
  unfold tailWord_8104032
  simp only [CollatzResearch.WordTrace]
  refine ⟨147789164888241798660093175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197052219850989064880124233 147789164888241798660093175)
  ·
    refine ⟨221683747332362697990139763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147789164888241798660093175 221683747332362697990139763)
    ·
      refine ⟨332525620998544046985209645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221683747332362697990139763 332525620998544046985209645)
      ·
        refine ⟨124697107874454017619453617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332525620998544046985209645 124697107874454017619453617)
        ·
          refine ⟨93522830905840513214590213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124697107874454017619453617 93522830905840513214590213)
          ·
            refine ⟨17535530794845096227735665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93522830905840513214590213 17535530794845096227735665)
            ·
              refine ⟨13151648096133822170801749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17535530794845096227735665 13151648096133822170801749)
              ·
                refine ⟨154120876126568228564083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13151648096133822170801749 154120876126568228564083)
                ·
                  rfl

theorem cell23_8104032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 8].length) (baseStart_8104032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104032 prefixEnd_8104032 := by exact prefixLift 8104032
  have htrace : WordTrace (prefixWord ++ tailWord_8104032) baseStart_8104032 baseEnd_8104032 := by
    simpa [prefixWord, tailWord_8104032, baseEnd_8104032] using wordTrace_append hprefix tailTrace_8104032
  have hstable : (prefixWord ++ tailWord_8104032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104032).length < 2 ^ (prefixWord ++ tailWord_8104032).sum := by decide
  have hdescent : baseEnd_8104032 < baseStart_8104032 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104036 : List Nat := [2, 3, 1, 1, 2, 1, 6, 1, 2, 4]
def baseStart_8104036 : Nat := 118140960795 + 8104036 * 2 ^ 59
def prefixEnd_8104036 : Nat := 4983230072969 + 3 ^ 40 * 8104036 * 2
def baseEnd_8104036 : Nat := 1387088569779986718526741

theorem tailTrace_8104036 : CollatzResearch.WordTrace tailWord_8104036 prefixEnd_8104036 1387088569779986718526741 := by
  unfold tailWord_8104036
  simp only [CollatzResearch.WordTrace]
  refine ⟨147789237834234553001665981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197052317112312737335554641 147789237834234553001665981)
  ·
    refine ⟨55420964187837957375624743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147789237834234553001665981 55420964187837957375624743)
    ·
      refine ⟨83131446281756936063437115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55420964187837957375624743 83131446281756936063437115)
      ·
        refine ⟨124697169422635404095155673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83131446281756936063437115 124697169422635404095155673)
        ·
          refine ⟨93522877066976553071366755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124697169422635404095155673 93522877066976553071366755)
          ·
            refine ⟨140284315600464829607050133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93522877066976553071366755 140284315600464829607050133)
            ·
              refine ⟨6575827293771788887830475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 140284315600464829607050133 6575827293771788887830475)
              ·
                refine ⟨9863740940657683331745713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6575827293771788887830475 9863740940657683331745713)
                ·
                  refine ⟨7397805705493262498809285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9863740940657683331745713 7397805705493262498809285)
                  ·
                    refine ⟨1387088569779986718526741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7397805705493262498809285 1387088569779986718526741)
                    ·
                      rfl

theorem cell23_8104036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_8104036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104036 prefixEnd_8104036 := by exact prefixLift 8104036
  have htrace : WordTrace (prefixWord ++ tailWord_8104036) baseStart_8104036 baseEnd_8104036 := by
    simpa [prefixWord, tailWord_8104036, baseEnd_8104036] using wordTrace_append hprefix tailTrace_8104036
  have hstable : (prefixWord ++ tailWord_8104036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104036).length < 2 ^ (prefixWord ++ tailWord_8104036).sum := by decide
  have hdescent : baseEnd_8104036 < baseStart_8104036 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104112 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 4]
def baseStart_8104112 : Nat := 118140960795 + 8104112 * 2 ^ 59
def prefixEnd_8104112 : Nat := 4983230072969 + 3 ^ 40 * 8104112 * 2
def baseEnd_8104112 : Nat := 4161304733869701858229873

theorem tailTrace_8104112 : CollatzResearch.WordTrace tailWord_8104112 prefixEnd_8104112 4161304733869701858229873 := by
  unfold tailWord_8104112
  simp only [CollatzResearch.WordTrace]
  refine ⟨147790623808096885491549295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197054165077462513988732393 147790623808096885491549295)
  ·
    refine ⟨221685935712145328237323943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147790623808096885491549295 221685935712145328237323943)
    ·
      refine ⟨332528903568217992355985915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221685935712145328237323943 332528903568217992355985915)
      ·
        refine ⟨498793355352326988533978873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332528903568217992355985915 498793355352326988533978873)
        ·
          refine ⟨374095016514245241400484155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498793355352326988533978873 374095016514245241400484155)
          ·
            refine ⟨561142524771367862100726233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374095016514245241400484155 561142524771367862100726233)
            ·
              refine ⟨420856893578525896575544675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 561142524771367862100726233 420856893578525896575544675)
              ·
                refine ⟨631285340367788844863317013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420856893578525896575544675 631285340367788844863317013)
                ·
                  refine ⟨29591500329740102102967985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 631285340367788844863317013 29591500329740102102967985)
                  ·
                    refine ⟨22193625247305076577225989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29591500329740102102967985 22193625247305076577225989)
                    ·
                      refine ⟨4161304733869701858229873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22193625247305076577225989 4161304733869701858229873)
                      ·
                        rfl

theorem cell23_8104112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 4].length) (baseStart_8104112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104112 prefixEnd_8104112 := by exact prefixLift 8104112
  have htrace : WordTrace (prefixWord ++ tailWord_8104112) baseStart_8104112 baseEnd_8104112 := by
    simpa [prefixWord, tailWord_8104112, baseEnd_8104112] using wordTrace_append hprefix tailTrace_8104112
  have hstable : (prefixWord ++ tailWord_8104112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104112).length < 2 ^ (prefixWord ++ tailWord_8104112).sum := by decide
  have hdescent : baseEnd_8104112 < baseStart_8104112 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104133 : List Nat := [1, 3, 1, 1, 1, 1, 7, 2, 2, 2, 2]
def baseStart_8104133 : Nat := 118140960795 + 8104133 * 2 ^ 59
def prefixEnd_8104133 : Nat := 4983230072969 + 3 ^ 40 * 8104133 * 2
def baseEnd_8104133 : Nat := 4161315516963446276067277

theorem tailTrace_8104133 : CollatzResearch.WordTrace tailWord_8104133 prefixEnd_8104133 4161315516963446276067277 := by
  unfold tailWord_8104133
  simp only [CollatzResearch.WordTrace]
  refine ⟨295582013549117691569613053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197054675699411794379742035 295582013549117691569613053)
  ·
    refine ⟨110843255080919134338604895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295582013549117691569613053 110843255080919134338604895)
    ·
      refine ⟨166264882621378701507907343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110843255080919134338604895 166264882621378701507907343)
      ·
        refine ⟨249397323932068052261861015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166264882621378701507907343 249397323932068052261861015)
        ·
          refine ⟨374095985898102078392791523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249397323932068052261861015 374095985898102078392791523)
          ·
            refine ⟨561143978847153117589187285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374095985898102078392791523 561143978847153117589187285)
            ·
              refine ⟨13151812004230151193496577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 561143978847153117589187285 13151812004230151193496577)
              ·
                refine ⟨9863859003172613395122433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13151812004230151193496577 9863859003172613395122433)
                ·
                  refine ⟨7397894252379460046341825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9863859003172613395122433 7397894252379460046341825)
                  ·
                    refine ⟨5548420689284595034756369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7397894252379460046341825 5548420689284595034756369)
                    ·
                      refine ⟨4161315516963446276067277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5548420689284595034756369 4161315516963446276067277)
                      ·
                        rfl

theorem cell23_8104133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2, 2, 2, 2].length) (baseStart_8104133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104133 prefixEnd_8104133 := by exact prefixLift 8104133
  have htrace : WordTrace (prefixWord ++ tailWord_8104133) baseStart_8104133 baseEnd_8104133 := by
    simpa [prefixWord, tailWord_8104133, baseEnd_8104133] using wordTrace_append hprefix tailTrace_8104133
  have hstable : (prefixWord ++ tailWord_8104133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104133).length < 2 ^ (prefixWord ++ tailWord_8104133).sum := by decide
  have hdescent : baseEnd_8104133 < baseStart_8104133 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104139 : List Nat := [1, 1, 1, 1, 3, 2, 3, 6, 5]
def baseStart_8104139 : Nat := 118140960795 + 8104139 * 2 ^ 59
def prefixEnd_8104139 : Nat := 4983230072969 + 3 ^ 40 * 8104139 * 2
def baseEnd_8104139 : Nat := 462368733094152583621361

theorem tailTrace_8104139 : CollatzResearch.WordTrace tailWord_8104139 prefixEnd_8104139 462368733094152583621361 := by
  unfold tailWord_8104139
  simp only [CollatzResearch.WordTrace]
  refine ⟨295582232387095954594331471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197054821591397303062887647 295582232387095954594331471)
  ·
    refine ⟨443373348580643931891497207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295582232387095954594331471 443373348580643931891497207)
    ·
      refine ⟨665060022870965897837245811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443373348580643931891497207 665060022870965897837245811)
      ·
        refine ⟨997590034306448846755868717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665060022870965897837245811 997590034306448846755868717)
        ·
          refine ⟨374096262864918317533450769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 997590034306448846755868717 374096262864918317533450769)
          ·
            refine ⟨280572197148688738150088077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374096262864918317533450769 280572197148688738150088077)
            ·
              refine ⟨105214573930758276806283029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280572197148688738150088077 105214573930758276806283029)
              ·
                refine ⟨4931933153004294225294517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105214573930758276806283029 4931933153004294225294517)
                ·
                  refine ⟨462368733094152583621361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4931933153004294225294517 462368733094152583621361)
                  ·
                    rfl

theorem cell23_8104139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 6, 5].length) (baseStart_8104139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104139 prefixEnd_8104139 := by exact prefixLift 8104139
  have htrace : WordTrace (prefixWord ++ tailWord_8104139) baseStart_8104139 baseEnd_8104139 := by
    simpa [prefixWord, tailWord_8104139, baseEnd_8104139] using wordTrace_append hprefix tailTrace_8104139
  have hstable : (prefixWord ++ tailWord_8104139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104139).length < 2 ^ (prefixWord ++ tailWord_8104139).sum := by decide
  have hdescent : baseEnd_8104139 < baseStart_8104139 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104150 : List Nat := [5, 2, 1, 2, 1, 1, 3, 1, 1, 4, 2]
def baseStart_8104150 : Nat := 118140960795 + 8104150 * 2 ^ 59
def prefixEnd_8104150 : Nat := 4983230072969 + 3 ^ 40 * 8104150 * 2
def baseEnd_8104150 : Nat := 4161324246134572709554699

theorem tailTrace_8104150 : CollatzResearch.WordTrace tailWord_8104150 prefixEnd_8104150 4161324246134572709554699 := by
  unfold tailWord_8104150
  simp only [CollatzResearch.WordTrace]
  refine ⟨18473914599378506467061369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197055089060037402315321269 18473914599378506467061369)
  ·
    refine ⟨13855435949533879850296027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18473914599378506467061369 13855435949533879850296027)
    ·
      refine ⟨20783153924300819775444041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13855435949533879850296027 20783153924300819775444041)
      ·
        refine ⟨15587365443225614831583031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20783153924300819775444041 15587365443225614831583031)
        ·
          refine ⟨23381048164838422247374547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15587365443225614831583031 23381048164838422247374547)
          ·
            refine ⟨35071572247257633371061821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23381048164838422247374547 35071572247257633371061821)
            ·
              refine ⟨13151839592721612514148183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35071572247257633371061821 13151839592721612514148183)
              ·
                refine ⟨19727759389082418771222275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13151839592721612514148183 19727759389082418771222275)
                ·
                  refine ⟨29591639083623628156833413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19727759389082418771222275 29591639083623628156833413)
                  ·
                    refine ⟨5548432328179430279406265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29591639083623628156833413 5548432328179430279406265)
                    ·
                      refine ⟨4161324246134572709554699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5548432328179430279406265 4161324246134572709554699)
                      ·
                        rfl

theorem cell23_8104150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_8104150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104150 prefixEnd_8104150 := by exact prefixLift 8104150
  have htrace : WordTrace (prefixWord ++ tailWord_8104150) baseStart_8104150 baseEnd_8104150 := by
    simpa [prefixWord, tailWord_8104150, baseEnd_8104150] using wordTrace_append hprefix tailTrace_8104150
  have hstable : (prefixWord ++ tailWord_8104150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104150).length < 2 ^ (prefixWord ++ tailWord_8104150).sum := by decide
  have hdescent : baseEnd_8104150 < baseStart_8104150 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104196 : List Nat := [2, 3, 2, 2, 3, 1, 1, 1, 1, 2, 5]
def baseStart_8104196 : Nat := 118140960795 + 8104196 * 2 ^ 59
def prefixEnd_8104196 : Nat := 4983230072969 + 3 ^ 40 * 8104196 * 2
def baseEnd_8104196 : Nat := 4161347866244679529579487

theorem tailTrace_8104196 : CollatzResearch.WordTrace tailWord_8104196 prefixEnd_8104196 4161347866244679529579487 := by
  unfold tailWord_8104196
  simp only [CollatzResearch.WordTrace]
  refine ⟨147792155673944726664578221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197056207565259635552770961 147792155673944726664578221)
  ·
    refine ⟨55422058377729272499216833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147792155673944726664578221 55422058377729272499216833)
    ·
      refine ⟨41566543783296954374412625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55422058377729272499216833 41566543783296954374412625)
      ·
        refine ⟨31174907837472715780809469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41566543783296954374412625 31174907837472715780809469)
        ·
          refine ⟨11690590439052268417803551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31174907837472715780809469 11690590439052268417803551)
          ·
            refine ⟨17535885658578402626705327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11690590439052268417803551 17535885658578402626705327)
            ·
              refine ⟨26303828487867603940057991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17535885658578402626705327 26303828487867603940057991)
              ·
                refine ⟨39455742731801405910086987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26303828487867603940057991 39455742731801405910086987)
                ·
                  refine ⟨59183614097702108865130481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39455742731801405910086987 59183614097702108865130481)
                  ·
                    refine ⟨44387710573276581648847861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59183614097702108865130481 44387710573276581648847861)
                    ·
                      refine ⟨4161347866244679529579487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44387710573276581648847861 4161347866244679529579487)
                      ·
                        rfl

theorem cell23_8104196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_8104196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104196 prefixEnd_8104196 := by exact prefixLift 8104196
  have htrace : WordTrace (prefixWord ++ tailWord_8104196) baseStart_8104196 baseEnd_8104196 := by
    simpa [prefixWord, tailWord_8104196, baseEnd_8104196] using wordTrace_append hprefix tailTrace_8104196
  have hstable : (prefixWord ++ tailWord_8104196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104196).length < 2 ^ (prefixWord ++ tailWord_8104196).sum := by decide
  have hdescent : baseEnd_8104196 < baseStart_8104196 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104206 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2]
def baseStart_8104206 : Nat := 118140960795 + 8104206 * 2 ^ 59
def prefixEnd_8104206 : Nat := 4983230072969 + 3 ^ 40 * 8104206 * 2
def baseEnd_8104206 : Nat := 4161353001051224490454441

theorem tailTrace_8104206 : CollatzResearch.WordTrace tailWord_8104206 prefixEnd_8104206 4161353001051224490454441 := by
  unfold tailWord_8104206
  simp only [CollatzResearch.WordTrace]
  refine ⟨36948084509731653129627559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197056450718568816691346981 36948084509731653129627559)
  ·
    refine ⟨55422126764597479694441339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36948084509731653129627559 55422126764597479694441339)
    ·
      refine ⟨83133190146896219541662009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55422126764597479694441339 83133190146896219541662009)
      ·
        refine ⟨62349892610172164656246507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83133190146896219541662009 62349892610172164656246507)
        ·
          refine ⟨93524838915258246984369761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62349892610172164656246507 93524838915258246984369761)
          ·
            refine ⟨70143629186443685238277321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93524838915258246984369761 70143629186443685238277321)
            ·
              refine ⟨52607721889832763928707991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70143629186443685238277321 52607721889832763928707991)
              ·
                refine ⟨78911582834749145893061987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52607721889832763928707991 78911582834749145893061987)
                ·
                  refine ⟨118367374252123718839592981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78911582834749145893061987 118367374252123718839592981)
                  ·
                    refine ⟨5548470668068299320605921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118367374252123718839592981 5548470668068299320605921)
                    ·
                      refine ⟨4161353001051224490454441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5548470668068299320605921 4161353001051224490454441)
                      ·
                        rfl

theorem cell23_8104206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_8104206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104206 prefixEnd_8104206 := by exact prefixLift 8104206
  have htrace : WordTrace (prefixWord ++ tailWord_8104206) baseStart_8104206 baseEnd_8104206 := by
    simpa [prefixWord, tailWord_8104206, baseEnd_8104206] using wordTrace_append hprefix tailTrace_8104206
  have hstable : (prefixWord ++ tailWord_8104206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104206).length < 2 ^ (prefixWord ++ tailWord_8104206).sum := by decide
  have hdescent : baseEnd_8104206 < baseStart_8104206 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104250 : List Nat := [3, 1, 1, 1, 4, 2, 4, 2, 1, 4]
def baseStart_8104250 : Nat := 118140960795 + 8104250 * 2 ^ 59
def prefixEnd_8104250 : Nat := 4983230072969 + 3 ^ 40 * 8104250 * 2
def baseEnd_8104250 : Nat := 1387125198066674106101413

theorem tailTrace_8104250 : CollatzResearch.WordTrace tailWord_8104250 prefixEnd_8104250 1387125198066674106101413 := by
  unfold tailWord_8104250
  simp only [CollatzResearch.WordTrace]
  refine ⟨73896570222423455137905551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197057520593129213701081469 73896570222423455137905551)
  ·
    refine ⟨110844855333635182706858327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73896570222423455137905551 110844855333635182706858327)
    ·
      refine ⟨166267283000452774060287491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110844855333635182706858327 166267283000452774060287491)
      ·
        refine ⟨249400924500679161090431237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166267283000452774060287491 249400924500679161090431237)
        ·
          refine ⟨46762673343877342704455857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249400924500679161090431237 46762673343877342704455857)
          ·
            refine ⟨35072005007908007028341893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46762673343877342704455857 35072005007908007028341893)
            ·
              refine ⟨6576000938982751317814105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35072005007908007028341893 6576000938982751317814105)
              ·
                refine ⟨4932000704237063488360579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6576000938982751317814105 4932000704237063488360579)
                ·
                  refine ⟨7398001056355595232540869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4932000704237063488360579 7398001056355595232540869)
                  ·
                    refine ⟨1387125198066674106101413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7398001056355595232540869 1387125198066674106101413)
                    ·
                      rfl

theorem cell23_8104250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 2, 1, 4].length) (baseStart_8104250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104250 prefixEnd_8104250 := by exact prefixLift 8104250
  have htrace : WordTrace (prefixWord ++ tailWord_8104250) baseStart_8104250 baseEnd_8104250 := by
    simpa [prefixWord, tailWord_8104250, baseEnd_8104250] using wordTrace_append hprefix tailTrace_8104250
  have hstable : (prefixWord ++ tailWord_8104250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104250).length < 2 ^ (prefixWord ++ tailWord_8104250).sum := by decide
  have hdescent : baseEnd_8104250 < baseStart_8104250 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104259 : List Nat := [1, 1, 1, 3, 1, 3, 3, 2, 3, 5]
def baseStart_8104259 : Nat := 118140960795 + 8104259 * 2 ^ 59
def prefixEnd_8104259 : Nat := 4983230072969 + 3 ^ 40 * 8104259 * 2
def baseEnd_8104259 : Nat := 1387126738508637594363899

theorem tailTrace_8104259 : CollatzResearch.WordTrace tailWord_8104259 prefixEnd_8104259 1387126738508637594363899 := by
  unfold tailWord_8104259
  simp only [CollatzResearch.WordTrace]
  refine ⟨295586609146661215088699831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197057739431107476725799887 295586609146661215088699831)
  ·
    refine ⟨443379913719991822633049747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295586609146661215088699831 443379913719991822633049747)
    ·
      refine ⟨665069870579987733949574621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443379913719991822633049747 665069870579987733949574621)
      ·
        refine ⟨249401201467495400231090483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 665069870579987733949574621 249401201467495400231090483)
        ·
          refine ⟨374101802201243100346635725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249401201467495400231090483 374101802201243100346635725)
          ·
            refine ⟨140288175825466162629988397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374101802201243100346635725 140288175825466162629988397)
            ·
              refine ⟨52608065934549810986245649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140288175825466162629988397 52608065934549810986245649)
              ·
                refine ⟨39456049450912358239684237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52608065934549810986245649 39456049450912358239684237)
                ·
                  refine ⟨14796018544092134339881589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39456049450912358239684237 14796018544092134339881589)
                  ·
                    refine ⟨1387126738508637594363899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14796018544092134339881589 1387126738508637594363899)
                    ·
                      rfl

theorem cell23_8104259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 5].length) (baseStart_8104259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104259 prefixEnd_8104259 := by exact prefixLift 8104259
  have htrace : WordTrace (prefixWord ++ tailWord_8104259) baseStart_8104259 baseEnd_8104259 := by
    simpa [prefixWord, tailWord_8104259, baseEnd_8104259] using wordTrace_append hprefix tailTrace_8104259
  have hstable : (prefixWord ++ tailWord_8104259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104259).length < 2 ^ (prefixWord ++ tailWord_8104259).sum := by decide
  have hdescent : baseEnd_8104259 < baseStart_8104259 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104273 : List Nat := [1, 2, 2, 1, 4, 3, 1, 2, 3, 1, 3]
def baseStart_8104273 : Nat := 118140960795 + 8104273 * 2 ^ 59
def prefixEnd_8104273 : Nat := 4983230072969 + 3 ^ 40 * 8104273 * 2
def baseEnd_8104273 : Nat := 4161387404255075728316633

theorem tailTrace_8104273 : CollatzResearch.WordTrace tailWord_8104273 prefixEnd_8104273 4161387404255075728316633 := by
  unfold tailWord_8104273
  simp only [CollatzResearch.WordTrace]
  refine ⟨295587119768610495479709473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197058079845740330319806315 295587119768610495479709473)
  ·
    refine ⟨221690339826457871609782105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295587119768610495479709473 221690339826457871609782105)
    ·
      refine ⟨166267754869843403707336579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221690339826457871609782105 166267754869843403707336579)
      ·
        refine ⟨249401632304765105561004869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166267754869843403707336579 249401632304765105561004869)
        ·
          refine ⟨46762806057143457292688413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249401632304765105561004869 46762806057143457292688413)
          ·
            refine ⟨17536052271428796484758155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46762806057143457292688413 17536052271428796484758155)
            ·
              refine ⟨26304078407143194727137233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17536052271428796484758155 26304078407143194727137233)
              ·
                refine ⟨19728058805357396045352925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26304078407143194727137233 19728058805357396045352925)
                ·
                  refine ⟨7398022052009023517007347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19728058805357396045352925 7398022052009023517007347)
                  ·
                    refine ⟨11097033078013535275511021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7398022052009023517007347 11097033078013535275511021)
                    ·
                      refine ⟨4161387404255075728316633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11097033078013535275511021 4161387404255075728316633)
                      ·
                        rfl

theorem cell23_8104273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 3, 1, 3].length) (baseStart_8104273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104273 prefixEnd_8104273 := by exact prefixLift 8104273
  have htrace : WordTrace (prefixWord ++ tailWord_8104273) baseStart_8104273 baseEnd_8104273 := by
    simpa [prefixWord, tailWord_8104273, baseEnd_8104273] using wordTrace_append hprefix tailTrace_8104273
  have hstable : (prefixWord ++ tailWord_8104273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104273).length < 2 ^ (prefixWord ++ tailWord_8104273).sum := by decide
  have hdescent : baseEnd_8104273 < baseStart_8104273 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104276 : List Nat := [2, 4, 1, 1, 2, 2, 2, 1, 3, 5]
def baseStart_8104276 : Nat := 118140960795 + 8104276 * 2 ^ 59
def prefixEnd_8104276 : Nat := 4983230072969 + 3 ^ 40 * 8104276 * 2
def baseEnd_8104276 : Nat := 1387129648232346405526373

theorem tailTrace_8104276 : CollatzResearch.WordTrace tailWord_8104276 prefixEnd_8104276 1387129648232346405526373 := by
  unfold tailWord_8104276
  simp only [CollatzResearch.WordTrace]
  refine ⟨147793614593799813496034341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197058152791733084661379121 147793614593799813496034341)
  ·
    refine ⟨27711302736337465030506439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147793614593799813496034341 27711302736337465030506439)
    ·
      refine ⟨41566954104506197545759659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27711302736337465030506439 41566954104506197545759659)
      ·
        refine ⟨62350431156759296318639489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41566954104506197545759659 62350431156759296318639489)
        ·
          refine ⟨46762823367569472238979617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62350431156759296318639489 46762823367569472238979617)
          ·
            refine ⟨35072117525677104179234713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46762823367569472238979617 35072117525677104179234713)
            ·
              refine ⟨26304088144257828134426035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35072117525677104179234713 26304088144257828134426035)
              ·
                refine ⟨39456132216386742201639053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26304088144257828134426035 39456132216386742201639053)
                ·
                  refine ⟨14796049581145028325614645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39456132216386742201639053 14796049581145028325614645)
                  ·
                    refine ⟨1387129648232346405526373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14796049581145028325614645 1387129648232346405526373)
                    ·
                      rfl

theorem cell23_8104276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_8104276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104276 prefixEnd_8104276 := by exact prefixLift 8104276
  have htrace : WordTrace (prefixWord ++ tailWord_8104276) baseStart_8104276 baseEnd_8104276 := by
    simpa [prefixWord, tailWord_8104276, baseEnd_8104276] using wordTrace_append hprefix tailTrace_8104276
  have hstable : (prefixWord ++ tailWord_8104276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104276).length < 2 ^ (prefixWord ++ tailWord_8104276).sum := by decide
  have hdescent : baseEnd_8104276 < baseStart_8104276 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104293 : List Nat := [1, 3, 1, 3, 1, 3, 4, 1, 1, 5]
def baseStart_8104293 : Nat := 118140960795 + 8104293 * 2 ^ 59
def prefixEnd_8104293 : Nat := 4983230072969 + 3 ^ 40 * 8104293 * 2
def baseEnd_8104293 : Nat := 1387132557956055216688847

theorem tailTrace_8104293 : CollatzResearch.WordTrace tailWord_8104293 prefixEnd_8104293 1387132557956055216688847 := by
  unfold tailWord_8104293
  simp only [CollatzResearch.WordTrace]
  refine ⟨295587849228538038895437533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197058566152358692596958355 295587849228538038895437533)
  ·
    refine ⟨110845443460701764585789075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295587849228538038895437533 110845443460701764585789075)
    ·
      refine ⟨166268165191052646878683613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110845443460701764585789075 166268165191052646878683613)
      ·
        refine ⟨62350561946644742579506355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166268165191052646878683613 62350561946644742579506355)
        ·
          refine ⟨93525842919967113869259533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62350561946644742579506355 93525842919967113869259533)
          ·
            refine ⟨35072191094987667700972325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93525842919967113869259533 35072191094987667700972325)
            ·
              refine ⟨6576035830310187693932311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35072191094987667700972325 6576035830310187693932311)
              ·
                refine ⟨9864053745465281540898467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6576035830310187693932311 9864053745465281540898467)
                ·
                  refine ⟨14796080618197922311347701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9864053745465281540898467 14796080618197922311347701)
                  ·
                    refine ⟨1387132557956055216688847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14796080618197922311347701 1387132557956055216688847)
                    ·
                      rfl

theorem cell23_8104293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 1, 1, 5].length) (baseStart_8104293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104293 prefixEnd_8104293 := by exact prefixLift 8104293
  have htrace : WordTrace (prefixWord ++ tailWord_8104293) baseStart_8104293 baseEnd_8104293 := by
    simpa [prefixWord, tailWord_8104293, baseEnd_8104293] using wordTrace_append hprefix tailTrace_8104293
  have hstable : (prefixWord ++ tailWord_8104293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104293).length < 2 ^ (prefixWord ++ tailWord_8104293).sum := by decide
  have hdescent : baseEnd_8104293 < baseStart_8104293 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104316 : List Nat := [2, 2, 2, 1, 1, 1, 2, 4, 3, 2, 3]
def baseStart_8104316 : Nat := 118140960795 + 8104316 * 2 ^ 59
def prefixEnd_8104316 : Nat := 4983230072969 + 3 ^ 40 * 8104316 * 2
def baseEnd_8104316 : Nat := 4161409483923219060078935

theorem tailTrace_8104316 : CollatzResearch.WordTrace tailWord_8104316 prefixEnd_8104316 4161409483923219060078935 := by
  unfold tailWord_8104316
  simp only [CollatzResearch.WordTrace]
  refine ⟨147794344053727356911762401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197059125404969809215683201 147794344053727356911762401)
  ·
    refine ⟨110845758040295517683821801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147794344053727356911762401 110845758040295517683821801)
    ·
      refine ⟨83134318530221638262866351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110845758040295517683821801 83134318530221638262866351)
      ·
        refine ⟨124701477795332457394299527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83134318530221638262866351 124701477795332457394299527)
        ·
          refine ⟨187052216692998686091449291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124701477795332457394299527 187052216692998686091449291)
          ·
            refine ⟨280578325039498029137173937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187052216692998686091449291 280578325039498029137173937)
            ·
              refine ⟨210433743779623521852880453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280578325039498029137173937 210433743779623521852880453)
              ·
                refine ⟨39456326958679410347415085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210433743779623521852880453 39456326958679410347415085)
                ·
                  refine ⟨14796122609504778880280657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39456326958679410347415085 14796122609504778880280657)
                  ·
                    refine ⟨11097091957128584160210493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14796122609504778880280657 11097091957128584160210493)
                    ·
                      refine ⟨4161409483923219060078935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11097091957128584160210493 4161409483923219060078935)
                      ·
                        rfl

theorem cell23_8104316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_8104316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104316 prefixEnd_8104316 := by exact prefixLift 8104316
  have htrace : WordTrace (prefixWord ++ tailWord_8104316) baseStart_8104316 baseEnd_8104316 := by
    simpa [prefixWord, tailWord_8104316, baseEnd_8104316] using wordTrace_append hprefix tailTrace_8104316
  have hstable : (prefixWord ++ tailWord_8104316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104316).length < 2 ^ (prefixWord ++ tailWord_8104316).sum := by decide
  have hdescent : baseEnd_8104316 < baseStart_8104316 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104323 : List Nat := [1, 1, 1, 3, 6, 2, 1, 1, 1, 6]
def baseStart_8104323 : Nat := 118140960795 + 8104323 * 2 ^ 59
def prefixEnd_8104323 : Nat := 4983230072969 + 3 ^ 40 * 8104323 * 2
def baseEnd_8104323 : Nat := 1387137692762600177563801

theorem tailTrace_8104323 : CollatzResearch.WordTrace tailWord_8104323 prefixEnd_8104323 1387137692762600177563801 := by
  unfold tailWord_8104323
  simp only [CollatzResearch.WordTrace]
  refine ⟨295588943418429354019029623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197059295612286236012686415 295588943418429354019029623)
  ·
    refine ⟨443383415127644031028544435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295588943418429354019029623 443383415127644031028544435)
    ·
      refine ⟨665075122691466046542816653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443383415127644031028544435 665075122691466046542816653)
      ·
        refine ⟨249403171009299767453556245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 665075122691466046542816653 249403171009299767453556245)
        ·
          refine ⟨11690773641060926599385449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 249403171009299767453556245 11690773641060926599385449)
          ·
            refine ⟨8768080230795694949539087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11690773641060926599385449 8768080230795694949539087)
            ·
              refine ⟨13152120346193542424308631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8768080230795694949539087 13152120346193542424308631)
              ·
                refine ⟨19728180519290313636462947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13152120346193542424308631 19728180519290313636462947)
                ·
                  refine ⟨29592270778935470454694421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19728180519290313636462947 29592270778935470454694421)
                  ·
                    refine ⟨1387137692762600177563801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29592270778935470454694421 1387137692762600177563801)
                    ·
                      rfl

theorem cell23_8104323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 6].length) (baseStart_8104323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104323 prefixEnd_8104323 := by exact prefixLift 8104323
  have htrace : WordTrace (prefixWord ++ tailWord_8104323) baseStart_8104323 baseEnd_8104323 := by
    simpa [prefixWord, tailWord_8104323, baseEnd_8104323] using wordTrace_append hprefix tailTrace_8104323
  have hstable : (prefixWord ++ tailWord_8104323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104323).length < 2 ^ (prefixWord ++ tailWord_8104323).sum := by decide
  have hdescent : baseEnd_8104323 < baseStart_8104323 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104350 : List Nat := [4, 3, 1, 2, 1, 2, 2, 1, 1, 1, 5]
def baseStart_8104350 : Nat := 118140960795 + 8104350 * 2 ^ 59
def prefixEnd_8104350 : Nat := 4983230072969 + 3 ^ 40 * 8104350 * 2
def baseEnd_8104350 : Nat := 4161426942265471927053779

theorem tailTrace_8104350 : CollatzResearch.WordTrace tailWord_8104350 prefixEnd_8104350 4161426942265471927053779 := by
  unfold tailWord_8104350
  simp only [CollatzResearch.WordTrace]
  refine ⟨36948741023666442203782813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197059952126221025086841669 36948741023666442203782813)
  ·
    refine ⟨13855777883874915826418555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36948741023666442203782813 13855777883874915826418555)
    ·
      refine ⟨20783666825812373739627833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13855777883874915826418555 20783666825812373739627833)
      ·
        refine ⟨15587750119359280304720875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20783666825812373739627833 15587750119359280304720875)
        ·
          refine ⟨23381625179038920457081313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15587750119359280304720875 23381625179038920457081313)
          ·
            refine ⟨17536218884279190342810985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23381625179038920457081313 17536218884279190342810985)
            ·
              refine ⟨13152164163209392757108239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17536218884279190342810985 13152164163209392757108239)
              ·
                refine ⟨19728246244814089135662359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13152164163209392757108239 19728246244814089135662359)
                ·
                  refine ⟨29592369367221133703493539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19728246244814089135662359 29592369367221133703493539)
                  ·
                    refine ⟨44388554050831700555240309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29592369367221133703493539 44388554050831700555240309)
                    ·
                      refine ⟨4161426942265471927053779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44388554050831700555240309 4161426942265471927053779)
                      ·
                        rfl

theorem cell23_8104350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_8104350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104350 prefixEnd_8104350 := by exact prefixLift 8104350
  have htrace : WordTrace (prefixWord ++ tailWord_8104350) baseStart_8104350 baseEnd_8104350 := by
    simpa [prefixWord, tailWord_8104350, baseEnd_8104350] using wordTrace_append hprefix tailTrace_8104350
  have hstable : (prefixWord ++ tailWord_8104350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104350).length < 2 ^ (prefixWord ++ tailWord_8104350).sum := by decide
  have hdescent : baseEnd_8104350 < baseStart_8104350 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104353 : List Nat := [1, 2, 3, 5, 1, 2, 9]
def baseStart_8104353 : Nat := 118140960795 + 8104353 * 2 ^ 59
def prefixEnd_8104353 : Nat := 4983230072969 + 3 ^ 40 * 8104353 * 2
def baseEnd_8104353 : Nat := 51375660280338708831065

theorem tailTrace_8104353 : CollatzResearch.WordTrace tailWord_8104353 prefixEnd_8104353 51375660280338708831065 := by
  unfold tailWord_8104353
  simp only [CollatzResearch.WordTrace]
  refine ⟨295590037608320669142621713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197060025072213779428414475 295590037608320669142621713)
  ·
    refine ⟨221692528206240501856966285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295590037608320669142621713 221692528206240501856966285)
    ·
      refine ⟨83134698077340188196362357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221692528206240501856966285 83134698077340188196362357)
      ·
        refine ⟨7793877944750642643408971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83134698077340188196362357 7793877944750642643408971)
        ·
          refine ⟨11690816917125963965113457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7793877944750642643408971 11690816917125963965113457)
          ·
            refine ⟨8768112687844472973835093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11690816917125963965113457 8768112687844472973835093)
            ·
              refine ⟨51375660280338708831065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8768112687844472973835093 51375660280338708831065)
              ·
                rfl

theorem cell23_8104353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 9].length) (baseStart_8104353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104353 prefixEnd_8104353 := by exact prefixLift 8104353
  have htrace : WordTrace (prefixWord ++ tailWord_8104353) baseStart_8104353 baseEnd_8104353 := by
    simpa [prefixWord, tailWord_8104353, baseEnd_8104353] using wordTrace_append hprefix tailTrace_8104353
  have hstable : (prefixWord ++ tailWord_8104353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104353).length < 2 ^ (prefixWord ++ tailWord_8104353).sum := by decide
  have hdescent : baseEnd_8104353 < baseStart_8104353 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104389 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 2, 2, 9]
def baseStart_8104389 : Nat := 118140960795 + 8104389 * 2 ^ 59
def prefixEnd_8104389 : Nat := 4983230072969 + 3 ^ 40 * 8104389 * 2
def baseEnd_8104389 : Nat := 4161446968010997274466099

theorem tailTrace_8104389 : CollatzResearch.WordTrace tailWord_8104389 prefixEnd_8104389 4161446968010997274466099 := by
  unfold tailWord_8104389
  simp only [CollatzResearch.WordTrace]
  refine ⟨295591350636190247290932221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197060900424126831527288147 295591350636190247290932221)
  ·
    refine ⟨110846756488571342734099583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295591350636190247290932221 110846756488571342734099583)
    ·
      refine ⟨166270134732857014101149375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110846756488571342734099583 166270134732857014101149375)
      ·
        refine ⟨249405202099285521151724063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166270134732857014101149375 249405202099285521151724063)
        ·
          refine ⟨374107803148928281727586095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249405202099285521151724063 374107803148928281727586095)
          ·
            refine ⟨561161704723392422591379143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374107803148928281727586095 561161704723392422591379143)
            ·
              refine ⟨841742557085088633887068715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561161704723392422591379143 841742557085088633887068715)
              ·
                refine ⟨1262613835627632950830603073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 841742557085088633887068715 1262613835627632950830603073)
                ·
                  refine ⟨946960376720724713122952305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1262613835627632950830603073 946960376720724713122952305)
                  ·
                    refine ⟨710220282540543534842214229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 946960376720724713122952305 710220282540543534842214229)
                    ·
                      refine ⟨4161446968010997274466099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 710220282540543534842214229 4161446968010997274466099)
                      ·
                        rfl

theorem cell23_8104389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_8104389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104389 prefixEnd_8104389 := by exact prefixLift 8104389
  have htrace : WordTrace (prefixWord ++ tailWord_8104389) baseStart_8104389 baseEnd_8104389 := by
    simpa [prefixWord, tailWord_8104389, baseEnd_8104389] using wordTrace_append hprefix tailTrace_8104389
  have hstable : (prefixWord ++ tailWord_8104389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104389).length < 2 ^ (prefixWord ++ tailWord_8104389).sum := by decide
  have hdescent : baseEnd_8104389 < baseStart_8104389 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104416 : List Nat := [2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 4]
def baseStart_8104416 : Nat := 118140960795 + 8104416 * 2 ^ 59
def prefixEnd_8104416 : Nat := 4983230072969 + 3 ^ 40 * 8104416 * 2
def baseEnd_8104416 : Nat := 4161460831988668668828475

theorem tailTrace_8104416 : CollatzResearch.WordTrace tailWord_8104416 prefixEnd_8104416 4161460831988668668828475 := by
  unfold tailWord_8104416
  simp only [CollatzResearch.WordTrace]
  refine ⟨147796167703546215451082551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197061556938061620601443401 147796167703546215451082551)
  ·
    refine ⟨221694251555319323176623827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147796167703546215451082551 221694251555319323176623827)
    ·
      refine ⟨332541377332978984764935741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221694251555319323176623827 332541377332978984764935741)
      ·
        refine ⟨124703016499867119286850903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332541377332978984764935741 124703016499867119286850903)
        ·
          refine ⟨187054524749800678930276355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124703016499867119286850903 187054524749800678930276355)
          ·
            refine ⟨280581787124701018395414533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187054524749800678930276355 280581787124701018395414533)
            ·
              refine ⟨52609085085881440949140225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 280581787124701018395414533 52609085085881440949140225)
              ·
                refine ⟨39456813814411080711855169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52609085085881440949140225 39456813814411080711855169)
                ·
                  refine ⟨29592610360808310533891377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39456813814411080711855169 29592610360808310533891377)
                  ·
                    refine ⟨22194457770606232900418533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29592610360808310533891377 22194457770606232900418533)
                    ·
                      refine ⟨4161460831988668668828475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22194457770606232900418533 4161460831988668668828475)
                      ·
                        rfl

theorem cell23_8104416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_8104416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104416 prefixEnd_8104416 := by exact prefixLift 8104416
  have htrace : WordTrace (prefixWord ++ tailWord_8104416) baseStart_8104416 baseEnd_8104416 := by
    simpa [prefixWord, tailWord_8104416, baseEnd_8104416] using wordTrace_append hprefix tailTrace_8104416
  have hstable : (prefixWord ++ tailWord_8104416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104416).length < 2 ^ (prefixWord ++ tailWord_8104416).sum := by decide
  have hdescent : baseEnd_8104416 < baseStart_8104416 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104460 : List Nat := [2, 2, 1, 2, 4, 2, 2, 3, 5]
def baseStart_8104460 : Nat := 118140960795 + 8104460 * 2 ^ 59
def prefixEnd_8104460 : Nat := 4983230072969 + 3 ^ 40 * 8104460 * 2
def baseEnd_8104460 : Nat := 462387047237496277408697

theorem tailTrace_8104460 : CollatzResearch.WordTrace tailWord_8104460 prefixEnd_8104460 462387047237496277408697 := by
  unfold tailWord_8104460
  simp only [CollatzResearch.WordTrace]
  refine ⟨147796970109466513208383417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197062626812622017611177889 147796970109466513208383417)
  ·
    refine ⟨110847727582099884906287563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147796970109466513208383417 110847727582099884906287563)
    ·
      refine ⟨166271591373149827359431345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110847727582099884906287563 166271591373149827359431345)
      ·
        refine ⟨124703693529862370519573509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166271591373149827359431345 124703693529862370519573509)
        ·
          refine ⟨23381942536849194472420033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124703693529862370519573509 23381942536849194472420033)
          ·
            refine ⟨17536456902636895854315025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23381942536849194472420033 17536456902636895854315025)
            ·
              refine ⟨13152342676977671890736269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17536456902636895854315025 13152342676977671890736269)
              ·
                refine ⟨4932128503866626959026101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13152342676977671890736269 4932128503866626959026101)
                ·
                  refine ⟨462387047237496277408697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4932128503866626959026101 462387047237496277408697)
                  ·
                    rfl

theorem cell23_8104460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 3, 5].length) (baseStart_8104460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104460 prefixEnd_8104460 := by exact prefixLift 8104460
  have htrace : WordTrace (prefixWord ++ tailWord_8104460) baseStart_8104460 baseEnd_8104460 := by
    simpa [prefixWord, tailWord_8104460, baseEnd_8104460] using wordTrace_append hprefix tailTrace_8104460
  have hstable : (prefixWord ++ tailWord_8104460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104460).length < 2 ^ (prefixWord ++ tailWord_8104460).sum := by decide
  have hdescent : baseEnd_8104460 < baseStart_8104460 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104471 : List Nat := [1, 1, 3, 6, 1, 2, 1, 2, 2, 2, 2]
def baseStart_8104471 : Nat := 118140960795 + 8104471 * 2 ^ 59
def prefixEnd_8104471 : Nat := 4983230072969 + 3 ^ 40 * 8104471 * 2
def baseEnd_8104471 : Nat := 4161489073424665953640723

theorem tailTrace_8104471 : CollatzResearch.WordTrace tailWord_8104471 prefixEnd_8104471 4161489073424665953640723 := by
  unfold tailWord_8104471
  simp only [CollatzResearch.WordTrace]
  refine ⟨295594341421893175295417267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197062894281262116863611511 295594341421893175295417267)
  ·
    refine ⟨443391512132839762943125901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295594341421893175295417267 443391512132839762943125901)
    ·
      refine ⟨166271817049814911103672213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 443391512132839762943125901 166271817049814911103672213)
      ·
        refine ⟨7793991424210073957984635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 166271817049814911103672213 7793991424210073957984635)
        ·
          refine ⟨11690987136315110936976953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7793991424210073957984635 11690987136315110936976953)
          ·
            refine ⟨8768240352236333202732715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11690987136315110936976953 8768240352236333202732715)
            ·
              refine ⟨13152360528354499804099073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8768240352236333202732715 13152360528354499804099073)
              ·
                refine ⟨9864270396265874853074305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13152360528354499804099073 9864270396265874853074305)
                ·
                  refine ⟨7398202797199406139805729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9864270396265874853074305 7398202797199406139805729)
                  ·
                    refine ⟨5548652097899554604854297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7398202797199406139805729 5548652097899554604854297)
                    ·
                      refine ⟨4161489073424665953640723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5548652097899554604854297 4161489073424665953640723)
                      ·
                        rfl

theorem cell23_8104471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_8104471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104471 prefixEnd_8104471 := by exact prefixLift 8104471
  have htrace : WordTrace (prefixWord ++ tailWord_8104471) baseStart_8104471 baseEnd_8104471 := by
    simpa [prefixWord, tailWord_8104471, baseEnd_8104471] using wordTrace_append hprefix tailTrace_8104471
  have hstable : (prefixWord ++ tailWord_8104471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104471).length < 2 ^ (prefixWord ++ tailWord_8104471).sum := by decide
  have hdescent : baseEnd_8104471 < baseStart_8104471 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104503 : List Nat := [1, 1, 3, 1, 2, 3, 1, 4, 3, 4]
def baseStart_8104503 : Nat := 118140960795 + 8104503 * 2 ^ 59
def prefixEnd_8104503 : Nat := 4983230072969 + 3 ^ 40 * 8104503 * 2
def baseEnd_8104503 : Nat := 1387168501601869942813525

theorem tailTrace_8104503 : CollatzResearch.WordTrace tailWord_8104503 prefixEnd_8104503 1387168501601869942813525 := by
  unfold tailWord_8104503
  simp only [CollatzResearch.WordTrace]
  refine ⟨295595508557777244760582163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197063672371851496507054775 295595508557777244760582163)
  ·
    refine ⟨443393262836665867140873245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295595508557777244760582163 443393262836665867140873245)
    ·
      refine ⟨166272473563749700177827467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 443393262836665867140873245 166272473563749700177827467)
      ·
        refine ⟨249408710345624550266741201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166272473563749700177827467 249408710345624550266741201)
        ·
          refine ⟨187056532759218412700055901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249408710345624550266741201 187056532759218412700055901)
          ·
            refine ⟨70146199784706904762520963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187056532759218412700055901 70146199784706904762520963)
            ·
              refine ⟨105219299677060357143781445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70146199784706904762520963 105219299677060357143781445)
              ·
                refine ⟨19728618689448816964459021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105219299677060357143781445 19728618689448816964459021)
                ·
                  refine ⟨7398232008543306361672133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19728618689448816964459021 7398232008543306361672133)
                  ·
                    refine ⟨1387168501601869942813525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7398232008543306361672133 1387168501601869942813525)
                    ·
                      rfl

theorem cell23_8104503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 3, 4].length) (baseStart_8104503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104503 prefixEnd_8104503 := by exact prefixLift 8104503
  have htrace : WordTrace (prefixWord ++ tailWord_8104503) baseStart_8104503 baseEnd_8104503 := by
    simpa [prefixWord, tailWord_8104503, baseEnd_8104503] using wordTrace_append hprefix tailTrace_8104503
  have hstable : (prefixWord ++ tailWord_8104503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104503).length < 2 ^ (prefixWord ++ tailWord_8104503).sum := by decide
  have hdescent : baseEnd_8104503 < baseStart_8104503 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104530 : List Nat := [3, 2, 2, 1, 2, 1, 3, 2, 2, 2, 3]
def baseStart_8104530 : Nat := 118140960795 + 8104530 * 2 ^ 59
def prefixEnd_8104530 : Nat := 4983230072969 + 3 ^ 40 * 8104530 * 2
def baseEnd_8104530 : Nat := 4161519368783281222802951

theorem tailTrace_8104530 : CollatzResearch.WordTrace tailWord_8104530 prefixEnd_8104530 4161519368783281222802951 := by
  unfold tailWord_8104530
  simp only [CollatzResearch.WordTrace]
  refine ⟨73899123332169857092953761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197064328885786285581210029 73899123332169857092953761)
  ·
    refine ⟨55424342499127392819715321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73899123332169857092953761 55424342499127392819715321)
    ·
      refine ⟨41568256874345544614786491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55424342499127392819715321 41568256874345544614786491)
      ·
        refine ⟨62352385311518316922179737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41568256874345544614786491 62352385311518316922179737)
        ·
          refine ⟨46764288983638737691634803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62352385311518316922179737 46764288983638737691634803)
          ·
            refine ⟨70146433475458106537452205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46764288983638737691634803 70146433475458106537452205)
            ·
              refine ⟨26304912553296789951544577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70146433475458106537452205 26304912553296789951544577)
              ·
                refine ⟨19728684414972592463658433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26304912553296789951544577 19728684414972592463658433)
                ·
                  refine ⟨14796513311229444347743825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19728684414972592463658433 14796513311229444347743825)
                  ·
                    refine ⟨11097384983422083260807869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14796513311229444347743825 11097384983422083260807869)
                    ·
                      refine ⟨4161519368783281222802951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11097384983422083260807869 4161519368783281222802951)
                      ·
                        rfl

theorem cell23_8104530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_8104530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104530 prefixEnd_8104530 := by exact prefixLift 8104530
  have htrace : WordTrace (prefixWord ++ tailWord_8104530) baseStart_8104530 baseEnd_8104530 := by
    simpa [prefixWord, tailWord_8104530, baseEnd_8104530] using wordTrace_append hprefix tailTrace_8104530
  have hstable : (prefixWord ++ tailWord_8104530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104530).length < 2 ^ (prefixWord ++ tailWord_8104530).sum := by decide
  have hdescent : baseEnd_8104530 < baseStart_8104530 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104536 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 1, 1, 8]
def baseStart_8104536 : Nat := 118140960795 + 8104536 * 2 ^ 59
def prefixEnd_8104536 : Nat := 4983230072969 + 3 ^ 40 * 8104536 * 2
def baseEnd_8104536 : Nat := 4161522449667208199327923

theorem tailTrace_8104536 : CollatzResearch.WordTrace tailWord_8104536 prefixEnd_8104536 4161522449667208199327923 := by
  unfold tailWord_8104536
  simp only [CollatzResearch.WordTrace]
  refine ⟨147798356083328845698266731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197064474777771794264355641 147798356083328845698266731)
  ·
    refine ⟨221697534124993268547400097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147798356083328845698266731 221697534124993268547400097)
    ·
      refine ⟨166273150593744951410550073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221697534124993268547400097 166273150593744951410550073)
      ·
        refine ⟨124704862945308713557912555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166273150593744951410550073 124704862945308713557912555)
        ·
          refine ⟨187057294417963070336868833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124704862945308713557912555 187057294417963070336868833)
          ·
            refine ⟨140292970813472302752651625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187057294417963070336868833 140292970813472302752651625)
            ·
              refine ⟨105219728110104227064488719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140292970813472302752651625 105219728110104227064488719)
              ·
                refine ⟨157829592165156340596733079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105219728110104227064488719 157829592165156340596733079)
                ·
                  refine ⟨236744388247734510895099619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157829592165156340596733079 236744388247734510895099619)
                  ·
                    refine ⟨355116582371601766342649429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 236744388247734510895099619 355116582371601766342649429)
                    ·
                      refine ⟨4161522449667208199327923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 355116582371601766342649429 4161522449667208199327923)
                      ·
                        rfl

theorem cell23_8104536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_8104536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104536 prefixEnd_8104536 := by exact prefixLift 8104536
  have htrace : WordTrace (prefixWord ++ tailWord_8104536) baseStart_8104536 baseEnd_8104536 := by
    simpa [prefixWord, tailWord_8104536, baseEnd_8104536] using wordTrace_append hprefix tailTrace_8104536
  have hstable : (prefixWord ++ tailWord_8104536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104536).length < 2 ^ (prefixWord ++ tailWord_8104536).sum := by decide
  have hdescent : baseEnd_8104536 < baseStart_8104536 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104563 : List Nat := [1, 1, 1, 2, 2, 1, 1, 8, 1, 5]
def baseStart_8104563 : Nat := 118140960795 + 8104563 * 2 ^ 59
def prefixEnd_8104563 : Nat := 4983230072969 + 3 ^ 40 * 8104563 * 2
def baseEnd_8104563 : Nat := 1387178771214959864563433

theorem tailTrace_8104563 : CollatzResearch.WordTrace tailWord_8104563 prefixEnd_8104563 1387178771214959864563433 := by
  unfold tailWord_8104563
  simp only [CollatzResearch.WordTrace]
  refine ⟨295597696937559875007766343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197065131291706583338510895 295597696937559875007766343)
  ·
    refine ⟨443396545406339812511649515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295597696937559875007766343 443396545406339812511649515)
    ·
      refine ⟨665094818109509718767474273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443396545406339812511649515 665094818109509718767474273)
      ·
        refine ⟨498821113582132289075605705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 665094818109509718767474273 498821113582132289075605705)
        ·
          refine ⟨374115835186599216806704279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498821113582132289075605705 374115835186599216806704279)
          ·
            refine ⟨561173752779898825210056419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374115835186599216806704279 561173752779898825210056419)
            ·
              refine ⟨841760629169848237815084629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561173752779898825210056419 841760629169848237815084629)
              ·
                refine ⟨9864382373084159036895523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 841760629169848237815084629 9864382373084159036895523)
                ·
                  refine ⟨14796573559626238555343285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9864382373084159036895523 14796573559626238555343285)
                  ·
                    refine ⟨1387178771214959864563433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14796573559626238555343285 1387178771214959864563433)
                    ·
                      rfl

theorem cell23_8104563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 8, 1, 5].length) (baseStart_8104563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104563 prefixEnd_8104563 := by exact prefixLift 8104563
  have htrace : WordTrace (prefixWord ++ tailWord_8104563) baseStart_8104563 baseEnd_8104563 := by
    simpa [prefixWord, tailWord_8104563, baseEnd_8104563] using wordTrace_append hprefix tailTrace_8104563
  have hstable : (prefixWord ++ tailWord_8104563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104563).length < 2 ^ (prefixWord ++ tailWord_8104563).sum := by decide
  have hdescent : baseEnd_8104563 < baseStart_8104563 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104593 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 8, 4]
def baseStart_8104593 : Nat := 118140960795 + 8104593 * 2 ^ 59
def prefixEnd_8104593 : Nat := 4983230072969 + 3 ^ 40 * 8104593 * 2
def baseEnd_8104593 : Nat := 1387183906021504825438387

theorem tailTrace_8104593 : CollatzResearch.WordTrace tailWord_8104593 prefixEnd_8104593 1387183906021504825438387 := by
  unfold tailWord_8104593
  simp only [CollatzResearch.WordTrace]
  refine ⟨295598791127451190131358433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197065860751634126754238955 295598791127451190131358433)
  ·
    refine ⟨221699093345588392598518825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295598791127451190131358433 221699093345588392598518825)
    ·
      refine ⟨166274320009191294448889119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221699093345588392598518825 166274320009191294448889119)
      ·
        refine ⟨249411480013786941673333679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166274320009191294448889119 249411480013786941673333679)
        ·
          refine ⟨374117220020680412510000519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249411480013786941673333679 374117220020680412510000519)
          ·
            refine ⟨561175830031020618765000779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374117220020680412510000519 561175830031020618765000779)
            ·
              refine ⟨841763745046530928147501169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561175830031020618765000779 841763745046530928147501169)
              ·
                refine ⟨631322808784898196110625877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 841763745046530928147501169 631322808784898196110625877)
                ·
                  refine ⟨7398314165448025735671397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 631322808784898196110625877 7398314165448025735671397)
                  ·
                    refine ⟨1387183906021504825438387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7398314165448025735671397 1387183906021504825438387)
                    ·
                      rfl

theorem cell23_8104593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 8, 4].length) (baseStart_8104593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104593 prefixEnd_8104593 := by exact prefixLift 8104593
  have htrace : WordTrace (prefixWord ++ tailWord_8104593) baseStart_8104593 baseEnd_8104593 := by
    simpa [prefixWord, tailWord_8104593, baseEnd_8104593] using wordTrace_append hprefix tailTrace_8104593
  have hstable : (prefixWord ++ tailWord_8104593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104593).length < 2 ^ (prefixWord ++ tailWord_8104593).sum := by decide
  have hdescent : baseEnd_8104593 < baseStart_8104593 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104637 : List Nat := [1, 4, 1, 2, 1, 4, 1, 3, 1, 2, 3]
def baseStart_8104637 : Nat := 118140960795 + 8104637 * 2 ^ 59
def prefixEnd_8104637 : Nat := 4983230072969 + 3 ^ 40 * 8104637 * 2
def baseEnd_8104637 : Nat := 4161574311213312304164959

theorem tailTrace_8104637 : CollatzResearch.WordTrace tailWord_8104637 prefixEnd_8104637 4161574311213312304164959 := by
  unfold tailWord_8104637
  simp only [CollatzResearch.WordTrace]
  refine ⟨295600395939291785645960165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197066930626194523763973443 295600395939291785645960165)
  ·
    refine ⟨55425074238617209808617531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295600395939291785645960165 55425074238617209808617531)
    ·
      refine ⟨83137611357925814712926297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55425074238617209808617531 83137611357925814712926297)
      ·
        refine ⟨62353208518444361034694723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83137611357925814712926297 62353208518444361034694723)
        ·
          refine ⟨93529812777666541552042085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62353208518444361034694723 93529812777666541552042085)
          ·
            refine ⟨17536839895812476541007891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93529812777666541552042085 17536839895812476541007891)
            ·
              refine ⟨26305259843718714811511837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17536839895812476541007891 26305259843718714811511837)
              ·
                refine ⟨9864472441394518054316939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26305259843718714811511837 9864472441394518054316939)
                ·
                  refine ⟨14796708662091777081475409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9864472441394518054316939 14796708662091777081475409)
                  ·
                    refine ⟨11097531496568832811106557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14796708662091777081475409 11097531496568832811106557)
                    ·
                      refine ⟨4161574311213312304164959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11097531496568832811106557 4161574311213312304164959)
                      ·
                        rfl

theorem cell23_8104637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_8104637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104637 prefixEnd_8104637 := by exact prefixLift 8104637
  have htrace : WordTrace (prefixWord ++ tailWord_8104637) baseStart_8104637 baseEnd_8104637 := by
    simpa [prefixWord, tailWord_8104637, baseEnd_8104637] using wordTrace_append hprefix tailTrace_8104637
  have hstable : (prefixWord ++ tailWord_8104637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104637).length < 2 ^ (prefixWord ++ tailWord_8104637).sum := by decide
  have hdescent : baseEnd_8104637 < baseStart_8104637 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104644 : List Nat := [2, 3, 3, 1, 1, 4, 1, 2, 2, 4]
def baseStart_8104644 : Nat := 118140960795 + 8104644 * 2 ^ 59
def prefixEnd_8104644 : Nat := 4983230072969 + 3 ^ 40 * 8104644 * 2
def baseEnd_8104644 : Nat := 1387192635192631258925809

theorem tailTrace_8104644 : CollatzResearch.WordTrace tailWord_8104644 prefixEnd_8104644 1387192635192631258925809 := by
  unfold tailWord_8104644
  simp only [CollatzResearch.WordTrace]
  refine ⟨147800325625133212920732493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197067100833510950560976657 147800325625133212920732493)
  ·
    refine ⟨55425122109424954845274685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147800325625133212920732493 55425122109424954845274685)
    ·
      refine ⟨20784420791034358066978007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55425122109424954845274685 20784420791034358066978007)
      ·
        refine ⟨31176631186551537100467011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20784420791034358066978007 31176631186551537100467011)
        ·
          refine ⟨46764946779827305650700517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31176631186551537100467011 46764946779827305650700517)
          ·
            refine ⟨8768427521217619809506347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46764946779827305650700517 8768427521217619809506347)
            ·
              refine ⟨13152641281826429714259521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8768427521217619809506347 13152641281826429714259521)
              ·
                refine ⟨9864480961369822285694641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13152641281826429714259521 9864480961369822285694641)
                ·
                  refine ⟨7398360721027366714270981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9864480961369822285694641 7398360721027366714270981)
                  ·
                    refine ⟨1387192635192631258925809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7398360721027366714270981 1387192635192631258925809)
                    ·
                      rfl

theorem cell23_8104644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_8104644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104644 prefixEnd_8104644 := by exact prefixLift 8104644
  have htrace : WordTrace (prefixWord ++ tailWord_8104644) baseStart_8104644 baseEnd_8104644 := by
    simpa [prefixWord, tailWord_8104644, baseEnd_8104644] using wordTrace_append hprefix tailTrace_8104644
  have hstable : (prefixWord ++ tailWord_8104644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104644).length < 2 ^ (prefixWord ++ tailWord_8104644).sum := by decide
  have hdescent : baseEnd_8104644 < baseStart_8104644 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104661 : List Nat := [1, 3, 2, 5, 1, 1, 3, 1, 2, 4]
def baseStart_8104661 : Nat := 118140960795 + 8104661 * 2 ^ 59
def prefixEnd_8104661 : Nat := 4983230072969 + 3 ^ 40 * 8104661 * 2
def baseEnd_8104661 : Nat := 1387195544916340070088283

theorem tailTrace_8104661 : CollatzResearch.WordTrace tailWord_8104661 prefixEnd_8104661 1387195544916340070088283 := by
  unfold tailWord_8104661
  simp only [CollatzResearch.WordTrace]
  refine ⟨295601271291204837744833837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197067514194136558496555891 295601271291204837744833837)
  ·
    refine ⟨110850476734201814154312689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295601271291204837744833837 110850476734201814154312689)
    ·
      refine ⟨83137857550651360615734517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110850476734201814154312689 83137857550651360615734517)
      ·
        refine ⟨7794174145373565057725111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83137857550651360615734517 7794174145373565057725111)
        ·
          refine ⟨11691261218060347586587667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7794174145373565057725111 11691261218060347586587667)
          ·
            refine ⟨17536891827090521379881501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11691261218060347586587667 17536891827090521379881501)
            ·
              refine ⟨6576334435158945517455563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17536891827090521379881501 6576334435158945517455563)
              ·
                refine ⟨9864501652738418276183345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6576334435158945517455563 9864501652738418276183345)
                ·
                  refine ⟨7398376239553813707137509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9864501652738418276183345 7398376239553813707137509)
                  ·
                    refine ⟨1387195544916340070088283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7398376239553813707137509 1387195544916340070088283)
                    ·
                      rfl

theorem cell23_8104661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_8104661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104661 prefixEnd_8104661 := by exact prefixLift 8104661
  have htrace : WordTrace (prefixWord ++ tailWord_8104661) baseStart_8104661 baseEnd_8104661 := by
    simpa [prefixWord, tailWord_8104661, baseEnd_8104661] using wordTrace_append hprefix tailTrace_8104661
  have hstable : (prefixWord ++ tailWord_8104661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104661).length < 2 ^ (prefixWord ++ tailWord_8104661).sum := by decide
  have hdescent : baseEnd_8104661 < baseStart_8104661 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104694 : List Nat := [5, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2]
def baseStart_8104694 : Nat := 118140960795 + 8104694 * 2 ^ 59
def prefixEnd_8104694 : Nat := 4983230072969 + 3 ^ 40 * 8104694 * 2
def baseEnd_8104694 : Nat := 4161603579610618581152197

theorem tailTrace_8104694 : CollatzResearch.WordTrace tailWord_8104694 prefixEnd_8104694 4161603579610618581152197 := by
  unfold tailWord_8104694
  simp only [CollatzResearch.WordTrace]
  refine ⟨18475154681255330273799071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197068316600056856253856757 18475154681255330273799071)
  ·
    refine ⟨27712732021882995410698607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18475154681255330273799071 27712732021882995410698607)
    ·
      refine ⟨41569098032824493116047911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27712732021882995410698607 41569098032824493116047911)
      ·
        refine ⟨62353647049236739674071867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41569098032824493116047911 62353647049236739674071867)
        ·
          refine ⟨93530470573855109511107801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62353647049236739674071867 93530470573855109511107801)
          ·
            refine ⟨70147852930391332133330851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93530470573855109511107801 70147852930391332133330851)
            ·
              refine ⟨105221779395586998199996277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70147852930391332133330851 105221779395586998199996277)
              ·
                refine ⟨9864541818336281081249651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105221779395586998199996277 9864541818336281081249651)
                ·
                  refine ⟨14796812727504421621874477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9864541818336281081249651 14796812727504421621874477)
                  ·
                    refine ⟨5548804772814158108202929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14796812727504421621874477 5548804772814158108202929)
                    ·
                      refine ⟨4161603579610618581152197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5548804772814158108202929 4161603579610618581152197)
                      ·
                        rfl

theorem cell23_8104694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_8104694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104694 prefixEnd_8104694 := by exact prefixLift 8104694
  have htrace : WordTrace (prefixWord ++ tailWord_8104694) baseStart_8104694 baseEnd_8104694 := by
    simpa [prefixWord, tailWord_8104694, baseEnd_8104694] using wordTrace_append hprefix tailTrace_8104694
  have hstable : (prefixWord ++ tailWord_8104694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104694).length < 2 ^ (prefixWord ++ tailWord_8104694).sum := by decide
  have hdescent : baseEnd_8104694 < baseStart_8104694 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104760 : List Nat := [2, 1, 2, 1, 3, 2, 1, 4, 2, 5]
def baseStart_8104760 : Nat := 118140960795 + 8104760 * 2 ^ 59
def prefixEnd_8104760 : Nat := 4983230072969 + 3 ^ 40 * 8104760 * 2
def baseEnd_8104760 : Nat := 1387212489777938440975631

theorem tailTrace_8104760 : CollatzResearch.WordTrace tailWord_8104760 prefixEnd_8104760 1387212489777938440975631 := by
  unfold tailWord_8104760
  simp only [CollatzResearch.WordTrace]
  refine ⟨147802441058923088826343867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197069921411897451768458489 147802441058923088826343867)
  ·
    refine ⟨221703661588384633239515801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147802441058923088826343867 221703661588384633239515801)
    ·
      refine ⟨166277746191288474929636851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221703661588384633239515801 166277746191288474929636851)
      ·
        refine ⟨249416619286932712394455277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166277746191288474929636851 249416619286932712394455277)
        ·
          refine ⟨93531232232599767147920729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249416619286932712394455277 93531232232599767147920729)
          ·
            refine ⟨70148424174449825360940547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93531232232599767147920729 70148424174449825360940547)
            ·
              refine ⟨105222636261674738041410821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70148424174449825360940547 105222636261674738041410821)
              ·
                refine ⟨19729244299064013382764529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105222636261674738041410821 19729244299064013382764529)
                ·
                  refine ⟨14796933224298010037073397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19729244299064013382764529 14796933224298010037073397)
                  ·
                    refine ⟨1387212489777938440975631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14796933224298010037073397 1387212489777938440975631)
                    ·
                      rfl

theorem cell23_8104760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 2, 5].length) (baseStart_8104760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104760 prefixEnd_8104760 := by exact prefixLift 8104760
  have htrace : WordTrace (prefixWord ++ tailWord_8104760) baseStart_8104760 baseEnd_8104760 := by
    simpa [prefixWord, tailWord_8104760, baseEnd_8104760] using wordTrace_append hprefix tailTrace_8104760
  have hstable : (prefixWord ++ tailWord_8104760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104760).length < 2 ^ (prefixWord ++ tailWord_8104760).sum := by decide
  have hdescent : baseEnd_8104760 < baseStart_8104760 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104767 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 2, 5, 2]
def baseStart_8104767 : Nat := 118140960795 + 8104767 * 2 ^ 59
def prefixEnd_8104767 : Nat := 4983230072969 + 3 ^ 40 * 8104767 * 2
def baseEnd_8104767 : Nat := 4161641063698396795539361

theorem tailTrace_8104767 : CollatzResearch.WordTrace tailWord_8104767 prefixEnd_8104767 4161641063698396795539361 := by
  unfold tailWord_8104767
  simp only [CollatzResearch.WordTrace]
  refine ⟨295605137428820817848192555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197070091619213878565461703 295605137428820817848192555)
  ·
    refine ⟨443407706143231226772288833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295605137428820817848192555 443407706143231226772288833)
    ·
      refine ⟨332555779607423420079216625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443407706143231226772288833 332555779607423420079216625)
      ·
        refine ⟨249416834705567565059412469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332555779607423420079216625 249416834705567565059412469)
        ·
          refine ⟨23382828253646959224319919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 249416834705567565059412469 23382828253646959224319919)
          ·
            refine ⟨35074242380470438836479879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23382828253646959224319919 35074242380470438836479879)
            ·
              refine ⟨52611363570705658254719819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35074242380470438836479879 52611363570705658254719819)
              ·
                refine ⟨78917045356058487382079729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52611363570705658254719819 78917045356058487382079729)
                ·
                  refine ⟨59187784017043865536559797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78917045356058487382079729 59187784017043865536559797)
                  ·
                    refine ⟨5548854751597862394052481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59187784017043865536559797 5548854751597862394052481)
                    ·
                      refine ⟨4161641063698396795539361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5548854751597862394052481 4161641063698396795539361)
                      ·
                        rfl

theorem cell23_8104767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 5, 2].length) (baseStart_8104767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104767 prefixEnd_8104767 := by exact prefixLift 8104767
  have htrace : WordTrace (prefixWord ++ tailWord_8104767) baseStart_8104767 baseEnd_8104767 := by
    simpa [prefixWord, tailWord_8104767, baseEnd_8104767] using wordTrace_append hprefix tailTrace_8104767
  have hstable : (prefixWord ++ tailWord_8104767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104767).length < 2 ^ (prefixWord ++ tailWord_8104767).sum := by decide
  have hdescent : baseEnd_8104767 < baseStart_8104767 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104858 : List Nat := [3, 1, 1, 4, 3, 2, 1, 3, 1, 4]
def baseStart_8104858 : Nat := 118140960795 + 8104858 * 2 ^ 59
def prefixEnd_8104858 : Nat := 4983230072969 + 3 ^ 40 * 8104858 * 2
def baseEnd_8104858 : Nat := 1387229263479318646500481

theorem tailTrace_8104858 : CollatzResearch.WordTrace tailWord_8104858 prefixEnd_8104858 1387229263479318646500481 := by
  unfold tailWord_8104858
  simp only [CollatzResearch.WordTrace]
  refine ⟨73902114117872785097438807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197072304314327426926503485 73902114117872785097438807)
  ·
    refine ⟨110853171176809177646158211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73902114117872785097438807 110853171176809177646158211)
    ·
      refine ⟨166279756765213766469237317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110853171176809177646158211 166279756765213766469237317)
      ·
        refine ⟨31177454393477581212981997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166279756765213766469237317 31177454393477581212981997)
        ·
          refine ⟨11691545397554092954868249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31177454393477581212981997 11691545397554092954868249)
          ·
            refine ⟨8768659048165569716151187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11691545397554092954868249 8768659048165569716151187)
            ·
              refine ⟨13152988572248354574226781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8768659048165569716151187 13152988572248354574226781)
              ·
                refine ⟨4932370714593132965335043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13152988572248354574226781 4932370714593132965335043)
                ·
                  refine ⟨7398556071889699448002565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4932370714593132965335043 7398556071889699448002565)
                  ·
                    refine ⟨1387229263479318646500481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7398556071889699448002565 1387229263479318646500481)
                    ·
                      rfl

theorem cell23_8104858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 3, 1, 4].length) (baseStart_8104858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104858 prefixEnd_8104858 := by exact prefixLift 8104858
  have htrace : WordTrace (prefixWord ++ tailWord_8104858) baseStart_8104858 baseEnd_8104858 := by
    simpa [prefixWord, tailWord_8104858, baseEnd_8104858] using wordTrace_append hprefix tailTrace_8104858
  have hstable : (prefixWord ++ tailWord_8104858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104858).length < 2 ^ (prefixWord ++ tailWord_8104858).sum := by decide
  have hdescent : baseEnd_8104858 < baseStart_8104858 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104867 : List Nat := [1, 1, 1, 4, 1, 2, 4, 3, 1, 5]
def baseStart_8104867 : Nat := 118140960795 + 8104867 * 2 ^ 59
def prefixEnd_8104867 : Nat := 4983230072969 + 3 ^ 40 * 8104867 * 2
def baseEnd_8104867 : Nat := 1387230803921282134762967

theorem tailTrace_8104867 : CollatzResearch.WordTrace tailWord_8104867 prefixEnd_8104867 1387230803921282134762967 := by
  unfold tailWord_8104867
  simp only [CollatzResearch.WordTrace]
  refine ⟨295608784728458534926832855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197072523152305689951221903 295608784728458534926832855)
  ·
    refine ⟨443413177092687802390249283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295608784728458534926832855 443413177092687802390249283)
    ·
      refine ⟨665119765639031703585373925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443413177092687802390249283 665119765639031703585373925)
      ·
        refine ⟨124709956057318444422257611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 665119765639031703585373925 124709956057318444422257611)
        ·
          refine ⟨187064934085977666633386417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124709956057318444422257611 187064934085977666633386417)
          ·
            refine ⟨140298700564483249975039813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187064934085977666633386417 140298700564483249975039813)
            ·
              refine ⟨26306006355840609370319965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140298700564483249975039813 26306006355840609370319965)
              ·
                refine ⟨9864752383440228513869987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26306006355840609370319965 9864752383440228513869987)
                ·
                  refine ⟨14797128575160342770804981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9864752383440228513869987 14797128575160342770804981)
                  ·
                    refine ⟨1387230803921282134762967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14797128575160342770804981 1387230803921282134762967)
                    ·
                      rfl

theorem cell23_8104867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 5].length) (baseStart_8104867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104867 prefixEnd_8104867 := by exact prefixLift 8104867
  have htrace : WordTrace (prefixWord ++ tailWord_8104867) baseStart_8104867 baseEnd_8104867 := by
    simpa [prefixWord, tailWord_8104867, baseEnd_8104867] using wordTrace_append hprefix tailTrace_8104867
  have hstable : (prefixWord ++ tailWord_8104867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104867).length < 2 ^ (prefixWord ++ tailWord_8104867).sum := by decide
  have hdescent : baseEnd_8104867 < baseStart_8104867 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104902 : List Nat := [6, 1, 3, 1, 1, 1, 2, 1, 2, 2, 3]
def baseStart_8104902 : Nat := 118140960795 + 8104902 * 2 ^ 59
def prefixEnd_8104902 : Nat := 4983230072969 + 3 ^ 40 * 8104902 * 2
def baseEnd_8104902 : Nat := 4161710383586753767351241

theorem tailTrace_8104902 : CollatzResearch.WordTrace tailWord_8104902 prefixEnd_8104902 4161710383586753767351241 := by
  unfold tailWord_8104902
  simp only [CollatzResearch.WordTrace]
  refine ⟨9237814415104116747011155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 197073374188887823936237973 9237814415104116747011155)
  ·
    refine ⟨13856721622656175120516733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9237814415104116747011155 13856721622656175120516733)
    ·
      refine ⟨5196270608496065670193775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13856721622656175120516733 5196270608496065670193775)
      ·
        refine ⟨7794405912744098505290663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5196270608496065670193775 7794405912744098505290663)
        ·
          refine ⟨11691608869116147757935995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7794405912744098505290663 11691608869116147757935995)
          ·
            refine ⟨17537413303674221636903993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11691608869116147757935995 17537413303674221636903993)
            ·
              refine ⟨13153059977755666227677995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17537413303674221636903993 13153059977755666227677995)
              ·
                refine ⟨19729589966633499341516993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13153059977755666227677995 19729589966633499341516993)
                ·
                  refine ⟨14797192474975124506137745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19729589966633499341516993 14797192474975124506137745)
                  ·
                    refine ⟨11097894356231343379603309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14797192474975124506137745 11097894356231343379603309)
                    ·
                      refine ⟨4161710383586753767351241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11097894356231343379603309 4161710383586753767351241)
                      ·
                        rfl

theorem cell23_8104902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_8104902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104902 prefixEnd_8104902 := by exact prefixLift 8104902
  have htrace : WordTrace (prefixWord ++ tailWord_8104902) baseStart_8104902 baseEnd_8104902 := by
    simpa [prefixWord, tailWord_8104902, baseEnd_8104902] using wordTrace_append hprefix tailTrace_8104902
  have hstable : (prefixWord ++ tailWord_8104902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104902).length < 2 ^ (prefixWord ++ tailWord_8104902).sum := by decide
  have hdescent : baseEnd_8104902 < baseStart_8104902 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104904 : List Nat := [2, 1, 3, 1, 5, 1, 1, 1, 3, 1, 4]
def baseStart_8104904 : Nat := 118140960795 + 8104904 * 2 ^ 59
def prefixEnd_8104904 : Nat := 4983230072969 + 3 ^ 40 * 8104904 * 2
def baseEnd_8104904 : Nat := 4161711410548062759526231

theorem tailTrace_8104904 : CollatzResearch.WordTrace tailWord_8104904 prefixEnd_8104904 4161711410548062759526231 := by
  unfold tailWord_8104904
  simp only [CollatzResearch.WordTrace]
  refine ⟨147805067114662245122964883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197073422819549660163953177 147805067114662245122964883)
  ·
    refine ⟨221707600671993367684447325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147805067114662245122964883 221707600671993367684447325)
    ·
      refine ⟨83140350251997512881667747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221707600671993367684447325 83140350251997512881667747)
      ·
        refine ⟨124710525377996269322501621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83140350251997512881667747 124710525377996269322501621)
        ·
          refine ⟨11691611754187150248984527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124710525377996269322501621 11691611754187150248984527)
          ·
            refine ⟨17537417631280725373476791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11691611754187150248984527 17537417631280725373476791)
            ·
              refine ⟨26306126446921088060215187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17537417631280725373476791 26306126446921088060215187)
              ·
                refine ⟨39459189670381632090322781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26306126446921088060215187 39459189670381632090322781)
                ·
                  refine ⟨14797196126393112033871043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39459189670381632090322781 14797196126393112033871043)
                  ·
                    refine ⟨22195794189589668050806565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14797196126393112033871043 22195794189589668050806565)
                    ·
                      refine ⟨4161711410548062759526231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22195794189589668050806565 4161711410548062759526231)
                      ·
                        rfl

theorem cell23_8104904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_8104904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104904 prefixEnd_8104904 := by exact prefixLift 8104904
  have htrace : WordTrace (prefixWord ++ tailWord_8104904) baseStart_8104904 baseEnd_8104904 := by
    simpa [prefixWord, tailWord_8104904, baseEnd_8104904] using wordTrace_append hprefix tailTrace_8104904
  have hstable : (prefixWord ++ tailWord_8104904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104904).length < 2 ^ (prefixWord ++ tailWord_8104904).sum := by decide
  have hdescent : baseEnd_8104904 < baseStart_8104904 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104914 : List Nat := [3, 2, 2, 3, 1, 2, 1, 2, 1, 6]
def baseStart_8104914 : Nat := 118140960795 + 8104914 * 2 ^ 59
def prefixEnd_8104914 : Nat := 4983230072969 + 3 ^ 40 * 8104914 * 2
def baseEnd_8104914 : Nat := 1387238848451535906800395

theorem tailTrace_8104914 : CollatzResearch.WordTrace tailWord_8104914 prefixEnd_8104914 1387238848451535906800395 := by
  unfold tailWord_8104914
  simp only [CollatzResearch.WordTrace]
  refine ⟨73902624739822065488448449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197073665972858841302529197 73902624739822065488448449)
  ·
    refine ⟨55426968554866549116336337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73902624739822065488448449 55426968554866549116336337)
    ·
      refine ⟨41570226416149911837252253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55426968554866549116336337 41570226416149911837252253)
      ·
        refine ⟨15588834906056216938969595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41570226416149911837252253 15588834906056216938969595)
        ·
          refine ⟨23383252359084325408454393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15588834906056216938969595 23383252359084325408454393)
          ·
            refine ⟨17537439269313244056340795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23383252359084325408454393 17537439269313244056340795)
            ·
              refine ⟨26306158903969866084511193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17537439269313244056340795 26306158903969866084511193)
              ·
                refine ⟨19729619177977399563383395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26306158903969866084511193 19729619177977399563383395)
                ·
                  refine ⟨29594428766966099345075093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19729619177977399563383395 29594428766966099345075093)
                  ·
                    refine ⟨1387238848451535906800395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29594428766966099345075093 1387238848451535906800395)
                    ·
                      rfl

theorem cell23_8104914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_8104914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104914 prefixEnd_8104914 := by exact prefixLift 8104914
  have htrace : WordTrace (prefixWord ++ tailWord_8104914) baseStart_8104914 baseEnd_8104914 := by
    simpa [prefixWord, tailWord_8104914, baseEnd_8104914] using wordTrace_append hprefix tailTrace_8104914
  have hstable : (prefixWord ++ tailWord_8104914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104914).length < 2 ^ (prefixWord ++ tailWord_8104914).sum := by decide
  have hdescent : baseEnd_8104914 < baseStart_8104914 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104918 : List Nat := [5, 2, 1, 1, 2, 2, 3, 1, 1, 5]
def baseStart_8104918 : Nat := 118140960795 + 8104918 * 2 ^ 59
def prefixEnd_8104918 : Nat := 4983230072969 + 3 ^ 40 * 8104918 * 2
def baseEnd_8104918 : Nat := 1387239533092408568250389

theorem tailTrace_8104918 : CollatzResearch.WordTrace tailWord_8104918 prefixEnd_8104918 1387239533092408568250389 := by
  unfold tailWord_8104918
  simp only [CollatzResearch.WordTrace]
  refine ⟨18475665303204610664808713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 197073763234182513757959605 18475665303204610664808713)
  ·
    refine ⟨13856748977403457998606535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18475665303204610664808713 13856748977403457998606535)
    ·
      refine ⟨20785123466105186997909803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13856748977403457998606535 20785123466105186997909803)
      ·
        refine ⟨31177685199157780496864705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20785123466105186997909803 31177685199157780496864705)
        ·
          refine ⟨23383263899368335372648529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31177685199157780496864705 23383263899368335372648529)
          ·
            refine ⟨17537447924526251529486397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23383263899368335372648529 17537447924526251529486397)
            ·
              refine ⟨6576542971697344323557399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17537447924526251529486397 6576542971697344323557399)
              ·
                refine ⟨9864814457546016485336099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6576542971697344323557399 9864814457546016485336099)
                ·
                  refine ⟨14797221686319024728004149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9864814457546016485336099 14797221686319024728004149)
                  ·
                    refine ⟨1387239533092408568250389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14797221686319024728004149 1387239533092408568250389)
                    ·
                      rfl

theorem cell23_8104918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_8104918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104918 prefixEnd_8104918 := by exact prefixLift 8104918
  have htrace : WordTrace (prefixWord ++ tailWord_8104918) baseStart_8104918 baseEnd_8104918 := by
    simpa [prefixWord, tailWord_8104918, baseEnd_8104918] using wordTrace_append hprefix tailTrace_8104918
  have hstable : (prefixWord ++ tailWord_8104918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104918).length < 2 ^ (prefixWord ++ tailWord_8104918).sum := by decide
  have hdescent : baseEnd_8104918 < baseStart_8104918 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104921 : List Nat := [1, 2, 1, 2, 5, 2, 3, 1, 1, 1, 4]
def baseStart_8104921 : Nat := 118140960795 + 8104921 * 2 ^ 59
def prefixEnd_8104921 : Nat := 4983230072969 + 3 ^ 40 * 8104921 * 2
def baseEnd_8104921 : Nat := 4161720139719189193013653

theorem tailTrace_8104921 : CollatzResearch.WordTrace tailWord_8104921 prefixEnd_8104921 4161720139719189193013653 := by
  unfold tailWord_8104921
  simp only [CollatzResearch.WordTrace]
  refine ⟨295610754270262902149298617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197073836180175268099532411 295610754270262902149298617)
  ·
    refine ⟨221708065702697176611973963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295610754270262902149298617 221708065702697176611973963)
    ·
      refine ⟨332562098554045764917960945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221708065702697176611973963 332562098554045764917960945)
      ·
        refine ⟨249421573915534323688470709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332562098554045764917960945 249421573915534323688470709)
        ·
          refine ⟨23383272554581342845794129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 249421573915534323688470709 23383272554581342845794129)
          ·
            refine ⟨17537454415936007134345597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23383272554581342845794129 17537454415936007134345597)
            ·
              refine ⟨6576545405976002675379599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17537454415936007134345597 6576545405976002675379599)
              ·
                refine ⟨9864818108964004013069399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6576545405976002675379599 9864818108964004013069399)
                ·
                  refine ⟨14797227163446006019604099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9864818108964004013069399 14797227163446006019604099)
                  ·
                    refine ⟨22195840745169009029406149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14797227163446006019604099 22195840745169009029406149)
                    ·
                      refine ⟨4161720139719189193013653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22195840745169009029406149 4161720139719189193013653)
                      ·
                        rfl

theorem cell23_8104921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 1, 1, 4].length) (baseStart_8104921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104921 prefixEnd_8104921 := by exact prefixLift 8104921
  have htrace : WordTrace (prefixWord ++ tailWord_8104921) baseStart_8104921 baseEnd_8104921 := by
    simpa [prefixWord, tailWord_8104921, baseEnd_8104921] using wordTrace_append hprefix tailTrace_8104921
  have hstable : (prefixWord ++ tailWord_8104921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104921).length < 2 ^ (prefixWord ++ tailWord_8104921).sum := by decide
  have hdescent : baseEnd_8104921 < baseStart_8104921 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104927 : List Nat := [1, 1, 2, 3, 6, 10]
def baseStart_8104927 : Nat := 118140960795 + 8104927 * 2 ^ 59
def prefixEnd_8104927 : Nat := 4983230072969 + 3 ^ 40 * 8104927 * 2
def baseEnd_8104927 : Nat := 17126433006597185882875

theorem tailTrace_8104927 : CollatzResearch.WordTrace tailWord_8104927 prefixEnd_8104927 17126433006597185882875 := by
  unfold tailWord_8104927
  simp only [CollatzResearch.WordTrace]
  refine ⟨295610973108241165174017035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197073982072160776782678023 295610973108241165174017035)
  ·
    refine ⟨443416459662361747761025553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295610973108241165174017035 443416459662361747761025553)
    ·
      refine ⟨332562344746771310820769165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443416459662361747761025553 332562344746771310820769165)
      ·
        refine ⟨124710879280039241557788437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332562344746771310820769165 124710879280039241557788437)
        ·
          refine ⟨5845822466251839448021333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 124710879280039241557788437 5845822466251839448021333)
          ·
            refine ⟨17126433006597185882875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5845822466251839448021333 17126433006597185882875)
            ·
              rfl

theorem cell23_8104927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 10].length) (baseStart_8104927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104927 prefixEnd_8104927 := by exact prefixLift 8104927
  have htrace : WordTrace (prefixWord ++ tailWord_8104927) baseStart_8104927 baseEnd_8104927 := by
    simpa [prefixWord, tailWord_8104927, baseEnd_8104927] using wordTrace_append hprefix tailTrace_8104927
  have hstable : (prefixWord ++ tailWord_8104927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104927).length < 2 ^ (prefixWord ++ tailWord_8104927).sum := by decide
  have hdescent : baseEnd_8104927 < baseStart_8104927 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8104967 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 5]
def baseStart_8104967 : Nat := 118140960795 + 8104967 * 2 ^ 59
def prefixEnd_8104967 : Nat := 4983230072969 + 3 ^ 40 * 8104967 * 2
def baseEnd_8104967 : Nat := 4161743759829296013038441

theorem tailTrace_8104967 : CollatzResearch.WordTrace tailWord_8104967 prefixEnd_8104967 4161743759829296013038441 := by
  unfold tailWord_8104967
  simp only [CollatzResearch.WordTrace]
  refine ⟨295612432028096252005473155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197074954685397501336982103 295612432028096252005473155)
  ·
    refine ⟨443418648042144378008209733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295612432028096252005473155 443418648042144378008209733)
    ·
      refine ⟨83140996507902070876539325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 443418648042144378008209733 83140996507902070876539325)
      ·
        refine ⟨31177873690463276578702247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83140996507902070876539325 31177873690463276578702247)
        ·
          refine ⟨46766810535694914868053371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31177873690463276578702247 46766810535694914868053371)
          ·
            refine ⟨70150215803542372302080057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46766810535694914868053371 70150215803542372302080057)
            ·
              refine ⟨52612661852656779226560043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70150215803542372302080057 52612661852656779226560043)
              ·
                refine ⟨78918992778985168839840065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52612661852656779226560043 78918992778985168839840065)
                ·
                  refine ⟨59189244584238876629880049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78918992778985168839840065 59189244584238876629880049)
                  ·
                    refine ⟨44391933438179157472410037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59189244584238876629880049 44391933438179157472410037)
                    ·
                      refine ⟨4161743759829296013038441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44391933438179157472410037 4161743759829296013038441)
                      ·
                        rfl

theorem cell23_8104967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_8104967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8104967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8104967 prefixEnd_8104967 := by exact prefixLift 8104967
  have htrace : WordTrace (prefixWord ++ tailWord_8104967) baseStart_8104967 baseEnd_8104967 := by
    simpa [prefixWord, tailWord_8104967, baseEnd_8104967] using wordTrace_append hprefix tailTrace_8104967
  have hstable : (prefixWord ++ tailWord_8104967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8104967).length < 2 ^ (prefixWord ++ tailWord_8104967).sum := by decide
  have hdescent : baseEnd_8104967 < baseStart_8104967 := by decide
  rcases family_descends (prefixWord ++ tailWord_8104967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105044 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 4, 3, 3]
def baseStart_8105044 : Nat := 118140960795 + 8105044 * 2 ^ 59
def prefixEnd_8105044 : Nat := 4983230072969 + 3 ^ 40 * 8105044 * 2
def baseEnd_8105044 : Nat := 4161783297839692211775587

theorem tailTrace_8105044 : CollatzResearch.WordTrace tailWord_8105044 prefixEnd_8105044 4161783297839692211775587 := by
  unfold tailWord_8105044
  simp only [CollatzResearch.WordTrace]
  refine ⟨147807620224408647078013093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197076826965878196104017457 147807620224408647078013093)
  ·
    refine ⟨27713928792076621327127455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147807620224408647078013093 27713928792076621327127455)
    ·
      refine ⟨41570893188114931990691183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27713928792076621327127455 41570893188114931990691183)
      ·
        refine ⟨62356339782172397986036775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41570893188114931990691183 62356339782172397986036775)
        ·
          refine ⟨93534509673258596979055163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62356339782172397986036775 93534509673258596979055163)
          ·
            refine ⟨140301764509887895468582745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93534509673258596979055163 140301764509887895468582745)
            ·
              refine ⟨105226323382415921601437059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140301764509887895468582745 105226323382415921601437059)
              ·
                refine ⟨157839485073623882402155589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105226323382415921601437059 157839485073623882402155589)
                ·
                  refine ⟨29594903451304477950404173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157839485073623882402155589 29594903451304477950404173)
                  ·
                    refine ⟨11098088794239179231401565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29594903451304477950404173 11098088794239179231401565)
                    ·
                      refine ⟨4161783297839692211775587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11098088794239179231401565 4161783297839692211775587)
                      ·
                        rfl

theorem cell23_8105044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_8105044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105044 prefixEnd_8105044 := by exact prefixLift 8105044
  have htrace : WordTrace (prefixWord ++ tailWord_8105044) baseStart_8105044 baseEnd_8105044 := by
    simpa [prefixWord, tailWord_8105044, baseEnd_8105044] using wordTrace_append hprefix tailTrace_8105044
  have hstable : (prefixWord ++ tailWord_8105044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105044).length < 2 ^ (prefixWord ++ tailWord_8105044).sum := by decide
  have hdescent : baseEnd_8105044 < baseStart_8105044 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105057 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 1, 1, 7]
def baseStart_8105057 : Nat := 118140960795 + 8105057 * 2 ^ 59
def prefixEnd_8105057 : Nat := 4983230072969 + 3 ^ 40 * 8105057 * 2
def baseEnd_8105057 : Nat := 4161789973088200660913027

theorem tailTrace_8105057 : CollatzResearch.WordTrace tailWord_8105057 prefixEnd_8105057 4161789973088200660913027 := by
  unfold tailWord_8105057
  simp only [CollatzResearch.WordTrace]
  refine ⟨295615714597770197376249425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197077143065180131584166283 295615714597770197376249425)
  ·
    refine ⟨221711785948327648032187069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295615714597770197376249425 221711785948327648032187069)
    ·
      refine ⟨83141919730622868012070151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221711785948327648032187069 83141919730622868012070151)
      ·
        refine ⟨124712879595934302018105227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83141919730622868012070151 124712879595934302018105227)
        ·
          refine ⟨187069319393901453027157841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124712879595934302018105227 187069319393901453027157841)
          ·
            refine ⟨140301989545426089770368381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187069319393901453027157841 140301989545426089770368381)
            ·
              refine ⟨52613246079534783663888143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140301989545426089770368381 52613246079534783663888143)
              ·
                refine ⟨78919869119302175495832215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52613246079534783663888143 78919869119302175495832215)
                ·
                  refine ⟨118379803678953263243748323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78919869119302175495832215 118379803678953263243748323)
                  ·
                    refine ⟨177569705518429894865622485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118379803678953263243748323 177569705518429894865622485)
                    ·
                      refine ⟨4161789973088200660913027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177569705518429894865622485 4161789973088200660913027)
                      ·
                        rfl

theorem cell23_8105057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_8105057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105057 prefixEnd_8105057 := by exact prefixLift 8105057
  have htrace : WordTrace (prefixWord ++ tailWord_8105057) baseStart_8105057 baseEnd_8105057 := by
    simpa [prefixWord, tailWord_8105057, baseEnd_8105057] using wordTrace_append hprefix tailTrace_8105057
  have hstable : (prefixWord ++ tailWord_8105057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105057).length < 2 ^ (prefixWord ++ tailWord_8105057).sum := by decide
  have hdescent : baseEnd_8105057 < baseStart_8105057 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105081 : List Nat := [1, 2, 1, 3, 5, 1, 2, 1, 2, 5]
def baseStart_8105081 : Nat := 118140960795 + 8105081 * 2 ^ 59
def prefixEnd_8105081 : Nat := 4983230072969 + 3 ^ 40 * 8105081 * 2
def baseEnd_8105081 : Nat := 1387267432207969522337639

theorem tailTrace_8105081 : CollatzResearch.WordTrace tailWord_8105081 prefixEnd_8105081 1387267432207969522337639 := by
  unfold tailWord_8105081
  simp only [CollatzResearch.WordTrace]
  refine ⟨295616589949683249475123097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197077726633122166316748731 295616589949683249475123097)
  ·
    refine ⟨221712442462262437106342323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295616589949683249475123097 221712442462262437106342323)
    ·
      refine ⟨332568663693393655659513485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221712442462262437106342323 332568663693393655659513485)
      ·
        refine ⟨124713248885022620872317557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332568663693393655659513485 124713248885022620872317557)
        ·
          refine ⟨11691867082970870706779771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124713248885022620872317557 11691867082970870706779771)
          ·
            refine ⟨17537800624456306060169657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11691867082970870706779771 17537800624456306060169657)
            ·
              refine ⟨13153350468342229545127243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17537800624456306060169657 13153350468342229545127243)
              ·
                refine ⟨19730025702513344317690865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13153350468342229545127243 19730025702513344317690865)
                ·
                  refine ⟨14797519276885008238268149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19730025702513344317690865 14797519276885008238268149)
                  ·
                    refine ⟨1387267432207969522337639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14797519276885008238268149 1387267432207969522337639)
                    ·
                      rfl

theorem cell23_8105081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 5].length) (baseStart_8105081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105081 prefixEnd_8105081 := by exact prefixLift 8105081
  have htrace : WordTrace (prefixWord ++ tailWord_8105081) baseStart_8105081 baseEnd_8105081 := by
    simpa [prefixWord, tailWord_8105081, baseEnd_8105081] using wordTrace_append hprefix tailTrace_8105081
  have hstable : (prefixWord ++ tailWord_8105081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105081).length < 2 ^ (prefixWord ++ tailWord_8105081).sum := by decide
  have hdescent : baseEnd_8105081 < baseStart_8105081 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105104 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 3]
def baseStart_8105104 : Nat := 118140960795 + 8105104 * 2 ^ 59
def prefixEnd_8105104 : Nat := 4983230072969 + 3 ^ 40 * 8105104 * 2
def baseEnd_8105104 : Nat := 4161814106678961977025311

theorem tailTrace_8105104 : CollatzResearch.WordTrace tailWord_8105104 prefixEnd_8105104 4161814106678961977025311 := by
  unfold tailWord_8105104
  simp only [CollatzResearch.WordTrace]
  refine ⟨147808714414299962201605183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197078285885733282935473577 147808714414299962201605183)
  ·
    refine ⟨221713071621449943302407775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147808714414299962201605183 221713071621449943302407775)
    ·
      refine ⟨332569607432174914953611663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221713071621449943302407775 332569607432174914953611663)
      ·
        refine ⟨498854411148262372430417495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332569607432174914953611663 498854411148262372430417495)
        ·
          refine ⟨748281616722393558645626243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498854411148262372430417495 748281616722393558645626243)
          ·
            refine ⟨1122422425083590337968439365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748281616722393558645626243 1122422425083590337968439365)
            ·
              refine ⟨210454204703173188369082381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1122422425083590337968439365 210454204703173188369082381)
              ·
                refine ⟨78920326763689945638405893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210454204703173188369082381 78920326763689945638405893)
                ·
                  refine ⟨14797561268191864807201105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78920326763689945638405893 14797561268191864807201105)
                  ·
                    refine ⟨11098170951143898605400829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14797561268191864807201105 11098170951143898605400829)
                    ·
                      refine ⟨4161814106678961977025311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11098170951143898605400829 4161814106678961977025311)
                      ·
                        rfl

theorem cell23_8105104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 3].length) (baseStart_8105104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105104 prefixEnd_8105104 := by exact prefixLift 8105104
  have htrace : WordTrace (prefixWord ++ tailWord_8105104) baseStart_8105104 baseEnd_8105104 := by
    simpa [prefixWord, tailWord_8105104, baseEnd_8105104] using wordTrace_append hprefix tailTrace_8105104
  have hstable : (prefixWord ++ tailWord_8105104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105104).length < 2 ^ (prefixWord ++ tailWord_8105104).sum := by decide
  have hdescent : baseEnd_8105104 < baseStart_8105104 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105107 : List Nat := [1, 1, 1, 2, 1, 2, 4, 3, 8]
def baseStart_8105107 : Nat := 118140960795 + 8105107 * 2 ^ 59
def prefixEnd_8105107 : Nat := 4983230072969 + 3 ^ 40 * 8105107 * 2
def baseEnd_8105107 : Nat := 462423960791213940587533

theorem tailTrace_8105107 : CollatzResearch.WordTrace tailWord_8105107 prefixEnd_8105107 462423960791213940587533 := by
  unfold tailWord_8105107
  simp only [CollatzResearch.WordTrace]
  refine ⟨295617538247589055915569575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197078358831726037277046383 295617538247589055915569575)
  ·
    refine ⟨443426307371383583873354363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295617538247589055915569575 443426307371383583873354363)
    ·
      refine ⟨665139461057075375810031545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443426307371383583873354363 665139461057075375810031545)
      ·
        refine ⟨498854595792806531857523659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 665139461057075375810031545 498854595792806531857523659)
        ·
          refine ⟨748281893689209797786285489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498854595792806531857523659 748281893689209797786285489)
          ·
            refine ⟨561211420266907348339714117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 748281893689209797786285489 561211420266907348339714117)
            ·
              refine ⟨105227141300045127813696397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 561211420266907348339714117 105227141300045127813696397)
              ·
                refine ⟨39460177987516922930136149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105227141300045127813696397 39460177987516922930136149)
                ·
                  refine ⟨462423960791213940587533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39460177987516922930136149 462423960791213940587533)
                  ·
                    rfl

theorem cell23_8105107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 8].length) (baseStart_8105107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105107 prefixEnd_8105107 := by exact prefixLift 8105107
  have htrace : WordTrace (prefixWord ++ tailWord_8105107) baseStart_8105107 baseEnd_8105107 := by
    simpa [prefixWord, tailWord_8105107, baseEnd_8105107] using wordTrace_append hprefix tailTrace_8105107
  have hstable : (prefixWord ++ tailWord_8105107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105107).length < 2 ^ (prefixWord ++ tailWord_8105107).sum := by decide
  have hdescent : baseEnd_8105107 < baseStart_8105107 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105118 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 1, 6, 2]
def baseStart_8105118 : Nat := 118140960795 + 8105118 * 2 ^ 59
def prefixEnd_8105118 : Nat := 4983230072969 + 3 ^ 40 * 8105118 * 2
def baseEnd_8105118 : Nat := 4161821295408124922250247

theorem tailTrace_8105118 : CollatzResearch.WordTrace tailWord_8105118 prefixEnd_8105118 4161821295408124922250247 := by
  unfold tailWord_8105118
  simp only [CollatzResearch.WordTrace]
  refine ⟨36952242431318650599277501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197078626300366136529480005 36952242431318650599277501)
  ·
    refine ⟨13857090911744493974729063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36952242431318650599277501 13857090911744493974729063)
    ·
      refine ⟨20785636367616740962093595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13857090911744493974729063 20785636367616740962093595)
      ·
        refine ⟨31178454551425111443140393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20785636367616740962093595 31178454551425111443140393)
        ·
          refine ⟨23383840913568833582355295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31178454551425111443140393 23383840913568833582355295)
          ·
            refine ⟨35075761370353250373532943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23383840913568833582355295 35075761370353250373532943)
            ·
              refine ⟨52613642055529875560299415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35075761370353250373532943 52613642055529875560299415)
              ·
                refine ⟨78920463083294813340449123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52613642055529875560299415 78920463083294813340449123)
                ·
                  refine ⟨118380694624942220010673685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78920463083294813340449123 118380694624942220010673685)
                  ·
                    refine ⟨5549095060544166563000329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118380694624942220010673685 5549095060544166563000329)
                    ·
                      refine ⟨4161821295408124922250247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5549095060544166563000329 4161821295408124922250247)
                      ·
                        rfl

theorem cell23_8105118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_8105118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105118 prefixEnd_8105118 := by exact prefixLift 8105118
  have htrace : WordTrace (prefixWord ++ tailWord_8105118) baseStart_8105118 baseEnd_8105118 := by
    simpa [prefixWord, tailWord_8105118, baseEnd_8105118] using wordTrace_append hprefix tailTrace_8105118
  have hstable : (prefixWord ++ tailWord_8105118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105118).length < 2 ^ (prefixWord ++ tailWord_8105118).sum := by decide
  have hdescent : baseEnd_8105118 < baseStart_8105118 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105138 : List Nat := [3, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3]
def baseStart_8105138 : Nat := 118140960795 + 8105138 * 2 ^ 59
def prefixEnd_8105138 : Nat := 4983230072969 + 3 ^ 40 * 8105138 * 2
def baseEnd_8105138 : Nat := 4161831565021214844000155

theorem tailTrace_8105138 : CollatzResearch.WordTrace tailWord_8105138 prefixEnd_8105138 4161831565021214844000155 := by
  unfold tailWord_8105138
  simp only [CollatzResearch.WordTrace]
  refine ⟨73904667227619187052487017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197079112606984498806632045 73904667227619187052487017)
  ·
    refine ⟨55428500420714390289365263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73904667227619187052487017 55428500420714390289365263)
    ·
      refine ⟨83142750631071585434047895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55428500420714390289365263 83142750631071585434047895)
      ·
        refine ⟨124714125946607378151071843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83142750631071585434047895 124714125946607378151071843)
        ·
          refine ⟨187071188919911067226607765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124714125946607378151071843 187071188919911067226607765)
          ·
            refine ⟨8768961980620831276247239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 187071188919911067226607765 8768961980620831276247239)
            ·
              refine ⟨13153442970931246914370859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8768961980620831276247239 13153442970931246914370859)
              ·
                refine ⟨19730164456396870371556289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13153442970931246914370859 19730164456396870371556289)
                ·
                  refine ⟨14797623342297652778667217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19730164456396870371556289 14797623342297652778667217)
                  ·
                    refine ⟨11098217506723239584000413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14797623342297652778667217 11098217506723239584000413)
                    ·
                      refine ⟨4161831565021214844000155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11098217506723239584000413 4161831565021214844000155)
                      ·
                        rfl

theorem cell23_8105138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_8105138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105138 prefixEnd_8105138 := by exact prefixLift 8105138
  have htrace : WordTrace (prefixWord ++ tailWord_8105138) baseStart_8105138 baseEnd_8105138 := by
    simpa [prefixWord, tailWord_8105138, baseEnd_8105138] using wordTrace_append hprefix tailTrace_8105138
  have hstable : (prefixWord ++ tailWord_8105138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105138).length < 2 ^ (prefixWord ++ tailWord_8105138).sum := by decide
  have hdescent : baseEnd_8105138 < baseStart_8105138 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105245 : List Nat := [1, 4, 2, 3, 1, 1, 3, 2, 1, 2, 3]
def baseStart_8105245 : Nat := 118140960795 + 8105245 * 2 ^ 59
def prefixEnd_8105245 : Nat := 4983230072969 + 3 ^ 40 * 8105245 * 2
def baseEnd_8105245 : Nat := 4161886507451245925362163

theorem tailTrace_8105245 : CollatzResearch.WordTrace tailWord_8105245 prefixEnd_8105245 4161886507451245925362163 := by
  unfold tailWord_8105245
  simp only [CollatzResearch.WordTrace]
  refine ⟨295622571521089105484093189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197081714347392736989395459 295622571521089105484093189)
  ·
    refine ⟨55429232160204207278267473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295622571521089105484093189 55429232160204207278267473)
    ·
      refine ⟨41571924120153155458700605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55429232160204207278267473 41571924120153155458700605)
      ·
        refine ⟨15589471545057433297012727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41571924120153155458700605 15589471545057433297012727)
        ·
          refine ⟨23384207317586149945519091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15589471545057433297012727 23384207317586149945519091)
          ·
            refine ⟨35076310976379224918278637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23384207317586149945519091 35076310976379224918278637)
            ·
              refine ⟨13153616616142209344354489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35076310976379224918278637 13153616616142209344354489)
              ·
                refine ⟨9865212462106657008265867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13153616616142209344354489 9865212462106657008265867)
                ·
                  refine ⟨14797818693159985512398801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9865212462106657008265867 14797818693159985512398801)
                  ·
                    refine ⟨11098364019869989134299101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14797818693159985512398801 11098364019869989134299101)
                    ·
                      refine ⟨4161886507451245925362163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11098364019869989134299101 4161886507451245925362163)
                      ·
                        rfl

theorem cell23_8105245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_8105245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105245 prefixEnd_8105245 := by exact prefixLift 8105245
  have htrace : WordTrace (prefixWord ++ tailWord_8105245) baseStart_8105245 baseEnd_8105245 := by
    simpa [prefixWord, tailWord_8105245, baseEnd_8105245] using wordTrace_append hprefix tailTrace_8105245
  have hstable : (prefixWord ++ tailWord_8105245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105245).length < 2 ^ (prefixWord ++ tailWord_8105245).sum := by decide
  have hdescent : baseEnd_8105245 < baseStart_8105245 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105258 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 3, 3, 3]
def baseStart_8105258 : Nat := 118140960795 + 8105258 * 2 ^ 59
def prefixEnd_8105258 : Nat := 4983230072969 + 3 ^ 40 * 8105258 * 2
def baseEnd_8105258 : Nat := 4161893182699754374499603

theorem tailTrace_8105258 : CollatzResearch.WordTrace tailWord_8105258 prefixEnd_8105258 4161893182699754374499603 := by
  unfold tailWord_8105258
  simp only [CollatzResearch.WordTrace]
  refine ⟨73905761417510502176079107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197082030446694672469544285 73905761417510502176079107)
  ·
    refine ⟨110858642126265753264118661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73905761417510502176079107 110858642126265753264118661)
    ·
      refine ⟨20785995398674828737022249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110858642126265753264118661 20785995398674828737022249)
      ·
        refine ⟨15589496549006121552766687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20785995398674828737022249 15589496549006121552766687)
        ·
          refine ⟨23384244823509182329150031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15589496549006121552766687 23384244823509182329150031)
          ·
            refine ⟨35076367235263773493725047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23384244823509182329150031 35076367235263773493725047)
            ·
              refine ⟨52614550852895660240587571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35076367235263773493725047 52614550852895660240587571)
              ·
                refine ⟨78921826279343490360881357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52614550852895660240587571 78921826279343490360881357)
                ·
                  refine ⟨29595684854753808885330509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78921826279343490360881357 29595684854753808885330509)
                  ·
                    refine ⟨11098381820532678331998941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29595684854753808885330509 11098381820532678331998941)
                    ·
                      refine ⟨4161893182699754374499603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11098381820532678331998941 4161893182699754374499603)
                      ·
                        rfl

theorem cell23_8105258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_8105258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105258 prefixEnd_8105258 := by exact prefixLift 8105258
  have htrace : WordTrace (prefixWord ++ tailWord_8105258) baseStart_8105258 baseEnd_8105258 := by
    simpa [prefixWord, tailWord_8105258, baseEnd_8105258] using wordTrace_append hprefix tailTrace_8105258
  have hstable : (prefixWord ++ tailWord_8105258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105258).length < 2 ^ (prefixWord ++ tailWord_8105258).sum := by decide
  have hdescent : baseEnd_8105258 < baseStart_8105258 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105319 : List Nat := [1, 1, 5, 1, 4, 2, 2, 1, 1, 3, 2]
def baseStart_8105319 : Nat := 118140960795 + 8105319 * 2 ^ 59
def prefixEnd_8105319 : Nat := 4983230072969 + 3 ^ 40 * 8105319 * 2
def baseEnd_8105319 : Nat := 4161924505019678635836823

theorem tailTrace_8105319 : CollatzResearch.WordTrace tailWord_8105319 prefixEnd_8105319 4161924505019678635836823 := by
  unfold tailWord_8105319
  simp only [CollatzResearch.WordTrace]
  refine ⟨295625270522821016122287011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197083513681880677414858007 295625270522821016122287011)
  ·
    refine ⟨443437905784231524183430517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295625270522821016122287011 443437905784231524183430517)
    ·
      refine ⟨41572303667271705392196611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 443437905784231524183430517 41572303667271705392196611)
      ·
        refine ⟨62358455500907558088294917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41572303667271705392196611 62358455500907558088294917)
        ·
          refine ⟨11692210406420167141555297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62358455500907558088294917 11692210406420167141555297)
          ·
            refine ⟨8769157804815125356166473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11692210406420167141555297 8769157804815125356166473)
            ·
              refine ⟨6576868353611344017124855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8769157804815125356166473 6576868353611344017124855)
              ·
                refine ⟨9865302530417016025687283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6576868353611344017124855 9865302530417016025687283)
                ·
                  refine ⟨14797953795625524038530925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9865302530417016025687283 14797953795625524038530925)
                  ·
                    refine ⟨5549232673359571514449097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14797953795625524038530925 5549232673359571514449097)
                    ·
                      refine ⟨4161924505019678635836823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5549232673359571514449097 4161924505019678635836823)
                      ·
                        rfl

theorem cell23_8105319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_8105319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105319 prefixEnd_8105319 := by exact prefixLift 8105319
  have htrace : WordTrace (prefixWord ++ tailWord_8105319) baseStart_8105319 baseEnd_8105319 := by
    simpa [prefixWord, tailWord_8105319, baseEnd_8105319] using wordTrace_append hprefix tailTrace_8105319
  have hstable : (prefixWord ++ tailWord_8105319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105319).length < 2 ^ (prefixWord ++ tailWord_8105319).sum := by decide
  have hdescent : baseEnd_8105319 < baseStart_8105319 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105326 : List Nat := [4, 1, 2, 4, 2, 1, 1, 2, 2, 1, 3]
def baseStart_8105326 : Nat := 118140960795 + 8105326 * 2 ^ 59
def prefixEnd_8105326 : Nat := 4983230072969 + 3 ^ 40 * 8105326 * 2
def baseEnd_8105326 : Nat := 4161928099384260108449291

theorem tailTrace_8105326 : CollatzResearch.WordTrace tailWord_8105326 prefixEnd_8105326 4161928099384260108449291 := by
  unfold tailWord_8105326
  simp only [CollatzResearch.WordTrace]
  refine ⟨36953190729224457039723979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197083683889197104211861221 36953190729224457039723979)
  ·
    refine ⟨55429786093836685559585969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36953190729224457039723979 55429786093836685559585969)
    ·
      refine ⟨41572339570377514169689477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55429786093836685559585969 41572339570377514169689477)
      ·
        refine ⟨7794813669445783906816777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41572339570377514169689477 7794813669445783906816777)
        ·
          refine ⟨5846110252084337930112583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7794813669445783906816777 5846110252084337930112583)
          ·
            refine ⟨8769165378126506895168875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5846110252084337930112583 8769165378126506895168875)
            ·
              refine ⟨13153748067189760342753313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8769165378126506895168875 13153748067189760342753313)
              ·
                refine ⟨9865311050392320257064985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13153748067189760342753313 9865311050392320257064985)
                ·
                  refine ⟨7398983287794240192798739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9865311050392320257064985 7398983287794240192798739)
                  ·
                    refine ⟨11098474931691360289198109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7398983287794240192798739 11098474931691360289198109)
                    ·
                      refine ⟨4161928099384260108449291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11098474931691360289198109 4161928099384260108449291)
                      ·
                        rfl

theorem cell23_8105326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_8105326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105326 prefixEnd_8105326 := by exact prefixLift 8105326
  have htrace : WordTrace (prefixWord ++ tailWord_8105326) baseStart_8105326 baseEnd_8105326 := by
    simpa [prefixWord, tailWord_8105326, baseEnd_8105326] using wordTrace_append hprefix tailTrace_8105326
  have hstable : (prefixWord ++ tailWord_8105326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105326).length < 2 ^ (prefixWord ++ tailWord_8105326).sum := by decide
  have hdescent : baseEnd_8105326 < baseStart_8105326 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105348 : List Nat := [2, 3, 2, 1, 1, 3, 2, 1, 2, 3, 3]
def baseStart_8105348 : Nat := 118140960795 + 8105348 * 2 ^ 59
def prefixEnd_8105348 : Nat := 4983230072969 + 3 ^ 40 * 8105348 * 2
def baseEnd_8105348 : Nat := 4161939395958659022374189

theorem tailTrace_8105348 : CollatzResearch.WordTrace tailWord_8105348 prefixEnd_8105348 4161939395958659022374189 := by
  unfold tailWord_8105348
  simp only [CollatzResearch.WordTrace]
  refine ⟨147813164119857977037546349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197084218826477302716728465 147813164119857977037546349)
  ·
    refine ⟨55429936544946741389079881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147813164119857977037546349 55429936544946741389079881)
    ·
      refine ⟨41572452408710056041809911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55429936544946741389079881 41572452408710056041809911)
      ·
        refine ⟨62358678613065084062714867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41572452408710056041809911 62358678613065084062714867)
        ·
          refine ⟨93538017919597626094072301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62358678613065084062714867 93538017919597626094072301)
          ·
            refine ⟨35076756719849109785277113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93538017919597626094072301 35076756719849109785277113)
            ·
              refine ⟨26307567539886832338957835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35076756719849109785277113 26307567539886832338957835)
              ·
                refine ⟨39461351309830248508436753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26307567539886832338957835 39461351309830248508436753)
                ·
                  refine ⟨29596013482372686381327565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39461351309830248508436753 29596013482372686381327565)
                  ·
                    refine ⟨11098505055889757392997837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29596013482372686381327565 11098505055889757392997837)
                    ·
                      refine ⟨4161939395958659022374189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11098505055889757392997837 4161939395958659022374189)
                      ·
                        rfl

theorem cell23_8105348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_8105348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105348 prefixEnd_8105348 := by exact prefixLift 8105348
  have htrace : WordTrace (prefixWord ++ tailWord_8105348) baseStart_8105348 baseEnd_8105348 := by
    simpa [prefixWord, tailWord_8105348, baseEnd_8105348] using wordTrace_append hprefix tailTrace_8105348
  have hstable : (prefixWord ++ tailWord_8105348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105348).length < 2 ^ (prefixWord ++ tailWord_8105348).sum := by decide
  have hdescent : baseEnd_8105348 < baseStart_8105348 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105351 : List Nat := [1, 1, 4, 2, 2, 2, 1, 2, 1, 7]
def baseStart_8105351 : Nat := 118140960795 + 8105351 * 2 ^ 59
def prefixEnd_8105351 : Nat := 4983230072969 + 3 ^ 40 * 8105351 * 2
def baseEnd_8105351 : Nat := 1387313645466874170212225

theorem tailTrace_8105351 : CollatzResearch.WordTrace tailWord_8105351 prefixEnd_8105351 1387313645466874170212225 := by
  unfold tailWord_8105351
  simp only [CollatzResearch.WordTrace]
  refine ⟨295626437658705085587451907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197084291772470057058301271 295626437658705085587451907)
  ·
    refine ⟨443439656488057628381177861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295626437658705085587451907 443439656488057628381177861)
    ·
      refine ⟨83144935591510805321470849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 443439656488057628381177861 83144935591510805321470849)
      ·
        refine ⟨62358701693633103991103137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83144935591510805321470849 62358701693633103991103137)
        ·
          refine ⟨46769026270224827993327353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62358701693633103991103137 46769026270224827993327353)
          ·
            refine ⟨35076769702668620994995515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46769026270224827993327353 35076769702668620994995515)
            ·
              refine ⟨52615154554002931492493273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35076769702668620994995515 52615154554002931492493273)
              ·
                refine ⟨39461365915502198619369955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52615154554002931492493273 39461365915502198619369955)
                ·
                  refine ⟨59192048873253297929054933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39461365915502198619369955 59192048873253297929054933)
                  ·
                    refine ⟨1387313645466874170212225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59192048873253297929054933 1387313645466874170212225)
                    ·
                      rfl

theorem cell23_8105351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_8105351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105351 prefixEnd_8105351 := by exact prefixLift 8105351
  have htrace : WordTrace (prefixWord ++ tailWord_8105351) baseStart_8105351 baseEnd_8105351 := by
    simpa [prefixWord, tailWord_8105351, baseEnd_8105351] using wordTrace_append hprefix tailTrace_8105351
  have hstable : (prefixWord ++ tailWord_8105351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105351).length < 2 ^ (prefixWord ++ tailWord_8105351).sum := by decide
  have hdescent : baseEnd_8105351 < baseStart_8105351 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105388 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 4, 4, 2]
def baseStart_8105388 : Nat := 118140960795 + 8105388 * 2 ^ 59
def prefixEnd_8105388 : Nat := 4983230072969 + 3 ^ 40 * 8105388 * 2
def baseEnd_8105388 : Nat := 4161959935184838865874005

theorem tailTrace_8105388 : CollatzResearch.WordTrace tailWord_8105388 prefixEnd_8105388 4161959935184838865874005 := by
  unfold tailWord_8105388
  simp only [CollatzResearch.WordTrace]
  refine ⟨147813893579785520453274409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197085191439714027271032545 147813893579785520453274409)
  ·
    refine ⟨110860420184839140339955807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147813893579785520453274409 110860420184839140339955807)
    ·
      refine ⟨166290630277258710509933711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110860420184839140339955807 166290630277258710509933711)
      ·
        refine ⟨249435945415888065764900567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166290630277258710509933711 249435945415888065764900567)
        ·
          refine ⟨374153918123832098647350851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249435945415888065764900567 374153918123832098647350851)
          ·
            refine ⟨561230877185748147971026277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374153918123832098647350851 561230877185748147971026277)
            ·
              refine ⟨105230789472327777744567427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 561230877185748147971026277 105230789472327777744567427)
              ·
                refine ⟨157846184208491666616851141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105230789472327777744567427 157846184208491666616851141)
                ·
                  refine ⟨29596159539092187490659589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157846184208491666616851141 29596159539092187490659589)
                  ·
                    refine ⟨5549279913579785154498673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29596159539092187490659589 5549279913579785154498673)
                    ·
                      refine ⟨4161959935184838865874005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5549279913579785154498673 4161959935184838865874005)
                      ·
                        rfl

theorem cell23_8105388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 4, 2].length) (baseStart_8105388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105388 prefixEnd_8105388 := by exact prefixLift 8105388
  have htrace : WordTrace (prefixWord ++ tailWord_8105388) baseStart_8105388 baseEnd_8105388 := by
    simpa [prefixWord, tailWord_8105388, baseEnd_8105388] using wordTrace_append hprefix tailTrace_8105388
  have hstable : (prefixWord ++ tailWord_8105388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105388).length < 2 ^ (prefixWord ++ tailWord_8105388).sum := by decide
  have hdescent : baseEnd_8105388 < baseStart_8105388 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105445 : List Nat := [1, 3, 1, 5, 1, 2, 2, 2, 6]
def baseStart_8105445 : Nat := 118140960795 + 8105445 * 2 ^ 59
def prefixEnd_8105445 : Nat := 4983230072969 + 3 ^ 40 * 8105445 * 2
def baseEnd_8105445 : Nat := 462443244842460571429027

theorem tailTrace_8105445 : CollatzResearch.WordTrace tailWord_8105445 prefixEnd_8105445 462443244842460571429027 := by
  unfold tailWord_8105445
  simp only [CollatzResearch.WordTrace]
  refine ⟨295629866120364539641373789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197086577413576359760915859 295629866120364539641373789)
  ·
    refine ⟨110861199795136702365515171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295629866120364539641373789 110861199795136702365515171)
    ·
      refine ⟨166291799692705053548272757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110861199795136702365515171 166291799692705053548272757)
      ·
        refine ⟨15589856221191098770150571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166291799692705053548272757 15589856221191098770150571)
        ·
          refine ⟨23384784331786648155225857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15589856221191098770150571 23384784331786648155225857)
          ·
            refine ⟨17538588248839986116419393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23384784331786648155225857 17538588248839986116419393)
            ·
              refine ⟨13153941186629989587314545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17538588248839986116419393 13153941186629989587314545)
              ·
                refine ⟨9865455889972492190485909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13153941186629989587314545 9865455889972492190485909)
                ·
                  refine ⟨462443244842460571429027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9865455889972492190485909 462443244842460571429027)
                  ·
                    rfl

theorem cell23_8105445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 6].length) (baseStart_8105445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105445 prefixEnd_8105445 := by exact prefixLift 8105445
  have htrace : WordTrace (prefixWord ++ tailWord_8105445) baseStart_8105445 baseEnd_8105445 := by
    simpa [prefixWord, tailWord_8105445, baseEnd_8105445] using wordTrace_append hprefix tailTrace_8105445
  have hstable : (prefixWord ++ tailWord_8105445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105445).length < 2 ^ (prefixWord ++ tailWord_8105445).sum := by decide
  have hdescent : baseEnd_8105445 < baseStart_8105445 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105482 : List Nat := [3, 1, 2, 2, 2, 2, 3, 1, 2, 3, 2]
def baseStart_8105482 : Nat := 118140960795 + 8105482 * 2 ^ 59
def prefixEnd_8105482 : Nat := 4983230072969 + 3 ^ 40 * 8105482 * 2
def baseEnd_8105482 : Nat := 4162008202366361498098573

theorem tailTrace_8105482 : CollatzResearch.WordTrace tailWord_8105482 prefixEnd_8105482 4162008202366361498098573 := by
  unfold tailWord_8105482
  simp only [CollatzResearch.WordTrace]
  refine ⟨73907803905307623740117675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197087477080820329973647133 73907803905307623740117675)
  ·
    refine ⟨110861705857961435610176513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73907803905307623740117675 110861705857961435610176513)
    ·
      refine ⟨83146279393471076707632385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110861705857961435610176513 83146279393471076707632385)
      ·
        refine ⟨62359709545103307530724289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83146279393471076707632385 62359709545103307530724289)
        ·
          refine ⟨46769782158827480648043217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62359709545103307530724289 46769782158827480648043217)
          ·
            refine ⟨35077336619120610486032413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46769782158827480648043217 35077336619120610486032413)
            ·
              refine ⟨13154001232170228932262155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35077336619120610486032413 13154001232170228932262155)
              ·
                refine ⟨19731001848255343398393233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13154001232170228932262155 19731001848255343398393233)
                ·
                  refine ⟨14798251386191507548794925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19731001848255343398393233 14798251386191507548794925)
                  ·
                    refine ⟨5549344269821815330798097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14798251386191507548794925 5549344269821815330798097)
                    ·
                      refine ⟨4162008202366361498098573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5549344269821815330798097 4162008202366361498098573)
                      ·
                        rfl

theorem cell23_8105482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_8105482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105482 prefixEnd_8105482 := by exact prefixLift 8105482
  have htrace : WordTrace (prefixWord ++ tailWord_8105482) baseStart_8105482 baseEnd_8105482 := by
    simpa [prefixWord, tailWord_8105482, baseEnd_8105482] using wordTrace_append hprefix tailTrace_8105482
  have hstable : (prefixWord ++ tailWord_8105482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105482).length < 2 ^ (prefixWord ++ tailWord_8105482).sum := by decide
  have hdescent : baseEnd_8105482 < baseStart_8105482 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105498 : List Nat := [3, 1, 1, 3, 1, 1, 1, 5, 1, 1, 5]
def baseStart_8105498 : Nat := 118140960795 + 8105498 * 2 ^ 59
def prefixEnd_8105498 : Nat := 4983230072969 + 3 ^ 40 * 8105498 * 2
def baseEnd_8105498 : Nat := 4162016418056833435498499

theorem tailTrace_8105498 : CollatzResearch.WordTrace tailWord_8105498 prefixEnd_8105498 4162016418056833435498499 := by
  unfold tailWord_8105498
  simp only [CollatzResearch.WordTrace]
  refine ⟨73907949797293132423263287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197087866126115019795368765 73907949797293132423263287)
  ·
    refine ⟨110861924695939698634894931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73907949797293132423263287 110861924695939698634894931)
    ·
      refine ⟨166292887043909547952342397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110861924695939698634894931 166292887043909547952342397)
      ·
        refine ⟨62359832641466080482128399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166292887043909547952342397 62359832641466080482128399)
        ·
          refine ⟨93539748962199120723192599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62359832641466080482128399 93539748962199120723192599)
          ·
            refine ⟨140309623443298681084788899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93539748962199120723192599 140309623443298681084788899)
            ·
              refine ⟨210464435164948021627183349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140309623443298681084788899 210464435164948021627183349)
              ·
                refine ⟨19731040796713877027548439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 210464435164948021627183349 19731040796713877027548439)
                ·
                  refine ⟨29596561195070815541322659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19731040796713877027548439 29596561195070815541322659)
                  ·
                    refine ⟨44394841792606223311983989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29596561195070815541322659 44394841792606223311983989)
                    ·
                      refine ⟨4162016418056833435498499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44394841792606223311983989 4162016418056833435498499)
                      ·
                        rfl

theorem cell23_8105498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_8105498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105498 prefixEnd_8105498 := by exact prefixLift 8105498
  have htrace : WordTrace (prefixWord ++ tailWord_8105498) baseStart_8105498 baseEnd_8105498 := by
    simpa [prefixWord, tailWord_8105498, baseEnd_8105498] using wordTrace_append hprefix tailTrace_8105498
  have hstable : (prefixWord ++ tailWord_8105498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105498).length < 2 ^ (prefixWord ++ tailWord_8105498).sum := by decide
  have hdescent : baseEnd_8105498 < baseStart_8105498 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105505 : List Nat := [1, 2, 3, 2, 2, 3, 1, 1, 4, 4]
def baseStart_8105505 : Nat := 118140960795 + 8105505 * 2 ^ 59
def prefixEnd_8105505 : Nat := 4983230072969 + 3 ^ 40 * 8105505 * 2
def baseEnd_8105505 : Nat := 1387340004140471636036989

theorem tailTrace_8105505 : CollatzResearch.WordTrace tailWord_8105505 prefixEnd_8105505 1387340004140471636036989 := by
  unfold tailWord_8105505
  simp only [CollatzResearch.WordTrace]
  refine ⟨295632054500147169888557969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197088036333431446592371979 295632054500147169888557969)
  ·
    refine ⟨221724040875110377416418477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295632054500147169888557969 221724040875110377416418477)
    ·
      refine ⟨83146515328166391531156929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221724040875110377416418477 83146515328166391531156929)
      ·
        refine ⟨62359886496124793648367697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83146515328166391531156929 62359886496124793648367697)
        ·
          refine ⟨46769914872093595236275773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62359886496124793648367697 46769914872093595236275773)
          ·
            refine ⟨17538718077035098213603415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46769914872093595236275773 17538718077035098213603415)
            ·
              refine ⟨26308077115552647320405123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17538718077035098213603415 26308077115552647320405123)
              ·
                refine ⟨39462115673328970980607685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26308077115552647320405123 39462115673328970980607685)
                ·
                  refine ⟨7399146688749182058863941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39462115673328970980607685 7399146688749182058863941)
                  ·
                    refine ⟨1387340004140471636036989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7399146688749182058863941 1387340004140471636036989)
                    ·
                      rfl

theorem cell23_8105505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_8105505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105505 prefixEnd_8105505 := by exact prefixLift 8105505
  have htrace : WordTrace (prefixWord ++ tailWord_8105505) baseStart_8105505 baseEnd_8105505 := by
    simpa [prefixWord, tailWord_8105505, baseEnd_8105505] using wordTrace_append hprefix tailTrace_8105505
  have hstable : (prefixWord ++ tailWord_8105505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105505).length < 2 ^ (prefixWord ++ tailWord_8105505).sum := by decide
  have hdescent : baseEnd_8105505 < baseStart_8105505 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105525 : List Nat := [1, 3, 3, 1, 1, 3, 3, 1, 1, 2, 4]
def baseStart_8105525 : Nat := 118140960795 + 8105525 * 2 ^ 59
def prefixEnd_8105525 : Nat := 4983230072969 + 3 ^ 40 * 8105525 * 2
def baseEnd_8105525 : Nat := 4162030282034504829860875

theorem tailTrace_8105525 : CollatzResearch.WordTrace tailWord_8105525 prefixEnd_8105525 4162030282034504829860875 := by
  unfold tailWord_8105525
  simp only [CollatzResearch.WordTrace]
  refine ⟨295632783960074713304286029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197088522640049808869524019 295632783960074713304286029)
  ·
    refine ⟨110862293985028017489107261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295632783960074713304286029 110862293985028017489107261)
    ·
      refine ⟨41573360244385506558415223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110862293985028017489107261 41573360244385506558415223)
      ·
        refine ⟨62360040366578259837622835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41573360244385506558415223 62360040366578259837622835)
        ·
          refine ⟨93540060549867389756434253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62360040366578259837622835 93540060549867389756434253)
          ·
            refine ⟨35077522706200271158662845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93540060549867389756434253 35077522706200271158662845)
            ·
              refine ⟨13154071014825101684498567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35077522706200271158662845 13154071014825101684498567)
              ·
                refine ⟨19731106522237652526747851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13154071014825101684498567 19731106522237652526747851)
                ·
                  refine ⟨29596659783356478790121777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19731106522237652526747851 29596659783356478790121777)
                  ·
                    refine ⟨22197494837517359092591333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29596659783356478790121777 22197494837517359092591333)
                    ·
                      refine ⟨4162030282034504829860875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22197494837517359092591333 4162030282034504829860875)
                      ·
                        rfl

theorem cell23_8105525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_8105525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105525 prefixEnd_8105525 := by exact prefixLift 8105525
  have htrace : WordTrace (prefixWord ++ tailWord_8105525) baseStart_8105525 baseEnd_8105525 := by
    simpa [prefixWord, tailWord_8105525, baseEnd_8105525] using wordTrace_append hprefix tailTrace_8105525
  have hstable : (prefixWord ++ tailWord_8105525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105525).length < 2 ^ (prefixWord ++ tailWord_8105525).sum := by decide
  have hdescent : baseEnd_8105525 < baseStart_8105525 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105535 : List Nat := [1, 1, 2, 2, 3, 5, 2, 7]
def baseStart_8105535 : Nat := 118140960795 + 8105535 * 2 ^ 59
def prefixEnd_8105535 : Nat := 4983230072969 + 3 ^ 40 * 8105535 * 2
def baseEnd_8105535 : Nat := 154149459883001844101327

theorem tailTrace_8105535 : CollatzResearch.WordTrace tailWord_8105535 prefixEnd_8105535 154149459883001844101327 := by
  unfold tailWord_8105535
  simp only [CollatzResearch.WordTrace]
  refine ⟨295633148690038485012150059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197088765793358990008100039 295633148690038485012150059)
  ·
    refine ⟨443449723035057727518225089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295633148690038485012150059 443449723035057727518225089)
    ·
      refine ⟨332587292276293295638668817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443449723035057727518225089 332587292276293295638668817)
      ·
        refine ⟨249440469207219971729001613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332587292276293295638668817 249440469207219971729001613)
        ·
          refine ⟨93540175952707489398375605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 249440469207219971729001613 93540175952707489398375605)
          ·
            refine ⟨8769391495566327131097713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93540175952707489398375605 8769391495566327131097713)
            ·
              refine ⟨6577043621674745348323285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8769391495566327131097713 6577043621674745348323285)
              ·
                refine ⟨154149459883001844101327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6577043621674745348323285 154149459883001844101327)
                ·
                  rfl

theorem cell23_8105535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 7].length) (baseStart_8105535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105535 prefixEnd_8105535 := by exact prefixLift 8105535
  have htrace : WordTrace (prefixWord ++ tailWord_8105535) baseStart_8105535 baseEnd_8105535 := by
    simpa [prefixWord, tailWord_8105535, baseEnd_8105535] using wordTrace_append hprefix tailTrace_8105535
  have hstable : (prefixWord ++ tailWord_8105535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105535).length < 2 ^ (prefixWord ++ tailWord_8105535).sum := by decide
  have hdescent : baseEnd_8105535 < baseStart_8105535 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105568 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 4]
def baseStart_8105568 : Nat := 118140960795 + 8105568 * 2 ^ 59
def prefixEnd_8105568 : Nat := 4983230072969 + 3 ^ 40 * 8105568 * 2
def baseEnd_8105568 : Nat := 4162052361702648161623177

theorem tailTrace_8105568 : CollatzResearch.WordTrace tailWord_8105568 prefixEnd_8105568 4162052361702648161623177 := by
  unfold tailWord_8105568
  simp only [CollatzResearch.WordTrace]
  refine ⟨147817176149459465824050679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197089568199279287765400905 147817176149459465824050679)
  ·
    refine ⟨221725764224189198736076019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147817176149459465824050679 221725764224189198736076019)
    ·
      refine ⟨332588646336283798104114029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221725764224189198736076019 332588646336283798104114029)
      ·
        refine ⟨124720742376106424289042761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332588646336283798104114029 124720742376106424289042761)
        ·
          refine ⟨93540556782079818216782071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124720742376106424289042761 93540556782079818216782071)
          ·
            refine ⟨140310835173119727325173107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93540556782079818216782071 140310835173119727325173107)
            ·
              refine ⟨210466252759679590987759661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140310835173119727325173107 210466252759679590987759661)
              ·
                refine ⟨78924844784879846620409873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210466252759679590987759661 78924844784879846620409873)
                ·
                  refine ⟨59193633588659884965307405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78924844784879846620409873 59193633588659884965307405)
                  ·
                    refine ⟨22197612595747456861990277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59193633588659884965307405 22197612595747456861990277)
                    ·
                      refine ⟨4162052361702648161623177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22197612595747456861990277 4162052361702648161623177)
                      ·
                        rfl

theorem cell23_8105568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_8105568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105568 prefixEnd_8105568 := by exact prefixLift 8105568
  have htrace : WordTrace (prefixWord ++ tailWord_8105568) baseStart_8105568 baseEnd_8105568 := by
    simpa [prefixWord, tailWord_8105568, baseEnd_8105568] using wordTrace_append hprefix tailTrace_8105568
  have hstable : (prefixWord ++ tailWord_8105568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105568).length < 2 ^ (prefixWord ++ tailWord_8105568).sum := by decide
  have hdescent : baseEnd_8105568 < baseStart_8105568 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105585 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 5, 4, 2]
def baseStart_8105585 : Nat := 118140960795 + 8105585 * 2 ^ 59
def prefixEnd_8105585 : Nat := 4983230072969 + 3 ^ 40 * 8105585 * 2
def baseEnd_8105585 : Nat := 4162061090873774595110599

theorem tailTrace_8105585 : CollatzResearch.WordTrace tailWord_8105585 prefixEnd_8105585 4162061090873774595110599 := by
  unfold tailWord_8105585
  simp only [CollatzResearch.WordTrace]
  refine ⟨295634972339857343551470209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197089981559904895700980139 295634972339857343551470209)
  ·
    refine ⟨221726229254893007663602657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295634972339857343551470209 221726229254893007663602657)
    ·
      refine ⟨166294671941169755747701993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221726229254893007663602657 166294671941169755747701993)
      ·
        refine ⟨124721003955877316810776495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166294671941169755747701993 124721003955877316810776495)
        ·
          refine ⟨187081505933815975216164743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124721003955877316810776495 187081505933815975216164743)
          ·
            refine ⟨280622258900723962824247115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187081505933815975216164743 280622258900723962824247115)
            ·
              refine ⟨420933388351085944236370673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280622258900723962824247115 420933388351085944236370673)
              ·
                refine ⟨315700041263314458177278005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 420933388351085944236370673 315700041263314458177278005)
                ·
                  refine ⟨29596878868435730454119813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 315700041263314458177278005 29596878868435730454119813)
                  ·
                    refine ⟨5549414787831699460147465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29596878868435730454119813 5549414787831699460147465)
                    ·
                      refine ⟨4162061090873774595110599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5549414787831699460147465 4162061090873774595110599)
                      ·
                        rfl

theorem cell23_8105585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 4, 2].length) (baseStart_8105585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105585 prefixEnd_8105585 := by exact prefixLift 8105585
  have htrace : WordTrace (prefixWord ++ tailWord_8105585) baseStart_8105585 baseEnd_8105585 := by
    simpa [prefixWord, tailWord_8105585, baseEnd_8105585] using wordTrace_append hprefix tailTrace_8105585
  have hstable : (prefixWord ++ tailWord_8105585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105585).length < 2 ^ (prefixWord ++ tailWord_8105585).sum := by decide
  have hdescent : baseEnd_8105585 < baseStart_8105585 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105589 : List Nat := [1, 3, 4, 2, 1, 2, 1, 1, 3, 3, 2]
def baseStart_8105589 : Nat := 118140960795 + 8105589 * 2 ^ 59
def prefixEnd_8105589 : Nat := 4983230072969 + 3 ^ 40 * 8105589 * 2
def baseEnd_8105589 : Nat := 4162063144796392579460581

theorem tailTrace_8105589 : CollatzResearch.WordTrace tailWord_8105589 prefixEnd_8105589 4162063144796392579460581 := by
  unfold tailWord_8105589
  simp only [CollatzResearch.WordTrace]
  refine ⟨295635118231842852234615821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197090078821228568156410547 295635118231842852234615821)
  ·
    refine ⟨110863169336941069587980933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295635118231842852234615821 110863169336941069587980933)
    ·
      refine ⟨20786844250676450547746425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110863169336941069587980933 20786844250676450547746425)
      ·
        refine ⟨15590133188007337910809819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20786844250676450547746425 15590133188007337910809819)
        ·
          refine ⟨23385199782011006866214729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15590133188007337910809819 23385199782011006866214729)
          ·
            refine ⟨17538899836508255149661047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23385199782011006866214729 17538899836508255149661047)
            ·
              refine ⟨26308349754762382724491571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17538899836508255149661047 26308349754762382724491571)
              ·
                refine ⟨39462524632143574086737357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26308349754762382724491571 39462524632143574086737357)
                ·
                  refine ⟨14798446737053840282526509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39462524632143574086737357 14798446737053840282526509)
                  ·
                    refine ⟨5549417526395190105947441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14798446737053840282526509 5549417526395190105947441)
                    ·
                      refine ⟨4162063144796392579460581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5549417526395190105947441 4162063144796392579460581)
                      ·
                        rfl

theorem cell23_8105589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_8105589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105589 prefixEnd_8105589 := by exact prefixLift 8105589
  have htrace : WordTrace (prefixWord ++ tailWord_8105589) baseStart_8105589 baseEnd_8105589 := by
    simpa [prefixWord, tailWord_8105589, baseEnd_8105589] using wordTrace_append hprefix tailTrace_8105589
  have hstable : (prefixWord ++ tailWord_8105589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105589).length < 2 ^ (prefixWord ++ tailWord_8105589).sum := by decide
  have hdescent : baseEnd_8105589 < baseStart_8105589 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105635 : List Nat := [1, 1, 1, 4, 1, 1, 5, 1, 2, 3, 3]
def baseStart_8105635 : Nat := 118140960795 + 8105635 * 2 ^ 59
def prefixEnd_8105635 : Nat := 4983230072969 + 3 ^ 40 * 8105635 * 2
def baseEnd_8105635 : Nat := 4162086764906499399485369

theorem tailTrace_8105635 : CollatzResearch.WordTrace tailWord_8105635 prefixEnd_8105635 4162086764906499399485369 := by
  unfold tailWord_8105635
  simp only [CollatzResearch.WordTrace]
  refine ⟨295636795989676202090790359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197091197326450801393860239 295636795989676202090790359)
  ·
    refine ⟨443455193984514303136185539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295636795989676202090790359 443455193984514303136185539)
    ·
      refine ⟨665182790976771454704278309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443455193984514303136185539 665182790976771454704278309)
      ·
        refine ⟨124721773308144647757052183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 665182790976771454704278309 124721773308144647757052183)
        ·
          refine ⟨187082659962216971635578275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124721773308144647757052183 187082659962216971635578275)
          ·
            refine ⟨280623989943325457453367413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187082659962216971635578275 280623989943325457453367413)
            ·
              refine ⟨26308499057186761636253195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 280623989943325457453367413 26308499057186761636253195)
              ·
                refine ⟨39462748585780142454379793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26308499057186761636253195 39462748585780142454379793)
                ·
                  refine ⟨29597061439335106840784845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39462748585780142454379793 29597061439335106840784845)
                  ·
                    refine ⟨11098898039750665065294317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29597061439335106840784845 11098898039750665065294317)
                    ·
                      refine ⟨4162086764906499399485369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11098898039750665065294317 4162086764906499399485369)
                      ·
                        rfl

theorem cell23_8105635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_8105635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105635 prefixEnd_8105635 := by exact prefixLift 8105635
  have htrace : WordTrace (prefixWord ++ tailWord_8105635) baseStart_8105635 baseEnd_8105635 := by
    simpa [prefixWord, tailWord_8105635, baseEnd_8105635] using wordTrace_append hprefix tailTrace_8105635
  have hstable : (prefixWord ++ tailWord_8105635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105635).length < 2 ^ (prefixWord ++ tailWord_8105635).sum := by decide
  have hdescent : baseEnd_8105635 < baseStart_8105635 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105648 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 7]
def baseStart_8105648 : Nat := 118140960795 + 8105648 * 2 ^ 59
def prefixEnd_8105648 : Nat := 4983230072969 + 3 ^ 40 * 8105648 * 2
def baseEnd_8105648 : Nat := 4162093440155007848622809

theorem tailTrace_8105648 : CollatzResearch.WordTrace tailWord_8105648 prefixEnd_8105648 4162093440155007848622809 := by
  unfold tailWord_8105648
  simp only [CollatzResearch.WordTrace]
  refine ⟨147818635069314552655506799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197091513425752736874009065 147818635069314552655506799)
  ·
    refine ⟨221727952603971828983260199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147818635069314552655506799 221727952603971828983260199)
    ·
      refine ⟨332591928905957743474890299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221727952603971828983260199 332591928905957743474890299)
      ·
        refine ⟨498887893358936615212335449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332591928905957743474890299 498887893358936615212335449)
        ·
          refine ⟨374165920019202461409251587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498887893358936615212335449 374165920019202461409251587)
          ·
            refine ⟨561248880028803692113877381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374165920019202461409251587 561248880028803692113877381)
            ·
              refine ⟨105234165005400692271352009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 561248880028803692113877381 105234165005400692271352009)
              ·
                refine ⟨78925623754050519203514007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105234165005400692271352009 78925623754050519203514007)
                ·
                  refine ⟨118388435631075778805271011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78925623754050519203514007 118388435631075778805271011)
                  ·
                    refine ⟨177582653446613668207906517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 118388435631075778805271011 177582653446613668207906517)
                    ·
                      refine ⟨4162093440155007848622809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177582653446613668207906517 4162093440155007848622809)
                      ·
                        rfl

theorem cell23_8105648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 7].length) (baseStart_8105648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105648 prefixEnd_8105648 := by exact prefixLift 8105648
  have htrace : WordTrace (prefixWord ++ tailWord_8105648) baseStart_8105648 baseEnd_8105648 := by
    simpa [prefixWord, tailWord_8105648, baseEnd_8105648] using wordTrace_append hprefix tailTrace_8105648
  have hstable : (prefixWord ++ tailWord_8105648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105648).length < 2 ^ (prefixWord ++ tailWord_8105648).sum := by decide
  have hdescent : baseEnd_8105648 < baseStart_8105648 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105655 : List Nat := [1, 1, 3, 1, 5, 2, 1, 1, 1, 7]
def baseStart_8105655 : Nat := 118140960795 + 8105655 * 2 ^ 59
def prefixEnd_8105655 : Nat := 4983230072969 + 3 ^ 40 * 8105655 * 2
def baseEnd_8105655 : Nat := 1387365678173196440411759

theorem tailTrace_8105655 : CollatzResearch.WordTrace tailWord_8105655 prefixEnd_8105655 1387365678173196440411759 := by
  unfold tailWord_8105655
  simp only [CollatzResearch.WordTrace]
  refine ⟨295637525449603745506518419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197091683633069163671012279 295637525449603745506518419)
  ·
    refine ⟨443456288174405618259777629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295637525449603745506518419 443456288174405618259777629)
    ·
      refine ⟨166296108065402106847416611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 443456288174405618259777629 166296108065402106847416611)
      ·
        refine ⟨249444162098103160271124917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166296108065402106847416611 249444162098103160271124917)
        ·
          refine ⟨23385390196697171275417961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 249444162098103160271124917 23385390196697171275417961)
          ·
            refine ⟨17539042647522878456563471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23385390196697171275417961 17539042647522878456563471)
            ·
              refine ⟨26308563971284317684845207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17539042647522878456563471 26308563971284317684845207)
              ·
                refine ⟨39462845956926476527267811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26308563971284317684845207 39462845956926476527267811)
                ·
                  refine ⟨59194268935389714790901717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39462845956926476527267811 59194268935389714790901717)
                  ·
                    refine ⟨1387365678173196440411759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59194268935389714790901717 1387365678173196440411759)
                    ·
                      rfl

theorem cell23_8105655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 7].length) (baseStart_8105655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105655 prefixEnd_8105655 := by exact prefixLift 8105655
  have htrace : WordTrace (prefixWord ++ tailWord_8105655) baseStart_8105655 baseEnd_8105655 := by
    simpa [prefixWord, tailWord_8105655, baseEnd_8105655] using wordTrace_append hprefix tailTrace_8105655
  have hstable : (prefixWord ++ tailWord_8105655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105655).length < 2 ^ (prefixWord ++ tailWord_8105655).sum := by decide
  have hdescent : baseEnd_8105655 < baseStart_8105655 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105670 : List Nat := [6, 1, 2, 1, 1, 1, 3, 2, 2, 2, 2]
def baseStart_8105670 : Nat := 118140960795 + 8105670 * 2 ^ 59
def prefixEnd_8105670 : Nat := 4983230072969 + 3 ^ 40 * 8105670 * 2
def baseEnd_8105670 : Nat := 4162104736729406762547709

theorem tailTrace_8105670 : CollatzResearch.WordTrace tailWord_8105670 prefixEnd_8105670 4162104736729406762547709 := by
  unfold tailWord_8105670
  simp only [CollatzResearch.WordTrace]
  refine ⟨9238689767017168845884827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 197092048363032935378876309 9238689767017168845884827)
  ·
    refine ⟨13858034650525753268827241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9238689767017168845884827 13858034650525753268827241)
    ·
      refine ⟨10393525987894314951620431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13858034650525753268827241 10393525987894314951620431)
      ·
        refine ⟨15590288981841472427430647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10393525987894314951620431 15590288981841472427430647)
        ·
          refine ⟨23385433472762208641145971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15590288981841472427430647 23385433472762208641145971)
          ·
            refine ⟨35078150209143312961718957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23385433472762208641145971 35078150209143312961718957)
            ·
              refine ⟨13154306328428742360644609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35078150209143312961718957 13154306328428742360644609)
              ·
                refine ⟨9865729746321556770483457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13154306328428742360644609 9865729746321556770483457)
                ·
                  refine ⟨7399297309741167577862593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9865729746321556770483457 7399297309741167577862593)
                  ·
                    refine ⟨5549472982305875683396945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7399297309741167577862593 5549472982305875683396945)
                    ·
                      refine ⟨4162104736729406762547709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5549472982305875683396945 4162104736729406762547709)
                      ·
                        rfl

theorem cell23_8105670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_8105670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105670 prefixEnd_8105670 := by exact prefixLift 8105670
  have htrace : WordTrace (prefixWord ++ tailWord_8105670) baseStart_8105670 baseEnd_8105670 := by
    simpa [prefixWord, tailWord_8105670, baseEnd_8105670] using wordTrace_append hprefix tailTrace_8105670
  have hstable : (prefixWord ++ tailWord_8105670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105670).length < 2 ^ (prefixWord ++ tailWord_8105670).sum := by decide
  have hdescent : baseEnd_8105670 < baseStart_8105670 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105675 : List Nat := [1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 4]
def baseStart_8105675 : Nat := 118140960795 + 8105675 * 2 ^ 59
def prefixEnd_8105675 : Nat := 4983230072969 + 3 ^ 40 * 8105675 * 2
def baseEnd_8105675 : Nat := 4162107304132679242985185

theorem tailTrace_8105675 : CollatzResearch.WordTrace tailWord_8105675 prefixEnd_8105675 4162107304132679242985185 := by
  unfold tailWord_8105675
  simp only [CollatzResearch.WordTrace]
  refine ⟨295638254909531288922246479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197092169939687525948164319 295638254909531288922246479)
  ·
    refine ⟨443457382364296933383369719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295638254909531288922246479 443457382364296933383369719)
    ·
      refine ⟨665186073546445400075054579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443457382364296933383369719 665186073546445400075054579)
      ·
        refine ⟨997779110319668100112581869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665186073546445400075054579 997779110319668100112581869)
        ·
          refine ⟨374167166369875537542218201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 997779110319668100112581869 374167166369875537542218201)
          ·
            refine ⟨280625374777406653156663651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374167166369875537542218201 280625374777406653156663651)
            ·
              refine ⟨420938062166109979734995477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280625374777406653156663651 420938062166109979734995477)
              ·
                refine ⟨19731471664036405300077913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 420938062166109979734995477 19731471664036405300077913)
                ·
                  refine ⟨14798603748027303975058435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19731471664036405300077913 14798603748027303975058435)
                  ·
                    refine ⟨22197905622040955962587653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14798603748027303975058435 22197905622040955962587653)
                    ·
                      refine ⟨4162107304132679242985185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22197905622040955962587653 4162107304132679242985185)
                      ·
                        rfl

theorem cell23_8105675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 4].length) (baseStart_8105675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105675 prefixEnd_8105675 := by exact prefixLift 8105675
  have htrace : WordTrace (prefixWord ++ tailWord_8105675) baseStart_8105675 baseEnd_8105675 := by
    simpa [prefixWord, tailWord_8105675, baseEnd_8105675] using wordTrace_append hprefix tailTrace_8105675
  have hstable : (prefixWord ++ tailWord_8105675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105675).length < 2 ^ (prefixWord ++ tailWord_8105675).sum := by decide
  have hdescent : baseEnd_8105675 < baseStart_8105675 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105695 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 3, 4, 3]
def baseStart_8105695 : Nat := 118140960795 + 8105695 * 2 ^ 59
def prefixEnd_8105695 : Nat := 4983230072969 + 3 ^ 40 * 8105695 * 2
def baseEnd_8105695 : Nat := 4162117573745769164735093

theorem tailTrace_8105695 : CollatzResearch.WordTrace tailWord_8105695 prefixEnd_8105695 4162117573745769164735093 := by
  unfold tailWord_8105695
  simp only [CollatzResearch.WordTrace]
  refine ⟨295638984369458832337974539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197092656246305888225316359 295638984369458832337974539)
  ·
    refine ⟨443458476554188248506961809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295638984369458832337974539 443458476554188248506961809)
    ·
      refine ⟨332593857415641186380221357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443458476554188248506961809 332593857415641186380221357)
      ·
        refine ⟨124722696530865444892583009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332593857415641186380221357 124722696530865444892583009)
        ·
          refine ⟨93542022398149083669437257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124722696530865444892583009 93542022398149083669437257)
          ·
            refine ⟨70156516798611812752077943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93542022398149083669437257 70156516798611812752077943)
            ·
              refine ⟨105234775197917719128116915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70156516798611812752077943 105234775197917719128116915)
              ·
                refine ⟨157852162796876578692175373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105234775197917719128116915 157852162796876578692175373)
                ·
                  refine ⟨59194561048828717009565765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157852162796876578692175373 59194561048828717009565765)
                  ·
                    refine ⟨11098980196655384439293581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59194561048828717009565765 11098980196655384439293581)
                    ·
                      refine ⟨4162117573745769164735093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11098980196655384439293581 4162117573745769164735093)
                      ·
                        rfl

theorem cell23_8105695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_8105695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105695 prefixEnd_8105695 := by exact prefixLift 8105695
  have htrace : WordTrace (prefixWord ++ tailWord_8105695) baseStart_8105695 baseEnd_8105695 := by
    simpa [prefixWord, tailWord_8105695, baseEnd_8105695] using wordTrace_append hprefix tailTrace_8105695
  have hstable : (prefixWord ++ tailWord_8105695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105695).length < 2 ^ (prefixWord ++ tailWord_8105695).sum := by decide
  have hdescent : baseEnd_8105695 < baseStart_8105695 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105719 : List Nat := [1, 1, 3, 1, 1, 1, 7, 3, 1, 4]
def baseStart_8105719 : Nat := 118140960795 + 8105719 * 2 ^ 59
def prefixEnd_8105719 : Nat := 4983230072969 + 3 ^ 40 * 8105719 * 2
def baseEnd_8105719 : Nat := 1387376632427159023611661

theorem tailTrace_8105719 : CollatzResearch.WordTrace tailWord_8105719 prefixEnd_8105719 1387376632427159023611661 := by
  unfold tailWord_8105719
  simp only [CollatzResearch.WordTrace]
  refine ⟨295639859721371884436848211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197093239814247922957898807 295639859721371884436848211)
  ·
    refine ⟨443459789582057826655272317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295639859721371884436848211 443459789582057826655272317)
    ·
      refine ⟨166297421093271684995727119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 443459789582057826655272317 166297421093271684995727119)
      ·
        refine ⟨249446131639907527493590679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166297421093271684995727119 249446131639907527493590679)
        ·
          refine ⟨374169197459861291240386019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249446131639907527493590679 374169197459861291240386019)
          ·
            refine ⟨561253796189791936860579029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374169197459861291240386019 561253796189791936860579029)
            ·
              refine ⟨13154385848198248520169821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 561253796189791936860579029 13154385848198248520169821)
              ·
                refine ⟨4932894693074343195063683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13154385848198248520169821 4932894693074343195063683)
                ·
                  refine ⟨7399342039611514792595525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4932894693074343195063683 7399342039611514792595525)
                  ·
                    refine ⟨1387376632427159023611661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7399342039611514792595525 1387376632427159023611661)
                    ·
                      rfl

theorem cell23_8105719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 3, 1, 4].length) (baseStart_8105719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105719 prefixEnd_8105719 := by exact prefixLift 8105719
  have htrace : WordTrace (prefixWord ++ tailWord_8105719) baseStart_8105719 baseEnd_8105719 := by
    simpa [prefixWord, tailWord_8105719, baseEnd_8105719] using wordTrace_append hprefix tailTrace_8105719
  have hstable : (prefixWord ++ tailWord_8105719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105719).length < 2 ^ (prefixWord ++ tailWord_8105719).sum := by decide
  have hdescent : baseEnd_8105719 < baseStart_8105719 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105736 : List Nat := [2, 1, 3, 2, 2, 1, 5, 2, 1, 4]
def baseStart_8105736 : Nat := 118140960795 + 8105736 * 2 ^ 59
def prefixEnd_8105736 : Nat := 4983230072969 + 3 ^ 40 * 8105736 * 2
def baseEnd_8105736 : Nat := 1387379542150867834774135

theorem tailTrace_8105736 : CollatzResearch.WordTrace tailWord_8105736 prefixEnd_8105736 1387379542150867834774135 := by
  unfold tailWord_8105736
  simp only [CollatzResearch.WordTrace]
  refine ⟨147820239881155148170108531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197093653174873530893478041 147820239881155148170108531)
  ·
    refine ⟨221730359821732722255162797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147820239881155148170108531 221730359821732722255162797)
    ·
      refine ⟨83148884933149770845686049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221730359821732722255162797 83148884933149770845686049)
      ·
        refine ⟨62361663699862328134264537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83148884933149770845686049 62361663699862328134264537)
        ·
          refine ⟨46771247774896746100698403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62361663699862328134264537 46771247774896746100698403)
          ·
            refine ⟨70156871662345119151047605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46771247774896746100698403 70156871662345119151047605)
            ·
              refine ⟨6577206718344854920410713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70156871662345119151047605 6577206718344854920410713)
              ·
                refine ⟨4932905038758641190308035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6577206718344854920410713 4932905038758641190308035)
                ·
                  refine ⟨7399357558137961785462053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4932905038758641190308035 7399357558137961785462053)
                  ·
                    refine ⟨1387379542150867834774135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7399357558137961785462053 1387379542150867834774135)
                    ·
                      rfl

theorem cell23_8105736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_8105736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105736 prefixEnd_8105736 := by exact prefixLift 8105736
  have htrace : WordTrace (prefixWord ++ tailWord_8105736) baseStart_8105736 baseEnd_8105736 := by
    simpa [prefixWord, tailWord_8105736, baseEnd_8105736] using wordTrace_append hprefix tailTrace_8105736
  have hstable : (prefixWord ++ tailWord_8105736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105736).length < 2 ^ (prefixWord ++ tailWord_8105736).sum := by decide
  have hdescent : baseEnd_8105736 < baseStart_8105736 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105745 : List Nat := [1, 2, 2, 1, 1, 3, 1, 4, 3, 5]
def baseStart_8105745 : Nat := 118140960795 + 8105745 * 2 ^ 59
def prefixEnd_8105745 : Nat := 4983230072969 + 3 ^ 40 * 8105745 * 2
def baseEnd_8105745 : Nat := 1387381082592831323036621

theorem tailTrace_8105745 : CollatzResearch.WordTrace tailWord_8105745 prefixEnd_8105745 1387381082592831323036621 := by
  unfold tailWord_8105745
  simp only [CollatzResearch.WordTrace]
  refine ⟨295640808019277690877294689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197093872012851793918196459 295640808019277690877294689)
  ·
    refine ⟨221730606014458268157971017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295640808019277690877294689 221730606014458268157971017)
    ·
      refine ⟨166297954510843701118478263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221730606014458268157971017 166297954510843701118478263)
      ·
        refine ⟨249446931766265551677717395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166297954510843701118478263 249446931766265551677717395)
        ·
          refine ⟨374170397649398327516576093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249446931766265551677717395 374170397649398327516576093)
          ·
            refine ⟨140313899118524372818716035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374170397649398327516576093 140313899118524372818716035)
            ·
              refine ⟨210470848677786559228074053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140313899118524372818716035 210470848677786559228074053)
              ·
                refine ⟨39463284127084979855263885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210470848677786559228074053 39463284127084979855263885)
                ·
                  refine ⟨14798731547656867445723957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39463284127084979855263885 14798731547656867445723957)
                  ·
                    refine ⟨1387381082592831323036621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14798731547656867445723957 1387381082592831323036621)
                    ·
                      rfl

theorem cell23_8105745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 5].length) (baseStart_8105745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105745 prefixEnd_8105745 := by exact prefixLift 8105745
  have htrace : WordTrace (prefixWord ++ tailWord_8105745) baseStart_8105745 baseEnd_8105745 := by
    simpa [prefixWord, tailWord_8105745, baseEnd_8105745] using wordTrace_append hprefix tailTrace_8105745
  have hstable : (prefixWord ++ tailWord_8105745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105745).length < 2 ^ (prefixWord ++ tailWord_8105745).sum := by decide
  have hdescent : baseEnd_8105745 < baseStart_8105745 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105749 : List Nat := [1, 3, 2, 1, 2, 5, 2, 1, 6]
def baseStart_8105749 : Nat := 118140960795 + 8105749 * 2 ^ 59
def prefixEnd_8105749 : Nat := 4983230072969 + 3 ^ 40 * 8105749 * 2
def baseEnd_8105749 : Nat := 462460589077901328162205

theorem tailTrace_8105749 : CollatzResearch.WordTrace tailWord_8105749 prefixEnd_8105749 462460589077901328162205 := by
  unfold tailWord_8105749
  simp only [CollatzResearch.WordTrace]
  refine ⟨295640953911263199560440301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197093969274175466373626867 295640953911263199560440301)
  ·
    refine ⟨110865357716723699835165113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295640953911263199560440301 110865357716723699835165113)
    ·
      refine ⟨83149018287542774876373835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110865357716723699835165113 83149018287542774876373835)
      ·
        refine ⟨124723527431314162314560753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83149018287542774876373835 124723527431314162314560753)
        ·
          refine ⟨93542645573485621735920565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124723527431314162314560753 93542645573485621735920565)
          ·
            refine ⟨8769623022514277037742553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93542645573485621735920565 8769623022514277037742553)
            ·
              refine ⟨6577217266885707778306915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8769623022514277037742553 6577217266885707778306915)
              ·
                refine ⟨9865825900328561667460373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6577217266885707778306915 9865825900328561667460373)
                ·
                  refine ⟨462460589077901328162205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9865825900328561667460373 462460589077901328162205)
                  ·
                    rfl

theorem cell23_8105749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 1, 6].length) (baseStart_8105749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105749 prefixEnd_8105749 := by exact prefixLift 8105749
  have htrace : WordTrace (prefixWord ++ tailWord_8105749) baseStart_8105749 baseEnd_8105749 := by
    simpa [prefixWord, tailWord_8105749, baseEnd_8105749] using wordTrace_append hprefix tailTrace_8105749
  have hstable : (prefixWord ++ tailWord_8105749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105749).length < 2 ^ (prefixWord ++ tailWord_8105749).sum := by decide
  have hdescent : baseEnd_8105749 < baseStart_8105749 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105752 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 3, 5, 2]
def baseStart_8105752 : Nat := 118140960795 + 8105752 * 2 ^ 59
def prefixEnd_8105752 : Nat := 4983230072969 + 3 ^ 40 * 8105752 * 2
def baseEnd_8105752 : Nat := 4162146842143075441722331

theorem tailTrace_8105752 : CollatzResearch.WordTrace tailWord_8105752 prefixEnd_8105752 4162146842143075441722331 := by
  unfold tailWord_8105752
  simp only [CollatzResearch.WordTrace]
  refine ⟨147820531665126165536399755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197094042220168220715199673 147820531665126165536399755)
  ·
    refine ⟨221730797497689248304599633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147820531665126165536399755 221730797497689248304599633)
    ·
      refine ⟨166298098123266936228449725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221730797497689248304599633 166298098123266936228449725)
      ·
        refine ⟨62361786796225101085668647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166298098123266936228449725 62361786796225101085668647)
        ·
          refine ⟨93542680194337651628502971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62361786796225101085668647 93542680194337651628502971)
          ·
            refine ⟨140314020291506477442754457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93542680194337651628502971 140314020291506477442754457)
            ·
              refine ⟨105235515218629858082065843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140314020291506477442754457 105235515218629858082065843)
              ·
                refine ⟨157853272827944787123098765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105235515218629858082065843 157853272827944787123098765)
                ·
                  refine ⟨59194977310479295171162037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157853272827944787123098765 59194977310479295171162037)
                  ·
                    refine ⟨5549529122857433922296441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59194977310479295171162037 5549529122857433922296441)
                    ·
                      refine ⟨4162146842143075441722331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5549529122857433922296441 4162146842143075441722331)
                      ·
                        rfl

theorem cell23_8105752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_8105752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105752 prefixEnd_8105752 := by exact prefixLift 8105752
  have htrace : WordTrace (prefixWord ++ tailWord_8105752) baseStart_8105752 baseEnd_8105752 := by
    simpa [prefixWord, tailWord_8105752, baseEnd_8105752] using wordTrace_append hprefix tailTrace_8105752
  have hstable : (prefixWord ++ tailWord_8105752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105752).length < 2 ^ (prefixWord ++ tailWord_8105752).sum := by decide
  have hdescent : baseEnd_8105752 < baseStart_8105752 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105762 : List Nat := [3, 3, 1, 1, 2, 1, 3, 1, 3, 5]
def baseStart_8105762 : Nat := 118140960795 + 8105762 * 2 ^ 59
def prefixEnd_8105762 : Nat := 4983230072969 + 3 ^ 40 * 8105762 * 2
def baseEnd_8105762 : Nat := 1387383992316540134199095

theorem tailTrace_8105762 : CollatzResearch.WordTrace tailWord_8105762 prefixEnd_8105762 1387383992316540134199095 := by
  unfold tailWord_8105762
  simp only [CollatzResearch.WordTrace]
  refine ⟨73910357015054025695165885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197094285373477401853775693 73910357015054025695165885)
  ·
    refine ⟨27716383880645259635687207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73910357015054025695165885 27716383880645259635687207)
    ·
      refine ⟨41574575820967889453530811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27716383880645259635687207 41574575820967889453530811)
      ·
        refine ⟨62361863731451834180296217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41574575820967889453530811 62361863731451834180296217)
        ·
          refine ⟨46771397798588875635222163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62361863731451834180296217 46771397798588875635222163)
          ·
            refine ⟨70157096697883313452833245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46771397798588875635222163 70157096697883313452833245)
            ·
              refine ⟨26308911261706242544812467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70157096697883313452833245 26308911261706242544812467)
              ·
                refine ⟨39463366892559363817218701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26308911261706242544812467 39463366892559363817218701)
                ·
                  refine ⟨14798762584709761431457013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39463366892559363817218701 14798762584709761431457013)
                  ·
                    refine ⟨1387383992316540134199095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14798762584709761431457013 1387383992316540134199095)
                    ·
                      rfl

theorem cell23_8105762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_8105762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105762 prefixEnd_8105762 := by exact prefixLift 8105762
  have htrace : WordTrace (prefixWord ++ tailWord_8105762) baseStart_8105762 baseEnd_8105762 := by
    simpa [prefixWord, tailWord_8105762, baseEnd_8105762] using wordTrace_append hprefix tailTrace_8105762
  have hstable : (prefixWord ++ tailWord_8105762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105762).length < 2 ^ (prefixWord ++ tailWord_8105762).sum := by decide
  have hdescent : baseEnd_8105762 < baseStart_8105762 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105775 : List Nat := [1, 1, 2, 1, 2, 1, 2, 6, 1, 6]
def baseStart_8105775 : Nat := 118140960795 + 8105775 * 2 ^ 59
def prefixEnd_8105775 : Nat := 4983230072969 + 3 ^ 40 * 8105775 * 2
def baseEnd_8105775 : Nat := 1387386217399376283911575

theorem tailTrace_8105775 : CollatzResearch.WordTrace tailWord_8105775 prefixEnd_8105775 1387386217399376283911575 := by
  unfold tailWord_8105775
  simp only [CollatzResearch.WordTrace]
  refine ⟨295641902209169006000886779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197094601472779337333924519 295641902209169006000886779)
  ·
    refine ⟨443462853313753509001330169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295641902209169006000886779 443462853313753509001330169)
    ·
      refine ⟨332597139985315131750997627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443462853313753509001330169 332597139985315131750997627)
      ·
        refine ⟨498895709977972697626496441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332597139985315131750997627 498895709977972697626496441)
        ·
          refine ⟨374171782483479523219872331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498895709977972697626496441 374171782483479523219872331)
          ·
            refine ⟨561257673725219284829808497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374171782483479523219872331 561257673725219284829808497)
            ·
              refine ⟨420943255293914463622356373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 561257673725219284829808497 420943255293914463622356373)
              ·
                refine ⟨19731715091902240482297955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 420943255293914463622356373 19731715091902240482297955)
                ·
                  refine ⟨29597572637853360723446933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19731715091902240482297955 29597572637853360723446933)
                  ·
                    refine ⟨1387386217399376283911575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29597572637853360723446933 1387386217399376283911575)
                    ·
                      rfl

theorem cell23_8105775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 6].length) (baseStart_8105775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105775 prefixEnd_8105775 := by exact prefixLift 8105775
  have htrace : WordTrace (prefixWord ++ tailWord_8105775) baseStart_8105775 baseEnd_8105775 := by
    simpa [prefixWord, tailWord_8105775, baseEnd_8105775] using wordTrace_append hprefix tailTrace_8105775
  have hstable : (prefixWord ++ tailWord_8105775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105775).length < 2 ^ (prefixWord ++ tailWord_8105775).sum := by decide
  have hdescent : baseEnd_8105775 < baseStart_8105775 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105802 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 5, 2, 3]
def baseStart_8105802 : Nat := 118140960795 + 8105802 * 2 ^ 59
def prefixEnd_8105802 : Nat := 4983230072969 + 3 ^ 40 * 8105802 * 2
def baseEnd_8105802 : Nat := 4162172516175800246097101

theorem tailTrace_8105802 : CollatzResearch.WordTrace tailWord_8105802 prefixEnd_8105802 4162172516175800246097101 := by
  unfold tailWord_8105802
  simp only [CollatzResearch.WordTrace]
  refine ⟨73910721745017797403029915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197095257986714126408079773 73910721745017797403029915)
  ·
    refine ⟨110866082617526696104544873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73910721745017797403029915 110866082617526696104544873)
    ·
      refine ⟨83149561963145022078408655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110866082617526696104544873 83149561963145022078408655)
      ·
        refine ⟨124724342944717533117612983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83149561963145022078408655 124724342944717533117612983)
        ·
          refine ⟨187086514417076299676419475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124724342944717533117612983 187086514417076299676419475)
          ·
            refine ⟨280629771625614449514629213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187086514417076299676419475 280629771625614449514629213)
            ·
              refine ⟨105236164359605418567985955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280629771625614449514629213 105236164359605418567985955)
              ·
                refine ⟨157854246539408127851978933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105236164359605418567985955 157854246539408127851978933)
                ·
                  refine ⟨14798835613069511986123025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157854246539408127851978933 14798835613069511986123025)
                  ·
                    refine ⟨11099126709802133989592269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14798835613069511986123025 11099126709802133989592269)
                    ·
                      refine ⟨4162172516175800246097101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11099126709802133989592269 4162172516175800246097101)
                      ·
                        rfl

theorem cell23_8105802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_8105802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105802 prefixEnd_8105802 := by exact prefixLift 8105802
  have htrace : WordTrace (prefixWord ++ tailWord_8105802) baseStart_8105802 baseEnd_8105802 := by
    simpa [prefixWord, tailWord_8105802, baseEnd_8105802] using wordTrace_append hprefix tailTrace_8105802
  have hstable : (prefixWord ++ tailWord_8105802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105802).length < 2 ^ (prefixWord ++ tailWord_8105802).sum := by decide
  have hdescent : baseEnd_8105802 < baseStart_8105802 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105809 : List Nat := [1, 2, 2, 1, 5, 1, 2, 3, 2, 4]
def baseStart_8105809 : Nat := 118140960795 + 8105809 * 2 ^ 59
def prefixEnd_8105809 : Nat := 4983230072969 + 3 ^ 40 * 8105809 * 2
def baseEnd_8105809 : Nat := 1387392036846793906236523

theorem tailTrace_8105809 : CollatzResearch.WordTrace tailWord_8105809 prefixEnd_8105809 1387392036846793906236523 := by
  unfold tailWord_8105809
  simp only [CollatzResearch.WordTrace]
  refine ⟨295643142291045829807624481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197095428194030553205082987 295643142291045829807624481)
  ·
    refine ⟨221732356718284372355718361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295643142291045829807624481 221732356718284372355718361)
    ·
      refine ⟨166299267538713279266788771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221732356718284372355718361 166299267538713279266788771)
      ·
        refine ⟨249448901308069918900183157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166299267538713279266788771 249448901308069918900183157)
        ·
          refine ⟨23385834497631554896892171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 249448901308069918900183157 23385834497631554896892171)
          ·
            refine ⟨35078751746447332345338257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23385834497631554896892171 35078751746447332345338257)
            ·
              refine ⟨26309063809835499259003693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35078751746447332345338257 26309063809835499259003693)
              ·
                refine ⟨9865898928688312222126385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26309063809835499259003693 9865898928688312222126385)
                ·
                  refine ⟨7399424196516234166594789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9865898928688312222126385 7399424196516234166594789)
                  ·
                    refine ⟨1387392036846793906236523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7399424196516234166594789 1387392036846793906236523)
                    ·
                      rfl

theorem cell23_8105809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 2, 4].length) (baseStart_8105809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105809 prefixEnd_8105809 := by exact prefixLift 8105809
  have htrace : WordTrace (prefixWord ++ tailWord_8105809) baseStart_8105809 baseEnd_8105809 := by
    simpa [prefixWord, tailWord_8105809, baseEnd_8105809] using wordTrace_append hprefix tailTrace_8105809
  have hstable : (prefixWord ++ tailWord_8105809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105809).length < 2 ^ (prefixWord ++ tailWord_8105809).sum := by decide
  have hdescent : baseEnd_8105809 < baseStart_8105809 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105820 : List Nat := [2, 2, 4, 2, 3, 1, 1, 1, 2, 3, 2]
def baseStart_8105820 : Nat := 118140960795 + 8105820 * 2 ^ 59
def prefixEnd_8105820 : Nat := 4983230072969 + 3 ^ 40 * 8105820 * 2
def baseEnd_8105820 : Nat := 4162181758827581175672019

theorem tailTrace_8105820 : CollatzResearch.WordTrace tailWord_8105820 prefixEnd_8105820 4162181758827581175672019 := by
  unfold tailWord_8105820
  simp only [CollatzResearch.WordTrace]
  refine ⟨147821771747002989343137457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197095695662670652457516609 147821771747002989343137457)
  ·
    refine ⟨110866328810252242007353093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147821771747002989343137457 110866328810252242007353093)
    ·
      refine ⟨20787436651922295376378705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110866328810252242007353093 20787436651922295376378705)
      ·
        refine ⟨15590577488941721532284029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20787436651922295376378705 15590577488941721532284029)
        ·
          refine ⟨5846466558353145574606511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15590577488941721532284029 5846466558353145574606511)
          ·
            refine ⟨8769699837529718361909767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5846466558353145574606511 8769699837529718361909767)
            ·
              refine ⟨13154549756294577542864651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8769699837529718361909767 13154549756294577542864651)
              ·
                refine ⟨19731824634441866314296977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13154549756294577542864651 19731824634441866314296977)
                ·
                  refine ⟨14798868475831399735722733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19731824634441866314296977 14798868475831399735722733)
                  ·
                    refine ⟨5549575678436774900896025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14798868475831399735722733 5549575678436774900896025)
                    ·
                      refine ⟨4162181758827581175672019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5549575678436774900896025 4162181758827581175672019)
                      ·
                        rfl

theorem cell23_8105820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_8105820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105820 prefixEnd_8105820 := by exact prefixLift 8105820
  have htrace : WordTrace (prefixWord ++ tailWord_8105820) baseStart_8105820 baseEnd_8105820 := by
    simpa [prefixWord, tailWord_8105820, baseEnd_8105820] using wordTrace_append hprefix tailTrace_8105820
  have hstable : (prefixWord ++ tailWord_8105820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105820).length < 2 ^ (prefixWord ++ tailWord_8105820).sum := by decide
  have hdescent : baseEnd_8105820 < baseStart_8105820 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105836 : List Nat := [2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 3]
def baseStart_8105836 : Nat := 118140960795 + 8105836 * 2 ^ 59
def prefixEnd_8105836 : Nat := 4983230072969 + 3 ^ 40 * 8105836 * 2
def baseEnd_8105836 : Nat := 4162189974518053113071945

theorem tailTrace_8105836 : CollatzResearch.WordTrace tailWord_8105836 prefixEnd_8105836 4162189974518053113071945 := by
  unfold tailWord_8105836
  simp only [CollatzResearch.WordTrace]
  refine ⟨147822063530974006709428681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197096084707965342279238241 147822063530974006709428681)
  ·
    refine ⟨110866547648230505032071511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147822063530974006709428681 110866547648230505032071511)
    ·
      refine ⟨166299821472345757548107267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110866547648230505032071511 166299821472345757548107267)
      ·
        refine ⟨249449732208518636322160901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166299821472345757548107267 249449732208518636322160901)
        ·
          refine ⟨46771824789097244310405169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249449732208518636322160901 46771824789097244310405169)
          ·
            refine ⟨35078868591822933232803877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46771824789097244310405169 35078868591822933232803877)
            ·
              refine ⟨6577287860966799981150727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35078868591822933232803877 6577287860966799981150727)
              ·
                refine ⟨9865931791450199971726091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6577287860966799981150727 9865931791450199971726091)
                ·
                  refine ⟨14798897687175299957589137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9865931791450199971726091 14798897687175299957589137)
                  ·
                    refine ⟨11099173265381474968191853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14798897687175299957589137 11099173265381474968191853)
                    ·
                      refine ⟨4162189974518053113071945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11099173265381474968191853 4162189974518053113071945)
                      ·
                        rfl

theorem cell23_8105836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 3].length) (baseStart_8105836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105836 prefixEnd_8105836 := by exact prefixLift 8105836
  have htrace : WordTrace (prefixWord ++ tailWord_8105836) baseStart_8105836 baseEnd_8105836 := by
    simpa [prefixWord, tailWord_8105836, baseEnd_8105836] using wordTrace_append hprefix tailTrace_8105836
  have hstable : (prefixWord ++ tailWord_8105836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105836).length < 2 ^ (prefixWord ++ tailWord_8105836).sum := by decide
  have hdescent : baseEnd_8105836 < baseStart_8105836 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105849 : List Nat := [1, 2, 1, 3, 2, 2, 3, 1, 4, 1, 3]
def baseStart_8105849 : Nat := 118140960795 + 8105849 * 2 ^ 59
def prefixEnd_8105849 : Nat := 4983230072969 + 3 ^ 40 * 8105849 * 2
def baseEnd_8105849 : Nat := 4162196649766561562209385

theorem tailTrace_8105849 : CollatzResearch.WordTrace tailWord_8105849 prefixEnd_8105849 4162196649766561562209385 := by
  unfold tailWord_8105849
  simp only [CollatzResearch.WordTrace]
  refine ⟨295644601210900916639080601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197096400807267277759387067 295644601210900916639080601)
  ·
    refine ⟨221733450908175687479310451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295644601210900916639080601 221733450908175687479310451)
    ·
      refine ⟨332600176362263531218965677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221733450908175687479310451 332600176362263531218965677)
      ·
        refine ⟨124725066135848824207112129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332600176362263531218965677 124725066135848824207112129)
        ·
          refine ⟨93543799601886618155334097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124725066135848824207112129 93543799601886618155334097)
          ·
            refine ⟨70157849701414963616500573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93543799601886618155334097 70157849701414963616500573)
            ·
              refine ⟨26309193638030611356187715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70157849701414963616500573 26309193638030611356187715)
              ·
                refine ⟨39463790457045917034281573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26309193638030611356187715 39463790457045917034281573)
                ·
                  refine ⟨7399460710696109443927795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39463790457045917034281573 7399460710696109443927795)
                  ·
                    refine ⟨11099191066044164165891693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7399460710696109443927795 11099191066044164165891693)
                    ·
                      refine ⟨4162196649766561562209385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11099191066044164165891693 4162196649766561562209385)
                      ·
                        rfl

theorem cell23_8105849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_8105849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105849 prefixEnd_8105849 := by exact prefixLift 8105849
  have htrace : WordTrace (prefixWord ++ tailWord_8105849) baseStart_8105849 baseEnd_8105849 := by
    simpa [prefixWord, tailWord_8105849, baseEnd_8105849] using wordTrace_append hprefix tailTrace_8105849
  have hstable : (prefixWord ++ tailWord_8105849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105849).length < 2 ^ (prefixWord ++ tailWord_8105849).sum := by decide
  have hdescent : baseEnd_8105849 < baseStart_8105849 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105892 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 1, 3, 5]
def baseStart_8105892 : Nat := 118140960795 + 8105892 * 2 ^ 59
def prefixEnd_8105892 : Nat := 4983230072969 + 3 ^ 40 * 8105892 * 2
def baseEnd_8105892 : Nat := 4162218729434704893971687

theorem tailTrace_8105892 : CollatzResearch.WordTrace tailWord_8105892 prefixEnd_8105892 4162218729434704893971687 := by
  unfold tailWord_8105892
  simp only [CollatzResearch.WordTrace]
  refine ⟨147823084774872567491447965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197097446366496756655263953 147823084774872567491447965)
  ·
    refine ⟨55433656790577212809292987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147823084774872567491447965 55433656790577212809292987)
    ·
      refine ⟨83150485185865819213939481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55433656790577212809292987 83150485185865819213939481)
      ·
        refine ⟨62362863889399364410454611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83150485185865819213939481 62362863889399364410454611)
        ·
          refine ⟨93544295834099046615681917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62362863889399364410454611 93544295834099046615681917)
          ·
            refine ⟨35079110937787142480880719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93544295834099046615681917 35079110937787142480880719)
            ·
              refine ⟨52618666406680713721321079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35079110937787142480880719 52618666406680713721321079)
              ·
                refine ⟨78927999610021070581981619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52618666406680713721321079 78927999610021070581981619)
                ·
                  refine ⟨118391999415031605872972429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78927999610021070581981619 118391999415031605872972429)
                  ·
                    refine ⟨44396999780636852202364661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118391999415031605872972429 44396999780636852202364661)
                    ·
                      refine ⟨4162218729434704893971687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44396999780636852202364661 4162218729434704893971687)
                      ·
                        rfl

theorem cell23_8105892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_8105892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105892 prefixEnd_8105892 := by exact prefixLift 8105892
  have htrace : WordTrace (prefixWord ++ tailWord_8105892) baseStart_8105892 baseEnd_8105892 := by
    simpa [prefixWord, tailWord_8105892, baseEnd_8105892] using wordTrace_append hprefix tailTrace_8105892
  have hstable : (prefixWord ++ tailWord_8105892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105892).length < 2 ^ (prefixWord ++ tailWord_8105892).sum := by decide
  have hdescent : baseEnd_8105892 < baseStart_8105892 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105966 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 2, 5, 2]
def baseStart_8105966 : Nat := 118140960795 + 8105966 * 2 ^ 59
def prefixEnd_8105966 : Nat := 4983230072969 + 3 ^ 40 * 8105966 * 2
def baseEnd_8105966 : Nat := 4162256727003137604446347

theorem tailTrace_8105966 : CollatzResearch.WordTrace tailWord_8105966 prefixEnd_8105966 4162256727003137604446347 := by
  unfold tailWord_8105966
  simp only [CollatzResearch.WordTrace]
  refine ⟨36956108568934630702636219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197099245700984697080726501 36956108568934630702636219)
  ·
    refine ⟨55434162853401946053954329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36956108568934630702636219 55434162853401946053954329)
    ·
      refine ⟨41575622140051459540465747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55434162853401946053954329 41575622140051459540465747)
      ·
        refine ⟨62363433210077189310698621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41575622140051459540465747 62363433210077189310698621)
        ·
          refine ⟨23386287453778945991511983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62363433210077189310698621 23386287453778945991511983)
          ·
            refine ⟨35079431180668418987267975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23386287453778945991511983 35079431180668418987267975)
            ·
              refine ⟨52619146771002628480901963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35079431180668418987267975 52619146771002628480901963)
              ·
                refine ⟨78928720156503942721352945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52619146771002628480901963 78928720156503942721352945)
                ·
                  refine ⟨59196540117377957041014709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78928720156503942721352945 59196540117377957041014709)
                  ·
                    refine ⟨5549675636004183472595129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59196540117377957041014709 5549675636004183472595129)
                    ·
                      refine ⟨4162256727003137604446347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5549675636004183472595129 4162256727003137604446347)
                      ·
                        rfl

theorem cell23_8105966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_8105966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105966 prefixEnd_8105966 := by exact prefixLift 8105966
  have htrace : WordTrace (prefixWord ++ tailWord_8105966) baseStart_8105966 baseEnd_8105966 := by
    simpa [prefixWord, tailWord_8105966, baseEnd_8105966] using wordTrace_append hprefix tailTrace_8105966
  have hstable : (prefixWord ++ tailWord_8105966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105966).length < 2 ^ (prefixWord ++ tailWord_8105966).sum := by decide
  have hdescent : baseEnd_8105966 < baseStart_8105966 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105979 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 1, 6, 2]
def baseStart_8105979 : Nat := 118140960795 + 8105979 * 2 ^ 59
def prefixEnd_8105979 : Nat := 4983230072969 + 3 ^ 40 * 8105979 * 2
def baseEnd_8105979 : Nat := 4162263402251646053583787

theorem tailTrace_8105979 : CollatzResearch.WordTrace tailWord_8105979 prefixEnd_8105979 4162263402251646053583787 := by
  unfold tailWord_8105979
  simp only [CollatzResearch.WordTrace]
  refine ⟨295649342700429948841312991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197099561800286632560875327 295649342700429948841312991)
  ·
    refine ⟨443474014050644923261969487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295649342700429948841312991 443474014050644923261969487)
    ·
      refine ⟨665211021075967384892954231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443474014050644923261969487 665211021075967384892954231)
      ·
        refine ⟨997816531613951077339431347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665211021075967384892954231 997816531613951077339431347)
        ·
          refine ⟨1496724797420926616009147021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 997816531613951077339431347 1496724797420926616009147021)
          ·
            refine ⟨561271799032847481003430133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1496724797420926616009147021 561271799032847481003430133)
            ·
              refine ⟨52619231159329451344071575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 561271799032847481003430133 52619231159329451344071575)
              ·
                refine ⟨78928846738994177016107363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52619231159329451344071575 78928846738994177016107363)
                ·
                  refine ⟨118393270108491265524161045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78928846738994177016107363 118393270108491265524161045)
                  ·
                    refine ⟨5549684536335528071445049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118393270108491265524161045 5549684536335528071445049)
                    ·
                      refine ⟨4162263402251646053583787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5549684536335528071445049 4162263402251646053583787)
                      ·
                        rfl

theorem cell23_8105979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 6, 2].length) (baseStart_8105979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105979 prefixEnd_8105979 := by exact prefixLift 8105979
  have htrace : WordTrace (prefixWord ++ tailWord_8105979) baseStart_8105979 baseEnd_8105979 := by
    simpa [prefixWord, tailWord_8105979, baseEnd_8105979] using wordTrace_append hprefix tailTrace_8105979
  have hstable : (prefixWord ++ tailWord_8105979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105979).length < 2 ^ (prefixWord ++ tailWord_8105979).sum := by decide
  have hdescent : baseEnd_8105979 < baseStart_8105979 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105989 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 5, 4]
def baseStart_8105989 : Nat := 118140960795 + 8105989 * 2 ^ 59
def prefixEnd_8105989 : Nat := 4983230072969 + 3 ^ 40 * 8105989 * 2
def baseEnd_8105989 : Nat := 1387422845686063671486247

theorem tailTrace_8105989 : CollatzResearch.WordTrace tailWord_8105989 prefixEnd_8105989 1387422845686063671486247 := by
  unfold tailWord_8105989
  simp only [CollatzResearch.WordTrace]
  refine ⟨295649707430393720549177021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197099804953595813699451347 295649707430393720549177021)
  ·
    refine ⟨110868640286397645205941383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295649707430393720549177021 110868640286397645205941383)
    ·
      refine ⟨166302960429596467808912075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110868640286397645205941383 166302960429596467808912075)
      ·
        refine ⟨249454440644394701713368113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166302960429596467808912075 249454440644394701713368113)
        ·
          refine ⟨187090830483296026285026085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249454440644394701713368113 187090830483296026285026085)
          ·
            refine ⟨35079530715618004928442391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187090830483296026285026085 35079530715618004928442391)
            ·
              refine ⟨52619296073427007392663587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35079530715618004928442391 52619296073427007392663587)
              ·
                refine ⟨78928944110140511088995381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52619296073427007392663587 78928944110140511088995381)
                ·
                  refine ⟨7399588510325672914593317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78928944110140511088995381 7399588510325672914593317)
                  ·
                    refine ⟨1387422845686063671486247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7399588510325672914593317 1387422845686063671486247)
                    ·
                      rfl

theorem cell23_8105989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 5, 4].length) (baseStart_8105989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105989 prefixEnd_8105989 := by exact prefixLift 8105989
  have htrace : WordTrace (prefixWord ++ tailWord_8105989) baseStart_8105989 baseEnd_8105989 := by
    simpa [prefixWord, tailWord_8105989, baseEnd_8105989] using wordTrace_append hprefix tailTrace_8105989
  have hstable : (prefixWord ++ tailWord_8105989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105989).length < 2 ^ (prefixWord ++ tailWord_8105989).sum := by decide
  have hdescent : baseEnd_8105989 < baseStart_8105989 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8105997 : List Nat := [1, 7, 1, 2, 1, 1, 2, 3, 5]
def baseStart_8105997 : Nat := 118140960795 + 8105997 * 2 ^ 59
def prefixEnd_8105997 : Nat := 4983230072969 + 3 ^ 40 * 8105997 * 2
def baseEnd_8105997 : Nat := 462474738322602998128745

theorem tailTrace_8105997 : CollatzResearch.WordTrace tailWord_8105997 prefixEnd_8105997 462474738322602998128745 := by
  unfold tailWord_8105997
  simp only [CollatzResearch.WordTrace]
  refine ⟨295649999214364737915468245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197099999476243158610312163 295649999214364737915468245)
  ·
    refine ⟨6929296856586673544893787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 295649999214364737915468245 6929296856586673544893787)
    ·
      refine ⟨10393945284880010317340681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6929296856586673544893787 10393945284880010317340681)
      ·
        refine ⟨7795458963660007738005511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10393945284880010317340681 7795458963660007738005511)
        ·
          refine ⟨11693188445490011607008267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7795458963660007738005511 11693188445490011607008267)
          ·
            refine ⟨17539782668235017410512401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11693188445490011607008267 17539782668235017410512401)
            ·
              refine ⟨13154837001176263057884301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17539782668235017410512401 13154837001176263057884301)
              ·
                refine ⟨4933063875441098646706613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13154837001176263057884301 4933063875441098646706613)
                ·
                  refine ⟨462474738322602998128745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4933063875441098646706613 462474738322602998128745)
                  ·
                    rfl

theorem cell23_8105997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_8105997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8105997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8105997 prefixEnd_8105997 := by exact prefixLift 8105997
  have htrace : WordTrace (prefixWord ++ tailWord_8105997) baseStart_8105997 baseEnd_8105997 := by
    simpa [prefixWord, tailWord_8105997, baseEnd_8105997] using wordTrace_append hprefix tailTrace_8105997
  have hstable : (prefixWord ++ tailWord_8105997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8105997).length < 2 ^ (prefixWord ++ tailWord_8105997).sum := by decide
  have hdescent : baseEnd_8105997 < baseStart_8105997 := by decide
  rcases family_descends (prefixWord ++ tailWord_8105997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106089 : List Nat := [1, 2, 1, 1, 1, 5, 1, 4, 1, 1, 5]
def baseStart_8106089 : Nat := 118140960795 + 8106089 * 2 ^ 59
def prefixEnd_8106089 : Nat := 4983230072969 + 3 ^ 40 * 8106089 * 2
def baseEnd_8106089 : Nat := 4162319885123640623208281

theorem tailTrace_8106089 : CollatzResearch.WordTrace tailWord_8106089 prefixEnd_8106089 4162319885123640623208281 := by
  unfold tailWord_8106089
  simp only [CollatzResearch.WordTrace]
  refine ⟨295653354730031437627817321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197102236486687625085211547 295653354730031437627817321)
  ·
    refine ⟨221740016047523578220862991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295653354730031437627817321 221740016047523578220862991)
    ·
      refine ⟨332610024071285367331294487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221740016047523578220862991 332610024071285367331294487)
      ·
        refine ⟨498915036106928050996941731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332610024071285367331294487 498915036106928050996941731)
        ·
          refine ⟨748372554160392076495412597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498915036106928050996941731 748372554160392076495412597)
          ·
            refine ⟨70159926952536757171444931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 748372554160392076495412597 70159926952536757171444931)
            ·
              refine ⟨105239890428805135757167397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70159926952536757171444931 105239890428805135757167397)
              ·
                refine ⟨19732479455400962954468887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105239890428805135757167397 19732479455400962954468887)
                ·
                  refine ⟨29598719183101444431703331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19732479455400962954468887 29598719183101444431703331)
                  ·
                    refine ⟨44398078774652166647554997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29598719183101444431703331 44398078774652166647554997)
                    ·
                      refine ⟨4162319885123640623208281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44398078774652166647554997 4162319885123640623208281)
                      ·
                        rfl

theorem cell23_8106089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 1, 5].length) (baseStart_8106089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106089 prefixEnd_8106089 := by exact prefixLift 8106089
  have htrace : WordTrace (prefixWord ++ tailWord_8106089) baseStart_8106089 baseEnd_8106089 := by
    simpa [prefixWord, tailWord_8106089, baseEnd_8106089] using wordTrace_append hprefix tailTrace_8106089
  have hstable : (prefixWord ++ tailWord_8106089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106089).length < 2 ^ (prefixWord ++ tailWord_8106089).sum := by decide
  have hdescent : baseEnd_8106089 < baseStart_8106089 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106103 : List Nat := [1, 1, 3, 1, 1, 7, 1, 2, 1, 1, 4]
def baseStart_8106103 : Nat := 118140960795 + 8106103 * 2 ^ 59
def prefixEnd_8106103 : Nat := 4983230072969 + 3 ^ 40 * 8106103 * 2
def baseEnd_8106103 : Nat := 4162327073852803568433217

theorem tailTrace_8106103 : CollatzResearch.WordTrace tailWord_8106103 prefixEnd_8106103 4162327073852803568433217 := by
  unfold tailWord_8106103
  simp only [CollatzResearch.WordTrace]
  refine ⟨295653865351980718018826963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197102576901320478679217975 295653865351980718018826963)
  ·
    refine ⟨443480798027971077028240445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295653865351980718018826963 443480798027971077028240445)
    ·
      refine ⟨166305299260489153885590167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 443480798027971077028240445 166305299260489153885590167)
      ·
        refine ⟨249457948890733730828385251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166305299260489153885590167 249457948890733730828385251)
        ·
          refine ⟨374186923336100596242577877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249457948890733730828385251 374186923336100596242577877)
          ·
            refine ⟨8770006015689857724435419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 374186923336100596242577877 8770006015689857724435419)
            ·
              refine ⟨13155009023534786586653129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8770006015689857724435419 13155009023534786586653129)
              ·
                refine ⟨9866256767651089939989847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13155009023534786586653129 9866256767651089939989847)
                ·
                  refine ⟨14799385151476634909984771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9866256767651089939989847 14799385151476634909984771)
                  ·
                    refine ⟨22199077727214952364977157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14799385151476634909984771 22199077727214952364977157)
                    ·
                      refine ⟨4162327073852803568433217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22199077727214952364977157 4162327073852803568433217)
                      ·
                        rfl

theorem cell23_8106103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 1, 4].length) (baseStart_8106103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106103 prefixEnd_8106103 := by exact prefixLift 8106103
  have htrace : WordTrace (prefixWord ++ tailWord_8106103) baseStart_8106103 baseEnd_8106103 := by
    simpa [prefixWord, tailWord_8106103, baseEnd_8106103] using wordTrace_append hprefix tailTrace_8106103
  have hstable : (prefixWord ++ tailWord_8106103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106103).length < 2 ^ (prefixWord ++ tailWord_8106103).sum := by decide
  have hdescent : baseEnd_8106103 < baseStart_8106103 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106109 : List Nat := [1, 4, 1, 1, 3, 2, 2, 9]
def baseStart_8106109 : Nat := 118140960795 + 8106109 * 2 ^ 59
def prefixEnd_8106109 : Nat := 4983230072969 + 3 ^ 40 * 8106109 * 2
def baseEnd_8106109 : Nat := 154160376101360390554007

theorem tailTrace_8106109 : CollatzResearch.WordTrace tailWord_8106109 prefixEnd_8106109 154160376101360390554007 := by
  unfold tailWord_8106109
  simp only [CollatzResearch.WordTrace]
  refine ⟨295654084189958981043545381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197102722793305987362363587 295654084189958981043545381)
  ·
    refine ⟨55435140785617308945664759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295654084189958981043545381 55435140785617308945664759)
    ·
      refine ⟨83152711178425963418497139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55435140785617308945664759 83152711178425963418497139)
      ·
        refine ⟨124729066767638945127745709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83152711178425963418497139 124729066767638945127745709)
        ·
          refine ⟨46773400037864604422904641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124729066767638945127745709 46773400037864604422904641)
          ·
            refine ⟨35080050028398453317178481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46773400037864604422904641 35080050028398453317178481)
            ·
              refine ⟨26310037521298839987883861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35080050028398453317178481 26310037521298839987883861)
              ·
                refine ⟨154160376101360390554007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26310037521298839987883861 154160376101360390554007)
                ·
                  rfl

theorem cell23_8106109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 9].length) (baseStart_8106109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106109 prefixEnd_8106109 := by exact prefixLift 8106109
  have htrace : WordTrace (prefixWord ++ tailWord_8106109) baseStart_8106109 baseEnd_8106109 := by
    simpa [prefixWord, tailWord_8106109, baseEnd_8106109] using wordTrace_append hprefix tailTrace_8106109
  have hstable : (prefixWord ++ tailWord_8106109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106109).length < 2 ^ (prefixWord ++ tailWord_8106109).sum := by decide
  have hdescent : baseEnd_8106109 < baseStart_8106109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106116 : List Nat := [2, 3, 2, 1, 2, 1, 3, 2, 1, 2, 4]
def baseStart_8106116 : Nat := 118140960795 + 8106116 * 2 ^ 59
def prefixEnd_8106116 : Nat := 4983230072969 + 3 ^ 40 * 8106116 * 2
def baseEnd_8106116 : Nat := 4162333749101312017570657

theorem tailTrace_8106116 : CollatzResearch.WordTrace tailWord_8106116 prefixEnd_8106116 4162333749101312017570657 := by
  unfold tailWord_8106116
  simp only [CollatzResearch.WordTrace]
  refine ⟨147827169750466810619525101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197102893000622414159366801 147827169750466810619525101)
  ·
    refine ⟨55435188656425053982321913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147827169750466810619525101 55435188656425053982321913)
    ·
      refine ⟨41576391492318790486741435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55435188656425053982321913 41576391492318790486741435)
      ·
        refine ⟨62364587238478185730112153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41576391492318790486741435 62364587238478185730112153)
        ·
          refine ⟨46773440428858639297584115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62364587238478185730112153 46773440428858639297584115)
          ·
            refine ⟨70160160643287958946376173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46773440428858639297584115 70160160643287958946376173)
            ·
              refine ⟨26310060241232984604891065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70160160643287958946376173 26310060241232984604891065)
              ·
                refine ⟨19732545180924738453668299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26310060241232984604891065 19732545180924738453668299)
                ·
                  refine ⟨29598817771387107680502449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19732545180924738453668299 29598817771387107680502449)
                  ·
                    refine ⟨22199113328540330760376837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29598817771387107680502449 22199113328540330760376837)
                    ·
                      refine ⟨4162333749101312017570657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22199113328540330760376837 4162333749101312017570657)
                      ·
                        rfl

theorem cell23_8106116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_8106116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106116 prefixEnd_8106116 := by exact prefixLift 8106116
  have htrace : WordTrace (prefixWord ++ tailWord_8106116) baseStart_8106116 baseEnd_8106116 := by
    simpa [prefixWord, tailWord_8106116, baseEnd_8106116] using wordTrace_append hprefix tailTrace_8106116
  have hstable : (prefixWord ++ tailWord_8106116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106116).length < 2 ^ (prefixWord ++ tailWord_8106116).sum := by decide
  have hdescent : baseEnd_8106116 < baseStart_8106116 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106120 : List Nat := [2, 1, 3, 4, 1, 2, 3, 1, 1, 1, 4]
def baseStart_8106120 : Nat := 118140960795 + 8106120 * 2 ^ 59
def prefixEnd_8106120 : Nat := 4983230072969 + 3 ^ 40 * 8106120 * 2
def baseEnd_8106120 : Nat := 4162335803023930001920639

theorem tailTrace_8106120 : CollatzResearch.WordTrace tailWord_8106120 prefixEnd_8106120 4162335803023930001920639 := by
  unfold tailWord_8106120
  simp only [CollatzResearch.WordTrace]
  refine ⟨147827242696459564961097907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197102990261946086614797209 147827242696459564961097907)
  ·
    refine ⟨221740864044689347441646861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147827242696459564961097907 221740864044689347441646861)
    ·
      refine ⟨83152824016758505290617573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221740864044689347441646861 83152824016758505290617573)
      ·
        refine ⟨15591154503142219741990795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83152824016758505290617573 15591154503142219741990795)
        ·
          refine ⟨23386731754713329612986193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15591154503142219741990795 23386731754713329612986193)
          ·
            refine ⟨17540048816034997209739645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23386731754713329612986193 17540048816034997209739645)
            ·
              refine ⟨6577518306013123953652367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17540048816034997209739645 6577518306013123953652367)
              ·
                refine ⟨9866277459019685930478551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6577518306013123953652367 9866277459019685930478551)
                ·
                  refine ⟨14799416188529528895717827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9866277459019685930478551 14799416188529528895717827)
                  ·
                    refine ⟨22199124282794293343576741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14799416188529528895717827 22199124282794293343576741)
                    ·
                      refine ⟨4162335803023930001920639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22199124282794293343576741 4162335803023930001920639)
                      ·
                        rfl

theorem cell23_8106120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_8106120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106120 prefixEnd_8106120 := by exact prefixLift 8106120
  have htrace : WordTrace (prefixWord ++ tailWord_8106120) baseStart_8106120 baseEnd_8106120 := by
    simpa [prefixWord, tailWord_8106120, baseEnd_8106120] using wordTrace_append hprefix tailTrace_8106120
  have hstable : (prefixWord ++ tailWord_8106120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106120).length < 2 ^ (prefixWord ++ tailWord_8106120).sum := by decide
  have hdescent : baseEnd_8106120 < baseStart_8106120 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106126 : List Nat := [4, 1, 1, 3, 4, 10]
def baseStart_8106126 : Nat := 118140960795 + 8106126 * 2 ^ 59
def prefixEnd_8106126 : Nat := 4983230072969 + 3 ^ 40 * 8106126 * 2
def baseEnd_8106126 : Nat := 17128966600443855878377

theorem tailTrace_8106126 : CollatzResearch.WordTrace tailWord_8106126 prefixEnd_8106126 17128966600443855878377 := by
  unfold tailWord_8106126
  simp only [CollatzResearch.WordTrace]
  refine ⟨36956838028862174118364279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197103136153931595297942821 36956838028862174118364279)
  ·
    refine ⟨55435257043293261177546419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36956838028862174118364279 55435257043293261177546419)
    ·
      refine ⟨83152885564939891766319629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55435257043293261177546419 83152885564939891766319629)
      ·
        refine ⟨31182332086852459412369861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83152885564939891766319629 31182332086852459412369861)
        ·
          refine ⟨5846687266284836139819349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31182332086852459412369861 5846687266284836139819349)
          ·
            refine ⟨17128966600443855878377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5846687266284836139819349 17128966600443855878377)
            ·
              rfl

theorem cell23_8106126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 10].length) (baseStart_8106126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106126 prefixEnd_8106126 := by exact prefixLift 8106126
  have htrace : WordTrace (prefixWord ++ tailWord_8106126) baseStart_8106126 baseEnd_8106126 := by
    simpa [prefixWord, tailWord_8106126, baseEnd_8106126] using wordTrace_append hprefix tailTrace_8106126
  have hstable : (prefixWord ++ tailWord_8106126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106126).length < 2 ^ (prefixWord ++ tailWord_8106126).sum := by decide
  have hdescent : baseEnd_8106126 < baseStart_8106126 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106159 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 4]
def baseStart_8106159 : Nat := 118140960795 + 8106159 * 2 ^ 59
def prefixEnd_8106159 : Nat := 4983230072969 + 3 ^ 40 * 8106159 * 2
def baseEnd_8106159 : Nat := 4162355828769455349332959

theorem tailTrace_8106159 : CollatzResearch.WordTrace tailWord_8106159 prefixEnd_8106159 4162355828769455349332959 := by
  unfold tailWord_8106159
  simp only [CollatzResearch.WordTrace]
  refine ⟨295655907839777839582865531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197103938559851893055243687 295655907839777839582865531)
  ·
    refine ⟨443483861759666759374298297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295655907839777839582865531 443483861759666759374298297)
    ·
      refine ⟨332612896319750069530723723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443483861759666759374298297 332612896319750069530723723)
      ·
        refine ⟨498919344479625104296085585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332612896319750069530723723 498919344479625104296085585)
        ·
          refine ⟨374189508359718828222064189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498919344479625104296085585 374189508359718828222064189)
          ·
            refine ⟨140321065634894560583274071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374189508359718828222064189 140321065634894560583274071)
            ·
              refine ⟨210481598452341840874911107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140321065634894560583274071 210481598452341840874911107)
              ·
                refine ⟨315722397678512761312366661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210481598452341840874911107 315722397678512761312366661)
                ·
                  refine ⟨59197949564721142746068749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 315722397678512761312366661 59197949564721142746068749)
                  ·
                    refine ⟨22199231086770428529775781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59197949564721142746068749 22199231086770428529775781)
                    ·
                      refine ⟨4162355828769455349332959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22199231086770428529775781 4162355828769455349332959)
                      ·
                        rfl

theorem cell23_8106159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 4].length) (baseStart_8106159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106159 prefixEnd_8106159 := by exact prefixLift 8106159
  have htrace : WordTrace (prefixWord ++ tailWord_8106159) baseStart_8106159 baseEnd_8106159 := by
    simpa [prefixWord, tailWord_8106159, baseEnd_8106159] using wordTrace_append hprefix tailTrace_8106159
  have hstable : (prefixWord ++ tailWord_8106159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106159).length < 2 ^ (prefixWord ++ tailWord_8106159).sum := by decide
  have hdescent : baseEnd_8106159 < baseStart_8106159 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106163 : List Nat := [1, 1, 1, 2, 3, 2, 1, 6, 1, 3, 2]
def baseStart_8106163 : Nat := 118140960795 + 8106163 * 2 ^ 59
def prefixEnd_8106163 : Nat := 4983230072969 + 3 ^ 40 * 8106163 * 2
def baseEnd_8106163 : Nat := 4162357882692073333682941

theorem tailTrace_8106163 : CollatzResearch.WordTrace tailWord_8106163 prefixEnd_8106163 4162357882692073333682941 := by
  unfold tailWord_8106163
  simp only [CollatzResearch.WordTrace]
  refine ⟨295656053731763348266011143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197104035821175565510674095 295656053731763348266011143)
  ·
    refine ⟨443484080597645022399016715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295656053731763348266011143 443484080597645022399016715)
    ·
      refine ⟨665226120896467533598525073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443484080597645022399016715 665226120896467533598525073)
      ·
        refine ⟨498919590672350650198893805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 665226120896467533598525073 498919590672350650198893805)
        ·
          refine ⟨187094846502131493824585177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 498919590672350650198893805 187094846502131493824585177)
          ·
            refine ⟨140321134876598620368438883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187094846502131493824585177 140321134876598620368438883)
            ·
              refine ⟨210481702314897930552658325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140321134876598620368438883 210481702314897930552658325)
              ·
                refine ⟨9866329796010840494655859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 210481702314897930552658325 9866329796010840494655859)
                ·
                  refine ⟨14799494694016260741983789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9866329796010840494655859 14799494694016260741983789)
                  ·
                    refine ⟨5549810510256097778243921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14799494694016260741983789 5549810510256097778243921)
                    ·
                      refine ⟨4162357882692073333682941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5549810510256097778243921 4162357882692073333682941)
                      ·
                        rfl

theorem cell23_8106163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 3, 2].length) (baseStart_8106163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106163 prefixEnd_8106163 := by exact prefixLift 8106163
  have htrace : WordTrace (prefixWord ++ tailWord_8106163) baseStart_8106163 baseEnd_8106163 := by
    simpa [prefixWord, tailWord_8106163, baseEnd_8106163] using wordTrace_append hprefix tailTrace_8106163
  have hstable : (prefixWord ++ tailWord_8106163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106163).length < 2 ^ (prefixWord ++ tailWord_8106163).sum := by decide
  have hdescent : baseEnd_8106163 < baseStart_8106163 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106169 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 1, 8]
def baseStart_8106169 : Nat := 118140960795 + 8106169 * 2 ^ 59
def prefixEnd_8106169 : Nat := 4983230072969 + 3 ^ 40 * 8106169 * 2
def baseEnd_8106169 : Nat := 1387453654525333436735971

theorem tailTrace_8106169 : CollatzResearch.WordTrace tailWord_8106169 prefixEnd_8106169 1387453654525333436735971 := by
  unfold tailWord_8106169
  simp only [CollatzResearch.WordTrace]
  refine ⟨295656272569741611290729561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197104181713161074193819707 295656272569741611290729561)
  ·
    refine ⟨221742204427306208468047171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295656272569741611290729561 221742204427306208468047171)
    ·
      refine ⟨332613306640959312702070757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221742204427306208468047171 332613306640959312702070757)
      ·
        refine ⟨62364994995179871131638267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 332613306640959312702070757 62364994995179871131638267)
        ·
          refine ⟨93547492492769806697457401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62364994995179871131638267 93547492492769806697457401)
          ·
            refine ⟨70160619369577355023093051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93547492492769806697457401 70160619369577355023093051)
            ·
              refine ⟨105240929054366032534639577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70160619369577355023093051 105240929054366032534639577)
              ·
                refine ⟨78930696790774524400979683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105240929054366032534639577 78930696790774524400979683)
                ·
                  refine ⟨118396045186161786601469525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78930696790774524400979683 118396045186161786601469525)
                  ·
                    refine ⟨1387453654525333436735971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 118396045186161786601469525 1387453654525333436735971)
                    ·
                      rfl

theorem cell23_8106169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 8].length) (baseStart_8106169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106169 prefixEnd_8106169 := by exact prefixLift 8106169
  have htrace : WordTrace (prefixWord ++ tailWord_8106169) baseStart_8106169 baseEnd_8106169 := by
    simpa [prefixWord, tailWord_8106169, baseEnd_8106169] using wordTrace_append hprefix tailTrace_8106169
  have hstable : (prefixWord ++ tailWord_8106169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106169).length < 2 ^ (prefixWord ++ tailWord_8106169).sum := by decide
  have hdescent : baseEnd_8106169 < baseStart_8106169 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106174 : List Nat := [4, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3]
def baseStart_8106174 : Nat := 118140960795 + 8106174 * 2 ^ 59
def prefixEnd_8106174 : Nat := 4983230072969 + 3 ^ 40 * 8106174 * 2
def baseEnd_8106174 : Nat := 4162363530979272790645391

theorem tailTrace_8106174 : CollatzResearch.WordTrace tailWord_8106174 prefixEnd_8106174 4162363530979272790645391 := by
  unfold tailWord_8106174
  simp only [CollatzResearch.WordTrace]
  refine ⟨36957056866840437143082697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197104303289815664763107717 36957056866840437143082697)
  ·
    refine ⟨27717792650130327857312023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36957056866840437143082697 27717792650130327857312023)
    ·
      refine ⟨41576688975195491785968035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27717792650130327857312023 41576688975195491785968035)
      ·
        refine ⟨62365033462793237678952053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41576688975195491785968035 62365033462793237678952053)
        ·
          refine ⟨5846721887136866032401755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62365033462793237678952053 5846721887136866032401755)
          ·
            refine ⟨8770082830705299048602633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5846721887136866032401755 8770082830705299048602633)
            ·
              refine ⟨6577562123028974286451975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8770082830705299048602633 6577562123028974286451975)
              ·
                refine ⟨9866343184543461429677963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6577562123028974286451975 9866343184543461429677963)
                ·
                  refine ⟨14799514776815192144516945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9866343184543461429677963 14799514776815192144516945)
                  ·
                    refine ⟨11099636082611394108387709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14799514776815192144516945 11099636082611394108387709)
                    ·
                      refine ⟨4162363530979272790645391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11099636082611394108387709 4162363530979272790645391)
                      ·
                        rfl

theorem cell23_8106174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_8106174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106174 prefixEnd_8106174 := by exact prefixLift 8106174
  have htrace : WordTrace (prefixWord ++ tailWord_8106174) baseStart_8106174 baseEnd_8106174 := by
    simpa [prefixWord, tailWord_8106174, baseEnd_8106174] using wordTrace_append hprefix tailTrace_8106174
  have hstable : (prefixWord ++ tailWord_8106174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106174).length < 2 ^ (prefixWord ++ tailWord_8106174).sum := by decide
  have hdescent : baseEnd_8106174 < baseStart_8106174 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106179 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 5]
def baseStart_8106179 : Nat := 118140960795 + 8106179 * 2 ^ 59
def prefixEnd_8106179 : Nat := 4983230072969 + 3 ^ 40 * 8106179 * 2
def baseEnd_8106179 : Nat := 4162366098382545271082867

theorem tailTrace_8106179 : CollatzResearch.WordTrace tailWord_8106179 prefixEnd_8106179 4162366098382545271082867 := by
  unfold tailWord_8106179
  simp only [CollatzResearch.WordTrace]
  refine ⟨295656637299705382998593591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197104424866470255332395727 295656637299705382998593591)
  ·
    refine ⟨443484955949558074497890387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295656637299705382998593591 443484955949558074497890387)
    ·
      refine ⟨665227433924337111746835581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443484955949558074497890387 665227433924337111746835581)
      ·
        refine ⟨249460287721626416905063343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 665227433924337111746835581 249460287721626416905063343)
        ·
          refine ⟨374190431582439625357595015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249460287721626416905063343 374190431582439625357595015)
          ·
            refine ⟨561285647373659438036392523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374190431582439625357595015 561285647373659438036392523)
            ·
              refine ⟨841928471060489157054588785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561285647373659438036392523 841928471060489157054588785)
              ·
                refine ⟨631446353295366867790941589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 841928471060489157054588785 631446353295366867790941589)
                ·
                  refine ⟨29599047810720321927700387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 631446353295366867790941589 29599047810720321927700387)
                  ·
                    refine ⟨44398571716080482891550581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29599047810720321927700387 44398571716080482891550581)
                    ·
                      refine ⟨4162366098382545271082867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44398571716080482891550581 4162366098382545271082867)
                      ·
                        rfl

theorem cell23_8106179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_8106179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106179 prefixEnd_8106179 := by exact prefixLift 8106179
  have htrace : WordTrace (prefixWord ++ tailWord_8106179) baseStart_8106179 baseEnd_8106179 := by
    simpa [prefixWord, tailWord_8106179, baseEnd_8106179] using wordTrace_append hprefix tailTrace_8106179
  have hstable : (prefixWord ++ tailWord_8106179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106179).length < 2 ^ (prefixWord ++ tailWord_8106179).sum := by decide
  have hdescent : baseEnd_8106179 < baseStart_8106179 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106204 : List Nat := [2, 2, 5, 2, 2, 1, 1, 1, 1, 3, 3]
def baseStart_8106204 : Nat := 118140960795 + 8106204 * 2 ^ 59
def prefixEnd_8106204 : Nat := 4983230072969 + 3 ^ 40 * 8106204 * 2
def baseEnd_8106204 : Nat := 4162378935398907673270253

theorem tailTrace_8106204 : CollatzResearch.WordTrace tailWord_8106204 prefixEnd_8106204 4162378935398907673270253 := by
  unfold tailWord_8106204
  simp only [CollatzResearch.WordTrace]
  refine ⟨147828774562307406134126833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197105032749743208178835777 147828774562307406134126833)
  ·
    refine ⟨110871580921730554600595125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147828774562307406134126833 110871580921730554600595125)
    ·
      refine ⟨10394210711412239493805793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110871580921730554600595125 10394210711412239493805793)
      ·
        refine ⟨7795658033559179620354345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10394210711412239493805793 7795658033559179620354345)
        ·
          refine ⟨5846743525169384715265759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7795658033559179620354345 5846743525169384715265759)
          ·
            refine ⟨8770115287754077072898639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5846743525169384715265759 8770115287754077072898639)
            ·
              refine ⟨13155172931631115609347959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8770115287754077072898639 13155172931631115609347959)
              ·
                refine ⟨19732759397446673414021939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13155172931631115609347959 19732759397446673414021939)
                ·
                  refine ⟨29599139096170010121032909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19732759397446673414021939 29599139096170010121032909)
                  ·
                    refine ⟨11099677161063753795387341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29599139096170010121032909 11099677161063753795387341)
                    ·
                      refine ⟨4162378935398907673270253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11099677161063753795387341 4162378935398907673270253)
                      ·
                        rfl

theorem cell23_8106204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_8106204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106204 prefixEnd_8106204 := by exact prefixLift 8106204
  have htrace : WordTrace (prefixWord ++ tailWord_8106204) baseStart_8106204 baseEnd_8106204 := by
    simpa [prefixWord, tailWord_8106204, baseEnd_8106204] using wordTrace_append hprefix tailTrace_8106204
  have hstable : (prefixWord ++ tailWord_8106204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106204).length < 2 ^ (prefixWord ++ tailWord_8106204).sum := by decide
  have hdescent : baseEnd_8106204 < baseStart_8106204 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106216 : List Nat := [2, 1, 4, 1, 2, 2, 2, 2, 7]
def baseStart_8106216 : Nat := 118140960795 + 8106216 * 2 ^ 59
def prefixEnd_8106216 : Nat := 4983230072969 + 3 ^ 40 * 8106216 * 2
def baseEnd_8106216 : Nat := 462487233018529069591133

theorem tailTrace_8106216 : CollatzResearch.WordTrace tailWord_8106216 prefixEnd_8106216 462487233018529069591133 := by
  unfold tailWord_8106216
  simp only [CollatzResearch.WordTrace]
  refine ⟨147828993400285669158845251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197105324533714225545127001 147828993400285669158845251)
  ·
    refine ⟨221743490100428503738267877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147828993400285669158845251 221743490100428503738267877)
    ·
      refine ⟨41576904393830344450925227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221743490100428503738267877 41576904393830344450925227)
      ·
        refine ⟨62365356590745516676387841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41576904393830344450925227 62365356590745516676387841)
        ·
          refine ⟨46774017443059137507290881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62365356590745516676387841 46774017443059137507290881)
          ·
            refine ⟨35080513082294353130468161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46774017443059137507290881 35080513082294353130468161)
            ·
              refine ⟨26310384811720764847851121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35080513082294353130468161 26310384811720764847851121)
              ·
                refine ⟨19732788608790573635888341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26310384811720764847851121 19732788608790573635888341)
                ·
                  refine ⟨462487233018529069591133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19732788608790573635888341 462487233018529069591133)
                  ·
                    rfl

theorem cell23_8106216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 7].length) (baseStart_8106216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106216 prefixEnd_8106216 := by exact prefixLift 8106216
  have htrace : WordTrace (prefixWord ++ tailWord_8106216) baseStart_8106216 baseEnd_8106216 := by
    simpa [prefixWord, tailWord_8106216, baseEnd_8106216] using wordTrace_append hprefix tailTrace_8106216
  have hstable : (prefixWord ++ tailWord_8106216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106216).length < 2 ^ (prefixWord ++ tailWord_8106216).sum := by decide
  have hdescent : baseEnd_8106216 < baseStart_8106216 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106280 : List Nat := [2, 1, 5, 1, 3, 1, 2, 1, 2, 5]
def baseStart_8106280 : Nat := 118140960795 + 8106280 * 2 ^ 59
def prefixEnd_8106280 : Nat := 4983230072969 + 3 ^ 40 * 8106280 * 2
def baseEnd_8106280 : Nat := 1387472653309549791973301

theorem tailTrace_8106280 : CollatzResearch.WordTrace tailWord_8106280 prefixEnd_8106280 1387472653309549791973301 := by
  unfold tailWord_8106280
  simp only [CollatzResearch.WordTrace]
  refine ⟨147830160536169738624010147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197106880714892984832013529 147830160536169738624010147)
  ·
    refine ⟨221745240804254607936015221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147830160536169738624010147 221745240804254607936015221)
    ·
      refine ⟨20788616325398869494001427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221745240804254607936015221 20788616325398869494001427)
      ·
        refine ⟨31182924488098304241002141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20788616325398869494001427 31182924488098304241002141)
        ·
          refine ⟨11693596683036864090375803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31182924488098304241002141 11693596683036864090375803)
          ·
            refine ⟨17540395024555296135563705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11693596683036864090375803 17540395024555296135563705)
            ·
              refine ⟨13155296268416472101672779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17540395024555296135563705 13155296268416472101672779)
              ·
                refine ⟨19732944402624708152509169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13155296268416472101672779 19732944402624708152509169)
                ·
                  refine ⟨14799708301968531114381877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19732944402624708152509169 14799708301968531114381877)
                  ·
                    refine ⟨1387472653309549791973301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14799708301968531114381877 1387472653309549791973301)
                    ·
                      rfl

theorem cell23_8106280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_8106280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106280 prefixEnd_8106280 := by exact prefixLift 8106280
  have htrace : WordTrace (prefixWord ++ tailWord_8106280) baseStart_8106280 baseEnd_8106280 := by
    simpa [prefixWord, tailWord_8106280, baseEnd_8106280] using wordTrace_append hprefix tailTrace_8106280
  have hstable : (prefixWord ++ tailWord_8106280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106280).length < 2 ^ (prefixWord ++ tailWord_8106280).sum := by decide
  have hdescent : baseEnd_8106280 < baseStart_8106280 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106303 : List Nat := [1, 1, 2, 2, 4, 1, 1, 4, 2, 2, 3]
def baseStart_8106303 : Nat := 118140960795 + 8106303 * 2 ^ 59
def prefixEnd_8106303 : Nat := 4983230072969 + 3 ^ 40 * 8106303 * 2
def baseEnd_8106303 : Nat := 4162429769983702785932297

theorem tailTrace_8106303 : CollatzResearch.WordTrace tailWord_8106303 prefixEnd_8106303 4162429769983702785932297 := by
  unfold tailWord_8106303
  simp only [CollatzResearch.WordTrace]
  refine ⟨295661159951256152176107563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197107439967504101450738375 295661159951256152176107563)
  ·
    refine ⟨443491739926884228264161345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295661159951256152176107563 443491739926884228264161345)
    ·
      refine ⟨332618804945163171198121009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443491739926884228264161345 332618804945163171198121009)
      ·
        refine ⟨249464103708872378398590757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 332618804945163171198121009 249464103708872378398590757)
        ·
          refine ⟨46774519445413570949735767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249464103708872378398590757 46774519445413570949735767)
          ·
            refine ⟨70161779168120356424603651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46774519445413570949735767 70161779168120356424603651)
            ·
              refine ⟨105242668752180534636905477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70161779168120356424603651 105242668752180534636905477)
              ·
                refine ⟨19733000391033850244419777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105242668752180534636905477 19733000391033850244419777)
                ·
                  refine ⟨14799750293275387683314833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19733000391033850244419777 14799750293275387683314833)
                  ·
                    refine ⟨11099812719956540762486125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14799750293275387683314833 11099812719956540762486125)
                    ·
                      refine ⟨4162429769983702785932297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11099812719956540762486125 4162429769983702785932297)
                      ·
                        rfl

theorem cell23_8106303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 2, 3].length) (baseStart_8106303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106303 prefixEnd_8106303 := by exact prefixLift 8106303
  have htrace : WordTrace (prefixWord ++ tailWord_8106303) baseStart_8106303 baseEnd_8106303 := by
    simpa [prefixWord, tailWord_8106303, baseEnd_8106303] using wordTrace_append hprefix tailTrace_8106303
  have hstable : (prefixWord ++ tailWord_8106303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106303).length < 2 ^ (prefixWord ++ tailWord_8106303).sum := by decide
  have hdescent : baseEnd_8106303 < baseStart_8106303 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106444 : List Nat := [2, 2, 1, 4, 3, 2, 1, 2, 1, 2, 3]
def baseStart_8106444 : Nat := 118140960795 + 8106444 * 2 ^ 59
def prefixEnd_8106444 : Nat := 4983230072969 + 3 ^ 40 * 8106444 * 2
def baseEnd_8106444 : Nat := 4162502170755986734269149

theorem tailTrace_8106444 : CollatzResearch.WordTrace tailWord_8106444 prefixEnd_8106444 4162502170755986734269149 := by
  unfold tailWord_8106444
  simp only [CollatzResearch.WordTrace]
  refine ⟨147833151321872666628495193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197110868429163555504660257 147833151321872666628495193)
  ·
    refine ⟨110874863491404499971371395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147833151321872666628495193 110874863491404499971371395)
    ·
      refine ⟨166312295237106749957057093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110874863491404499971371395 166312295237106749957057093)
      ·
        refine ⟨31183555356957515616948205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166312295237106749957057093 31183555356957515616948205)
        ·
          refine ⟨11693833258859068356355577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31183555356957515616948205 11693833258859068356355577)
          ·
            refine ⟨8770374944144301267266683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11693833258859068356355577 8770374944144301267266683)
            ·
              refine ⟨13155562416216451900900025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8770374944144301267266683 13155562416216451900900025)
              ·
                refine ⟨9866671812162338925675019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13155562416216451900900025 9866671812162338925675019)
                ·
                  refine ⟨14800007718243508388512529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9866671812162338925675019 14800007718243508388512529)
                  ·
                    refine ⟨11100005788682631291384397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14800007718243508388512529 11100005788682631291384397)
                    ·
                      refine ⟨4162502170755986734269149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11100005788682631291384397 4162502170755986734269149)
                      ·
                        rfl

theorem cell23_8106444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_8106444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106444 prefixEnd_8106444 := by exact prefixLift 8106444
  have htrace : WordTrace (prefixWord ++ tailWord_8106444) baseStart_8106444 baseEnd_8106444 := by
    simpa [prefixWord, tailWord_8106444, baseEnd_8106444] using wordTrace_append hprefix tailTrace_8106444
  have hstable : (prefixWord ++ tailWord_8106444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106444).length < 2 ^ (prefixWord ++ tailWord_8106444).sum := by decide
  have hdescent : baseEnd_8106444 < baseStart_8106444 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106474 : List Nat := [3, 1, 3, 1, 3, 2, 2, 2, 2, 1, 3]
def baseStart_8106474 : Nat := 118140960795 + 8106474 * 2 ^ 59
def prefixEnd_8106474 : Nat := 4983230072969 + 3 ^ 40 * 8106474 * 2
def baseEnd_8106474 : Nat := 4162517575175621616894011

theorem tailTrace_8106474 : CollatzResearch.WordTrace tailWord_8106474 prefixEnd_8106474 4162517575175621616894011 := by
  unfold tailWord_8106474
  simp only [CollatzResearch.WordTrace]
  refine ⟨73916849208409162095145619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197111597889091098920388317 73916849208409162095145619)
  ·
    refine ⟨110875273812613743142718429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73916849208409162095145619 110875273812613743142718429)
    ·
      refine ⟨41578227679730153678519411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110875273812613743142718429 41578227679730153678519411)
      ·
        refine ⟨62367341519595230517779117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41578227679730153678519411 62367341519595230517779117)
        ·
          refine ⟨23387753069848211444167169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62367341519595230517779117 23387753069848211444167169)
          ·
            refine ⟨17540814802386158583125377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23387753069848211444167169 17540814802386158583125377)
            ·
              refine ⟨13155611101789618937344033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17540814802386158583125377 13155611101789618937344033)
              ·
                refine ⟨9866708326342214203008025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13155611101789618937344033 9866708326342214203008025)
                ·
                  refine ⟨7400031244756660652256019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9866708326342214203008025 7400031244756660652256019)
                  ·
                    refine ⟨11100046867134990978384029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7400031244756660652256019 11100046867134990978384029)
                    ·
                      refine ⟨4162517575175621616894011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11100046867134990978384029 4162517575175621616894011)
                      ·
                        rfl

theorem cell23_8106474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_8106474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106474 prefixEnd_8106474 := by exact prefixLift 8106474
  have htrace : WordTrace (prefixWord ++ tailWord_8106474) baseStart_8106474 baseEnd_8106474 := by
    simpa [prefixWord, tailWord_8106474, baseEnd_8106474] using wordTrace_append hprefix tailTrace_8106474
  have hstable : (prefixWord ++ tailWord_8106474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106474).length < 2 ^ (prefixWord ++ tailWord_8106474).sum := by decide
  have hdescent : baseEnd_8106474 < baseStart_8106474 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106480 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 3, 4, 2]
def baseStart_8106480 : Nat := 118140960795 + 8106480 * 2 ^ 59
def prefixEnd_8106480 : Nat := 4983230072969 + 3 ^ 40 * 8106480 * 2
def baseEnd_8106480 : Nat := 4162520656059548593418983

theorem tailTrace_8106480 : CollatzResearch.WordTrace tailWord_8106480 prefixEnd_8106480 4162520656059548593418983 := by
  unfold tailWord_8106480
  simp only [CollatzResearch.WordTrace]
  refine ⟨147833807835807455702650447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197111743781076607603533929 147833807835807455702650447)
  ·
    refine ⟨221750711753711183553975671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147833807835807455702650447 221750711753711183553975671)
    ·
      refine ⟨332626067630566775330963507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221750711753711183553975671 332626067630566775330963507)
      ·
        refine ⟨498939101445850162996445261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332626067630566775330963507 498939101445850162996445261)
        ·
          refine ⟨187102163042193811123666973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 498939101445850162996445261 187102163042193811123666973)
          ·
            refine ⟨70163311140822679171375115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187102163042193811123666973 70163311140822679171375115)
            ·
              refine ⟨105244966711234018757062673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70163311140822679171375115 105244966711234018757062673)
              ·
                refine ⟨78933725033425514067797005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105244966711234018757062673 78933725033425514067797005)
                ·
                  refine ⟨29600146887534567775423877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78933725033425514067797005 29600146887534567775423877)
                  ·
                    refine ⟨5550027541412731457891977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29600146887534567775423877 5550027541412731457891977)
                    ·
                      refine ⟨4162520656059548593418983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5550027541412731457891977 4162520656059548593418983)
                      ·
                        rfl

theorem cell23_8106480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 3, 4, 2].length) (baseStart_8106480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106480 prefixEnd_8106480 := by exact prefixLift 8106480
  have htrace : WordTrace (prefixWord ++ tailWord_8106480) baseStart_8106480 baseEnd_8106480 := by
    simpa [prefixWord, tailWord_8106480, baseEnd_8106480] using wordTrace_append hprefix tailTrace_8106480
  have hstable : (prefixWord ++ tailWord_8106480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106480).length < 2 ^ (prefixWord ++ tailWord_8106480).sum := by decide
  have hdescent : baseEnd_8106480 < baseStart_8106480 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106483 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 1, 6, 3]
def baseStart_8106483 : Nat := 118140960795 + 8106483 * 2 ^ 59
def prefixEnd_8106483 : Nat := 4983230072969 + 3 ^ 40 * 8106483 * 2
def baseEnd_8106483 : Nat := 4162522196501512081681469

theorem tailTrace_8106483 : CollatzResearch.WordTrace tailWord_8106483 prefixEnd_8106483 4162522196501512081681469 := by
  unfold tailWord_8106483
  simp only [CollatzResearch.WordTrace]
  refine ⟨295667725090604042917660103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197111816727069361945106735 295667725090604042917660103)
  ·
    refine ⟨443501587635906064376490155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295667725090604042917660103 443501587635906064376490155)
    ·
      refine ⟨665252381453859096564735233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443501587635906064376490155 665252381453859096564735233)
      ·
        refine ⟨498939286090394322423551425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 665252381453859096564735233 498939286090394322423551425)
        ·
          refine ⟨374204464567795741817663569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498939286090394322423551425 374204464567795741817663569)
          ·
            refine ⟨280653348425846806363247677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374204464567795741817663569 280653348425846806363247677)
            ·
              refine ⟨105245005659692552386217879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280653348425846806363247677 105245005659692552386217879)
              ·
                refine ⟨157867508489538828579326819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105245005659692552386217879 157867508489538828579326819)
                ·
                  refine ⟨236801262734308242868990229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157867508489538828579326819 236801262734308242868990229)
                  ·
                    refine ⟨11100059190670698884483917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 236801262734308242868990229 11100059190670698884483917)
                    ·
                      refine ⟨4162522196501512081681469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11100059190670698884483917 4162522196501512081681469)
                      ·
                        rfl

theorem cell23_8106483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 6, 3].length) (baseStart_8106483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106483 prefixEnd_8106483 := by exact prefixLift 8106483
  have htrace : WordTrace (prefixWord ++ tailWord_8106483) baseStart_8106483 baseEnd_8106483 := by
    simpa [prefixWord, tailWord_8106483, baseEnd_8106483] using wordTrace_append hprefix tailTrace_8106483
  have hstable : (prefixWord ++ tailWord_8106483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106483).length < 2 ^ (prefixWord ++ tailWord_8106483).sum := by decide
  have hdescent : baseEnd_8106483 < baseStart_8106483 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106497 : List Nat := [1, 2, 4, 1, 3, 1, 1, 3, 1, 4, 2]
def baseStart_8106497 : Nat := 118140960795 + 8106497 * 2 ^ 59
def prefixEnd_8106497 : Nat := 4983230072969 + 3 ^ 40 * 8106497 * 2
def baseEnd_8106497 : Nat := 4162529385230675026906405

theorem tailTrace_8106497 : CollatzResearch.WordTrace tailWord_8106497 prefixEnd_8106497 4162529385230675026906405 := by
  unfold tailWord_8106497
  simp only [CollatzResearch.WordTrace]
  refine ⟨295668235712553323308669745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197112157141702215539113163 295668235712553323308669745)
  ·
    refine ⟨221751176784414992481502309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295668235712553323308669745 221751176784414992481502309)
    ·
      refine ⟨41578345647077811090281683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221751176784414992481502309 41578345647077811090281683)
      ·
        refine ⟨62367518470616716635422525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41578345647077811090281683 62367518470616716635422525)
        ·
          refine ⟨23387819426481268738283447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62367518470616716635422525 23387819426481268738283447)
          ·
            refine ⟨35081729139721903107425171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23387819426481268738283447 35081729139721903107425171)
            ·
              refine ⟨52622593709582854661137757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35081729139721903107425171 52622593709582854661137757)
              ·
                refine ⟨19733472641093570497926659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52622593709582854661137757 19733472641093570497926659)
                ·
                  refine ⟨29600208961640355746889989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19733472641093570497926659 29600208961640355746889989)
                  ·
                    refine ⟨5550039180307566702541873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29600208961640355746889989 5550039180307566702541873)
                    ·
                      refine ⟨4162529385230675026906405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5550039180307566702541873 4162529385230675026906405)
                      ·
                        rfl

theorem cell23_8106497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_8106497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106497 prefixEnd_8106497 := by exact prefixLift 8106497
  have htrace : WordTrace (prefixWord ++ tailWord_8106497) baseStart_8106497 baseEnd_8106497 := by
    simpa [prefixWord, tailWord_8106497, baseEnd_8106497] using wordTrace_append hprefix tailTrace_8106497
  have hstable : (prefixWord ++ tailWord_8106497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106497).length < 2 ^ (prefixWord ++ tailWord_8106497).sum := by decide
  have hdescent : baseEnd_8106497 < baseStart_8106497 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106531 : List Nat := [1, 1, 1, 4, 4, 3, 1, 2, 2, 2, 2]
def baseStart_8106531 : Nat := 118140960795 + 8106531 * 2 ^ 59
def prefixEnd_8106531 : Nat := 4983230072969 + 3 ^ 40 * 8106531 * 2
def baseEnd_8106531 : Nat := 4162546843572927893881249

theorem tailTrace_8106531 : CollatzResearch.WordTrace tailWord_8106531 prefixEnd_8106531 4162546843572927893881249 := by
  unfold tailWord_8106531
  simp only [CollatzResearch.WordTrace]
  refine ⟨295669475794430147115407447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197112983862953431410271631 295669475794430147115407447)
  ·
    refine ⟨443504213691645220673111171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295669475794430147115407447 443504213691645220673111171)
    ·
      refine ⟨665256320537467831009666757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443504213691645220673111171 665256320537467831009666757)
      ·
        refine ⟨124735560100775218314312517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 665256320537467831009666757 124735560100775218314312517)
        ·
          refine ⟨23387917518895353433933597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124735560100775218314312517 23387917518895353433933597)
          ·
            refine ⟨8770469069585757537725099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23387917518895353433933597 8770469069585757537725099)
            ·
              refine ⟨13155703604378636306587649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8770469069585757537725099 13155703604378636306587649)
              ·
                refine ⟨9866777703283977229940737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13155703604378636306587649 9866777703283977229940737)
                ·
                  refine ⟨7400083277462982922455553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9866777703283977229940737 7400083277462982922455553)
                  ·
                    refine ⟨5550062458097237191841665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7400083277462982922455553 5550062458097237191841665)
                    ·
                      refine ⟨4162546843572927893881249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5550062458097237191841665 4162546843572927893881249)
                      ·
                        rfl

theorem cell23_8106531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 2, 2, 2].length) (baseStart_8106531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106531 prefixEnd_8106531 := by exact prefixLift 8106531
  have htrace : WordTrace (prefixWord ++ tailWord_8106531) baseStart_8106531 baseEnd_8106531 := by
    simpa [prefixWord, tailWord_8106531, baseEnd_8106531] using wordTrace_append hprefix tailTrace_8106531
  have hstable : (prefixWord ++ tailWord_8106531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106531).length < 2 ^ (prefixWord ++ tailWord_8106531).sum := by decide
  have hdescent : baseEnd_8106531 < baseStart_8106531 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106540 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 1, 7, 2]
def baseStart_8106540 : Nat := 118140960795 + 8106540 * 2 ^ 59
def prefixEnd_8106540 : Nat := 4983230072969 + 3 ^ 40 * 8106540 * 2
def baseEnd_8106540 : Nat := 4162551464898818358668707

theorem tailTrace_8106540 : CollatzResearch.WordTrace tailWord_8106540 prefixEnd_8106540 4162551464898818358668707 := by
  unfold tailWord_8106540
  simp only [CollatzResearch.WordTrace]
  refine ⟨147834902025698770826242537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197113202700931694434990049 147834902025698770826242537)
  ·
    refine ⟨110876176519274078119681903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147834902025698770826242537 110876176519274078119681903)
    ·
      refine ⟨166314264778911117179522855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110876176519274078119681903 166314264778911117179522855)
      ·
        refine ⟨249471397168366675769284283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166314264778911117179522855 249471397168366675769284283)
        ·
          refine ⟨374207095752550013653926425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249471397168366675769284283 374207095752550013653926425)
          ·
            refine ⟨280655321814412510240444819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374207095752550013653926425 280655321814412510240444819)
            ·
              refine ⟨420982982721618765360667229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280655321814412510240444819 420982982721618765360667229)
              ·
                refine ⟨157868618520607037010250211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 420982982721618765360667229 157868618520607037010250211)
                ·
                  refine ⟨236802927780910555515375317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157868618520607037010250211 236802927780910555515375317)
                  ·
                    refine ⟨5550068619865091144891609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 236802927780910555515375317 5550068619865091144891609)
                    ·
                      refine ⟨4162551464898818358668707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5550068619865091144891609 4162551464898818358668707)
                      ·
                        rfl

theorem cell23_8106540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 7, 2].length) (baseStart_8106540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106540 prefixEnd_8106540 := by exact prefixLift 8106540
  have htrace : WordTrace (prefixWord ++ tailWord_8106540) baseStart_8106540 baseEnd_8106540 := by
    simpa [prefixWord, tailWord_8106540, baseEnd_8106540] using wordTrace_append hprefix tailTrace_8106540
  have hstable : (prefixWord ++ tailWord_8106540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106540).length < 2 ^ (prefixWord ++ tailWord_8106540).sum := by decide
  have hdescent : baseEnd_8106540 < baseStart_8106540 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106548 : List Nat := [2, 5, 1, 3, 1, 2, 1, 1, 1, 4, 2]
def baseStart_8106548 : Nat := 118140960795 + 8106548 * 2 ^ 59
def prefixEnd_8106548 : Nat := 4983230072969 + 3 ^ 40 * 8106548 * 2
def baseEnd_8106548 : Nat := 4162555572744054327368671

theorem tailTrace_8106548 : CollatzResearch.WordTrace tailWord_8106548 prefixEnd_8106548 4162555572744054327368671 := by
  unfold tailWord_8106548
  simp only [CollatzResearch.WordTrace]
  refine ⟨147835047917684279509388149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197113397223579039345850865 147835047917684279509388149)
  ·
    refine ⟨13859535742282901204005139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147835047917684279509388149 13859535742282901204005139)
    ·
      refine ⟨20789303613424351806007709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13859535742282901204005139 20789303613424351806007709)
      ·
        refine ⟨7795988855034131927252891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20789303613424351806007709 7795988855034131927252891)
        ·
          refine ⟨11693983282551197890879337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7795988855034131927252891 11693983282551197890879337)
          ·
            refine ⟨8770487461913398418159503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11693983282551197890879337 8770487461913398418159503)
            ·
              refine ⟨13155731192870097627239255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8770487461913398418159503 13155731192870097627239255)
              ·
                refine ⟨19733596789305146440858883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13155731192870097627239255 19733596789305146440858883)
                ·
                  refine ⟨29600395183957719661288325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19733596789305146440858883 29600395183957719661288325)
                  ·
                    refine ⟨5550074096992072436491561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29600395183957719661288325 5550074096992072436491561)
                    ·
                      refine ⟨4162555572744054327368671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5550074096992072436491561 4162555572744054327368671)
                      ·
                        rfl

theorem cell23_8106548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_8106548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106548 prefixEnd_8106548 := by exact prefixLift 8106548
  have htrace : WordTrace (prefixWord ++ tailWord_8106548) baseStart_8106548 baseEnd_8106548 := by
    simpa [prefixWord, tailWord_8106548, baseEnd_8106548] using wordTrace_append hprefix tailTrace_8106548
  have hstable : (prefixWord ++ tailWord_8106548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106548).length < 2 ^ (prefixWord ++ tailWord_8106548).sum := by decide
  have hdescent : baseEnd_8106548 < baseStart_8106548 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106570 : List Nat := [3, 1, 2, 1, 1, 4, 2, 1, 1, 3, 4]
def baseStart_8106570 : Nat := 118140960795 + 8106570 * 2 ^ 59
def prefixEnd_8106570 : Nat := 4983230072969 + 3 ^ 40 * 8106570 * 2
def baseEnd_8106570 : Nat := 4162566869318453241293569

theorem tailTrace_8106570 : CollatzResearch.WordTrace tailWord_8106570 prefixEnd_8106570 4162566869318453241293569 := by
  unfold tailWord_8106570
  simp only [CollatzResearch.WordTrace]
  refine ⟨73917724560322214194019291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197113932160859237850718109 73917724560322214194019291)
  ·
    refine ⟨110876586840483321291028937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73917724560322214194019291 110876586840483321291028937)
    ·
      refine ⟨83157440130362490968271703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110876586840483321291028937 83157440130362490968271703)
      ·
        refine ⟨124736160195543736452407555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83157440130362490968271703 124736160195543736452407555)
        ·
          refine ⟨187104240293315604678611333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124736160195543736452407555 187104240293315604678611333)
          ·
            refine ⟨35082045054996675877239625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187104240293315604678611333 35082045054996675877239625)
            ·
              refine ⟨26311533791247506907929719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35082045054996675877239625 26311533791247506907929719)
              ·
                refine ⟨39467300686871260361894579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26311533791247506907929719 39467300686871260361894579)
                ·
                  refine ⟨59200951030306890542841869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39467300686871260361894579 59200951030306890542841869)
                  ·
                    refine ⟨22200356636365083953565701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59200951030306890542841869 22200356636365083953565701)
                    ·
                      refine ⟨4162566869318453241293569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22200356636365083953565701 4162566869318453241293569)
                      ·
                        rfl

theorem cell23_8106570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_8106570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106570 prefixEnd_8106570 := by exact prefixLift 8106570
  have htrace : WordTrace (prefixWord ++ tailWord_8106570) baseStart_8106570 baseEnd_8106570 := by
    simpa [prefixWord, tailWord_8106570, baseEnd_8106570] using wordTrace_append hprefix tailTrace_8106570
  have hstable : (prefixWord ++ tailWord_8106570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106570).length < 2 ^ (prefixWord ++ tailWord_8106570).sum := by decide
  have hdescent : baseEnd_8106570 < baseStart_8106570 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106594 : List Nat := [3, 3, 2, 3, 1, 1, 1, 1, 1, 2, 5]
def baseStart_8106594 : Nat := 118140960795 + 8106594 * 2 ^ 59
def prefixEnd_8106594 : Nat := 4983230072969 + 3 ^ 40 * 8106594 * 2
def baseEnd_8106594 : Nat := 4162579192854161147393459

theorem tailTrace_8106594 : CollatzResearch.WordTrace tailWord_8106594 prefixEnd_8106594 4162579192854161147393459 := by
  unfold tailWord_8106594
  simp only [CollatzResearch.WordTrace]
  refine ⟨73917943398300477218737709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197114515728801272583300557 73917943398300477218737709)
  ·
    refine ⟨27719228774362678957026641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73917943398300477218737709 27719228774362678957026641)
    ·
      refine ⟨20789421580772009217769981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27719228774362678957026641 20789421580772009217769981)
      ·
        refine ⟨7796033092789503456663743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20789421580772009217769981 7796033092789503456663743)
        ·
          refine ⟨11694049639184255184995615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7796033092789503456663743 11694049639184255184995615)
          ·
            refine ⟨17541074458776382777493423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11694049639184255184995615 17541074458776382777493423)
            ·
              refine ⟨26311611688164574166240135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17541074458776382777493423 26311611688164574166240135)
              ·
                refine ⟨39467417532246861249360203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26311611688164574166240135 39467417532246861249360203)
                ·
                  refine ⟨59201126298370291874040305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39467417532246861249360203 59201126298370291874040305)
                  ·
                    refine ⟨44400844723777718905530229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59201126298370291874040305 44400844723777718905530229)
                    ·
                      refine ⟨4162579192854161147393459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44400844723777718905530229 4162579192854161147393459)
                      ·
                        rfl

theorem cell23_8106594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_8106594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106594 prefixEnd_8106594 := by exact prefixLift 8106594
  have htrace : WordTrace (prefixWord ++ tailWord_8106594) baseStart_8106594 baseEnd_8106594 := by
    simpa [prefixWord, tailWord_8106594, baseEnd_8106594] using wordTrace_append hprefix tailTrace_8106594
  have hstable : (prefixWord ++ tailWord_8106594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106594).length < 2 ^ (prefixWord ++ tailWord_8106594).sum := by decide
  have hdescent : baseEnd_8106594 < baseStart_8106594 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106620 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 2, 5, 3]
def baseStart_8106620 : Nat := 118140960795 + 8106620 * 2 ^ 59
def prefixEnd_8106620 : Nat := 4983230072969 + 3 ^ 40 * 8106620 * 2
def baseEnd_8106620 : Nat := 4162592543351178045668339

theorem tailTrace_8106620 : CollatzResearch.WordTrace tailWord_8106620 prefixEnd_8106620 4162592543351178045668339 := by
  unfold tailWord_8106620
  simp only [CollatzResearch.WordTrace]
  refine ⟨147836360945553857657698657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197115147927405143543598209 147836360945553857657698657)
  ·
    refine ⟨110877270709165393243273993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147836360945553857657698657 110877270709165393243273993)
    ·
      refine ⟨83157953031874044932455495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110877270709165393243273993 83157953031874044932455495)
      ·
        refine ⟨124736929547811067398683243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83157953031874044932455495 124736929547811067398683243)
        ·
          refine ⟨187105394321716601098024865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124736929547811067398683243 187105394321716601098024865)
          ·
            refine ⟨140329045741287450823518649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187105394321716601098024865 140329045741287450823518649)
            ·
              refine ⟨105246784305965588117638987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140329045741287450823518649 105246784305965588117638987)
              ·
                refine ⟨157870176458948382176458481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105246784305965588117638987 157870176458948382176458481)
                ·
                  refine ⟨118402632344211286632343861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157870176458948382176458481 118402632344211286632343861)
                  ·
                    refine ⟨11100246782269808121782237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 118402632344211286632343861 11100246782269808121782237)
                    ·
                      refine ⟨4162592543351178045668339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11100246782269808121782237 4162592543351178045668339)
                      ·
                        rfl

theorem cell23_8106620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_8106620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106620 prefixEnd_8106620 := by exact prefixLift 8106620
  have htrace : WordTrace (prefixWord ++ tailWord_8106620) baseStart_8106620 baseEnd_8106620 := by
    simpa [prefixWord, tailWord_8106620, baseEnd_8106620] using wordTrace_append hprefix tailTrace_8106620
  have hstable : (prefixWord ++ tailWord_8106620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106620).length < 2 ^ (prefixWord ++ tailWord_8106620).sum := by decide
  have hdescent : baseEnd_8106620 < baseStart_8106620 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106644 : List Nat := [2, 4, 2, 2, 1, 2, 2, 2, 6]
def baseStart_8106644 : Nat := 118140960795 + 8106644 * 2 ^ 59
def prefixEnd_8106644 : Nat := 4983230072969 + 3 ^ 40 * 8106644 * 2
def baseEnd_8106644 : Nat := 462511651876320661307581

theorem tailTrace_8106644 : CollatzResearch.WordTrace tailWord_8106644 prefixEnd_8106644 462511651876320661307581 := by
  unfold tailWord_8106644
  simp only [CollatzResearch.WordTrace]
  refine ⟨147836798621510383707135493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197115731495347178276180657 147836798621510383707135493)
  ·
    refine ⟨27719399741533196945087905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147836798621510383707135493 27719399741533196945087905)
    ·
      refine ⟨20789549806149897708815929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27719399741533196945087905 20789549806149897708815929)
      ·
        refine ⟨15592162354612423281611947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20789549806149897708815929 15592162354612423281611947)
        ·
          refine ⟨23388243531918634922417921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15592162354612423281611947 23388243531918634922417921)
          ·
            refine ⟨17541182648938976191813441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23388243531918634922417921 17541182648938976191813441)
            ·
              refine ⟨13155886986704232143860081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17541182648938976191813441 13155886986704232143860081)
              ·
                refine ⟨9866915240028174107895061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13155886986704232143860081 9866915240028174107895061)
                ·
                  refine ⟨462511651876320661307581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9866915240028174107895061 462511651876320661307581)
                  ·
                    rfl

theorem cell23_8106644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_8106644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106644 prefixEnd_8106644 := by exact prefixLift 8106644
  have htrace : WordTrace (prefixWord ++ tailWord_8106644) baseStart_8106644 baseEnd_8106644 := by
    simpa [prefixWord, tailWord_8106644, baseEnd_8106644] using wordTrace_append hprefix tailTrace_8106644
  have hstable : (prefixWord ++ tailWord_8106644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106644).length < 2 ^ (prefixWord ++ tailWord_8106644).sum := by decide
  have hdescent : baseEnd_8106644 < baseStart_8106644 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106711 : List Nat := [1, 1, 3, 2, 1, 5, 2, 1, 3, 2, 2]
def baseStart_8106711 : Nat := 118140960795 + 8106711 * 2 ^ 59
def prefixEnd_8106711 : Nat := 4983230072969 + 3 ^ 40 * 8106711 * 2
def baseEnd_8106711 : Nat := 4162639270090737189630421

theorem tailTrace_8106711 : CollatzResearch.WordTrace tailWord_8106711 prefixEnd_8106711 4162639270090737189630421 := by
  unfold tailWord_8106711
  simp only [CollatzResearch.WordTrace]
  refine ⟨295676040933778037856959987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197117360622518691904639991 295676040933778037856959987)
  ·
    refine ⟨443514061400667056785439981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295676040933778037856959987 443514061400667056785439981)
    ·
      refine ⟨166317773025250146294539993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 443514061400667056785439981 166317773025250146294539993)
      ·
        refine ⟨124738329768937609720904995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166317773025250146294539993 124738329768937609720904995)
        ·
          refine ⟨187107494653406414581357493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124738329768937609720904995 187107494653406414581357493)
          ·
            refine ⟨17541327623756851367002265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 187107494653406414581357493 17541327623756851367002265)
            ·
              refine ⟨13155995717817638525251699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17541327623756851367002265 13155995717817638525251699)
              ·
                refine ⟨19733993576726457787877549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13155995717817638525251699 19733993576726457787877549)
                ·
                  refine ⟨7400247591272421670454081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19733993576726457787877549 7400247591272421670454081)
                  ·
                    refine ⟨5550185693454316252840561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7400247591272421670454081 5550185693454316252840561)
                    ·
                      refine ⟨4162639270090737189630421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5550185693454316252840561 4162639270090737189630421)
                      ·
                        rfl

theorem cell23_8106711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 3, 2, 2].length) (baseStart_8106711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106711 prefixEnd_8106711 := by exact prefixLift 8106711
  have htrace : WordTrace (prefixWord ++ tailWord_8106711) baseStart_8106711 baseEnd_8106711 := by
    simpa [prefixWord, tailWord_8106711, baseEnd_8106711] using wordTrace_append hprefix tailTrace_8106711
  have hstable : (prefixWord ++ tailWord_8106711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106711).length < 2 ^ (prefixWord ++ tailWord_8106711).sum := by decide
  have hdescent : baseEnd_8106711 < baseStart_8106711 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106721 : List Nat := [1, 2, 3, 1, 4, 2, 3, 1, 2, 4]
def baseStart_8106721 : Nat := 118140960795 + 8106721 * 2 ^ 59
def prefixEnd_8106721 : Nat := 4983230072969 + 3 ^ 40 * 8106721 * 2
def baseEnd_8106721 : Nat := 1387548134965760716835125

theorem tailTrace_8106721 : CollatzResearch.WordTrace tailWord_8106721 prefixEnd_8106721 1387548134965760716835125 := by
  unfold tailWord_8106721
  simp only [CollatzResearch.WordTrace]
  refine ⟨295676405663741809564824017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197117603775827873043216011 295676405663741809564824017)
  ·
    refine ⟨221757304247806357173618013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295676405663741809564824017 221757304247806357173618013)
    ·
      refine ⟨83158989092927383940106755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221757304247806357173618013 83158989092927383940106755)
      ·
        refine ⟨124738483639391075910160133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83158989092927383940106755 124738483639391075910160133)
        ·
          refine ⟨23388465682385826733155025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124738483639391075910160133 23388465682385826733155025)
          ·
            refine ⟨17541349261789370049866269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23388465682385826733155025 17541349261789370049866269)
            ·
              refine ⟨6578005973171013768699851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17541349261789370049866269 6578005973171013768699851)
              ·
                refine ⟨9867008959756520653049777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6578005973171013768699851 9867008959756520653049777)
                ·
                  refine ⟨7400256719817390489787333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9867008959756520653049777 7400256719817390489787333)
                  ·
                    refine ⟨1387548134965760716835125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7400256719817390489787333 1387548134965760716835125)
                    ·
                      rfl

theorem cell23_8106721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_8106721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106721 prefixEnd_8106721 := by exact prefixLift 8106721
  have htrace : WordTrace (prefixWord ++ tailWord_8106721) baseStart_8106721 baseEnd_8106721 := by
    simpa [prefixWord, tailWord_8106721, baseEnd_8106721] using wordTrace_append hprefix tailTrace_8106721
  have hstable : (prefixWord ++ tailWord_8106721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106721).length < 2 ^ (prefixWord ++ tailWord_8106721).sum := by decide
  have hdescent : baseEnd_8106721 < baseStart_8106721 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106724 : List Nat := [2, 3, 1, 1, 1, 6, 1, 1, 1, 2, 4]
def baseStart_8106724 : Nat := 118140960795 + 8106724 * 2 ^ 59
def prefixEnd_8106724 : Nat := 4983230072969 + 3 ^ 40 * 8106724 * 2
def baseEnd_8106724 : Nat := 4162645945339245638767861

theorem tailTrace_8106724 : CollatzResearch.WordTrace tailWord_8106724 prefixEnd_8106724 4162645945339245638767861 := by
  unfold tailWord_8106724
  simp only [CollatzResearch.WordTrace]
  refine ⟨147838257541365470538591613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197117676721820627384788817 147838257541365470538591613)
  ·
    refine ⟨55439346578012051451971855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147838257541365470538591613 55439346578012051451971855)
    ·
      refine ⟨83159019867018077177957783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55439346578012051451971855 83159019867018077177957783)
      ·
        refine ⟨124738529800527115766936675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83159019867018077177957783 124738529800527115766936675)
        ·
          refine ⟨187107794700790673650405013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124738529800527115766936675 187107794700790673650405013)
          ·
            refine ⟨8770677876599562827362735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 187107794700790673650405013 8770677876599562827362735)
            ·
              refine ⟨13156016814899344241044103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8770677876599562827362735 13156016814899344241044103)
              ·
                refine ⟨19734025222349016361566155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13156016814899344241044103 19734025222349016361566155)
                ·
                  refine ⟨29601037833523524542349233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19734025222349016361566155 29601037833523524542349233)
                  ·
                    refine ⟨22200778375142643406761925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29601037833523524542349233 22200778375142643406761925)
                    ·
                      refine ⟨4162645945339245638767861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22200778375142643406761925 4162645945339245638767861)
                      ·
                        rfl

theorem cell23_8106724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_8106724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106724 prefixEnd_8106724 := by exact prefixLift 8106724
  have htrace : WordTrace (prefixWord ++ tailWord_8106724) baseStart_8106724 baseEnd_8106724 := by
    simpa [prefixWord, tailWord_8106724, baseEnd_8106724] using wordTrace_append hprefix tailTrace_8106724
  have hstable : (prefixWord ++ tailWord_8106724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106724).length < 2 ^ (prefixWord ++ tailWord_8106724).sum := by decide
  have hdescent : baseEnd_8106724 < baseStart_8106724 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106734 : List Nat := [4, 1, 2, 1, 1, 5, 2, 7]
def baseStart_8106734 : Nat := 118140960795 + 8106734 * 2 ^ 59
def prefixEnd_8106734 : Nat := 4983230072969 + 3 ^ 40 * 8106734 * 2
def baseEnd_8106734 : Nat := 154172262227621874060845

theorem tailTrace_8106734 : CollatzResearch.WordTrace tailWord_8106734 prefixEnd_8106734 154172262227621874060845 := by
  unfold tailWord_8106734
  simp only [CollatzResearch.WordTrace]
  refine ⟨36959609976586839098130907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197117919875129808523364837 36959609976586839098130907)
  ·
    refine ⟨55439414964880258647196361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36959609976586839098130907 55439414964880258647196361)
    ·
      refine ⟨41579561223660193985397271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55439414964880258647196361 41579561223660193985397271)
      ·
        refine ⟨62369341835490290978095907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41579561223660193985397271 62369341835490290978095907)
        ·
          refine ⟨93554012753235436467143861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62369341835490290978095907 93554012753235436467143861)
          ·
            refine ⟨8770688695615822168794737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93554012753235436467143861 8770688695615822168794737)
            ·
              refine ⟨6578016521711866626596053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8770688695615822168794737 6578016521711866626596053)
              ·
                refine ⟨154172262227621874060845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6578016521711866626596053 154172262227621874060845)
                ·
                  rfl

theorem cell23_8106734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 7].length) (baseStart_8106734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106734 prefixEnd_8106734 := by exact prefixLift 8106734
  have htrace : WordTrace (prefixWord ++ tailWord_8106734) baseStart_8106734 baseEnd_8106734 := by
    simpa [prefixWord, tailWord_8106734, baseEnd_8106734] using wordTrace_append hprefix tailTrace_8106734
  have hstable : (prefixWord ++ tailWord_8106734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106734).length < 2 ^ (prefixWord ++ tailWord_8106734).sum := by decide
  have hdescent : baseEnd_8106734 < baseStart_8106734 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106824 : List Nat := [2, 1, 3, 1, 1, 3, 3, 4, 5]
def baseStart_8106824 : Nat := 118140960795 + 8106824 * 2 ^ 59
def prefixEnd_8106824 : Nat := 4983230072969 + 3 ^ 40 * 8106824 * 2
def baseEnd_8106824 : Nat := 462521921489410583057489

theorem tailTrace_8106824 : CollatzResearch.WordTrace tailWord_8106824 prefixEnd_8106824 462521921489410583057489 := by
  unfold tailWord_8106824
  simp only [CollatzResearch.WordTrace]
  refine ⟨147840081191184329077911763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197120108254912438770549017 147840081191184329077911763)
  ·
    refine ⟨221760121786776493616867645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147840081191184329077911763 221760121786776493616867645)
    ·
      refine ⟨83160045670041185106325367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221760121786776493616867645 83160045670041185106325367)
      ·
        refine ⟨124740068505061777659488051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83160045670041185106325367 124740068505061777659488051)
        ·
          refine ⟨187110102757592666489232077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124740068505061777659488051 187110102757592666489232077)
          ·
            refine ⟨70166288534097249933462029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187110102757592666489232077 70166288534097249933462029)
            ·
              refine ⟨26312358200286468725048261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70166288534097249933462029 26312358200286468725048261)
              ·
                refine ⟨4933567162553712885946549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26312358200286468725048261 4933567162553712885946549)
                ·
                  refine ⟨462521921489410583057489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4933567162553712885946549 462521921489410583057489)
                  ·
                    rfl

theorem cell23_8106824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 4, 5].length) (baseStart_8106824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106824 prefixEnd_8106824 := by exact prefixLift 8106824
  have htrace : WordTrace (prefixWord ++ tailWord_8106824) baseStart_8106824 baseEnd_8106824 := by
    simpa [prefixWord, tailWord_8106824, baseEnd_8106824] using wordTrace_append hprefix tailTrace_8106824
  have hstable : (prefixWord ++ tailWord_8106824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106824).length < 2 ^ (prefixWord ++ tailWord_8106824).sum := by decide
  have hdescent : baseEnd_8106824 < baseStart_8106824 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106834 : List Nat := [3, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3]
def baseStart_8106834 : Nat := 118140960795 + 8106834 * 2 ^ 59
def prefixEnd_8106834 : Nat := 4983230072969 + 3 ^ 40 * 8106834 * 2
def baseEnd_8106834 : Nat := 4162702428211240208392355

theorem tailTrace_8106834 : CollatzResearch.WordTrace tailWord_8106834 prefixEnd_8106834 4162702428211240208392355 := by
  unfold tailWord_8106834
  simp only [CollatzResearch.WordTrace]
  refine ⟨73920131778083107465921889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197120351408221619909125037 73920131778083107465921889)
  ·
    refine ⟨55440098833562330599441417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73920131778083107465921889 55440098833562330599441417)
    ·
      refine ⟨41580074125171747949581063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55440098833562330599441417 41580074125171747949581063)
      ·
        refine ⟨62370111187757621924371595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41580074125171747949581063 62370111187757621924371595)
        ·
          refine ⟨93555166781636432886557393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62370111187757621924371595 93555166781636432886557393)
          ·
            refine ⟨70166375086227324664918045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93555166781636432886557393 70166375086227324664918045)
            ·
              refine ⟨26312390657335246749344267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70166375086227324664918045 26312390657335246749344267)
              ·
                refine ⟨39468585986002870124016401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26312390657335246749344267 39468585986002870124016401)
                ·
                  refine ⟨29601439489502152593012301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39468585986002870124016401 29601439489502152593012301)
                  ·
                    refine ⟨11100539808563307222379613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29601439489502152593012301 11100539808563307222379613)
                    ·
                      refine ⟨4162702428211240208392355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11100539808563307222379613 4162702428211240208392355)
                      ·
                        rfl

theorem cell23_8106834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_8106834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106834 prefixEnd_8106834 := by exact prefixLift 8106834
  have htrace : WordTrace (prefixWord ++ tailWord_8106834) baseStart_8106834 baseEnd_8106834 := by
    simpa [prefixWord, tailWord_8106834, baseEnd_8106834] using wordTrace_append hprefix tailTrace_8106834
  have hstable : (prefixWord ++ tailWord_8106834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106834).length < 2 ^ (prefixWord ++ tailWord_8106834).sum := by decide
  have hdescent : baseEnd_8106834 < baseStart_8106834 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106837 : List Nat := [1, 3, 2, 2, 2, 1, 2, 2, 1, 7]
def baseStart_8106837 : Nat := 118140960795 + 8106837 * 2 ^ 59
def prefixEnd_8106837 : Nat := 4983230072969 + 3 ^ 40 * 8106837 * 2
def baseEnd_8106837 : Nat := 1387567989551067898884947

theorem tailTrace_8106837 : CollatzResearch.WordTrace tailWord_8106837 prefixEnd_8106837 1387567989551067898884947 := by
  unfold tailWord_8106837
  simp only [CollatzResearch.WordTrace]
  refine ⟨295680636531321561376046765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197120424354214374250697843 295680636531321561376046765)
  ·
    refine ⟨110880238699245585516017537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295680636531321561376046765 110880238699245585516017537)
    ·
      refine ⟨83160179024434189137013153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110880238699245585516017537 83160179024434189137013153)
      ·
        refine ⟨62370134268325641852759865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83160179024434189137013153 62370134268325641852759865)
        ·
          refine ⟨46777600701244231389569899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62370134268325641852759865 46777600701244231389569899)
          ·
            refine ⟨70166401051866347084354849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46777600701244231389569899 70166401051866347084354849)
            ·
              refine ⟨52624800788899760313266137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70166401051866347084354849 52624800788899760313266137)
              ·
                refine ⟨39468600591674820234949603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52624800788899760313266137 39468600591674820234949603)
                ·
                  refine ⟨59202900887512230352424405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39468600591674820234949603 59202900887512230352424405)
                  ·
                    refine ⟨1387567989551067898884947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59202900887512230352424405 1387567989551067898884947)
                    ·
                      rfl

theorem cell23_8106837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_8106837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106837 prefixEnd_8106837 := by exact prefixLift 8106837
  have htrace : WordTrace (prefixWord ++ tailWord_8106837) baseStart_8106837 baseEnd_8106837 := by
    simpa [prefixWord, tailWord_8106837, baseEnd_8106837] using wordTrace_append hprefix tailTrace_8106837
  have hstable : (prefixWord ++ tailWord_8106837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106837).length < 2 ^ (prefixWord ++ tailWord_8106837).sum := by decide
  have hdescent : baseEnd_8106837 < baseStart_8106837 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106877 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 2, 3, 5]
def baseStart_8106877 : Nat := 118140960795 + 8106877 * 2 ^ 59
def prefixEnd_8106877 : Nat := 4983230072969 + 3 ^ 40 * 8106877 * 2
def baseEnd_8106877 : Nat := 4162724507879383540154657

theorem tailTrace_8106877 : CollatzResearch.WordTrace tailWord_8106877 prefixEnd_8106877 4162724507879383540154657 := by
  unfold tailWord_8106877
  simp only [CollatzResearch.WordTrace]
  refine ⟨295682095451176648207502885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197121396967451098805001923 295682095451176648207502885)
  ·
    refine ⟨55440392897095621538906791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295682095451176648207502885 55440392897095621538906791)
    ·
      refine ⟨83160589345643432308360187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55440392897095621538906791 83160589345643432308360187)
      ·
        refine ⟨124740884018465148462540281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83160589345643432308360187 124740884018465148462540281)
        ·
          refine ⟨93555663013848861346905211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124740884018465148462540281 93555663013848861346905211)
          ·
            refine ⟨140333494520773292020357817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93555663013848861346905211 140333494520773292020357817)
            ·
              refine ⟨105250120890579969015268363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140333494520773292020357817 105250120890579969015268363)
              ·
                refine ⟨157875181335869953522902545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105250120890579969015268363 157875181335869953522902545)
                ·
                  refine ⟨118406386001902465142176909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157875181335869953522902545 118406386001902465142176909)
                  ·
                    refine ⟨44402394750713424428316341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118406386001902465142176909 44402394750713424428316341)
                    ·
                      refine ⟨4162724507879383540154657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44402394750713424428316341 4162724507879383540154657)
                      ·
                        rfl

theorem cell23_8106877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_8106877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106877 prefixEnd_8106877 := by exact prefixLift 8106877
  have htrace : WordTrace (prefixWord ++ tailWord_8106877) baseStart_8106877 baseEnd_8106877 := by
    simpa [prefixWord, tailWord_8106877, baseEnd_8106877] using wordTrace_append hprefix tailTrace_8106877
  have hstable : (prefixWord ++ tailWord_8106877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106877).length < 2 ^ (prefixWord ++ tailWord_8106877).sum := by decide
  have hdescent : baseEnd_8106877 < baseStart_8106877 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106914 : List Nat := [3, 3, 1, 2, 2, 1, 1, 2, 8]
def baseStart_8106914 : Nat := 118140960795 + 8106914 * 2 ^ 59
def prefixEnd_8106914 : Nat := 4983230072969 + 3 ^ 40 * 8106914 * 2
def baseEnd_8106914 : Nat := 462527056295955543932443

theorem tailTrace_8106914 : CollatzResearch.WordTrace tailWord_8106914 prefixEnd_8106914 462527056295955543932443 := by
  unfold tailWord_8106914
  simp only [CollatzResearch.WordTrace]
  refine ⟨73920861238010650881649949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197122296634695069017733197 73920861238010650881649949)
  ·
    refine ⟨27720322964253994080618731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73920861238010650881649949 27720322964253994080618731)
    ·
      refine ⟨41580484446380991120928097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27720322964253994080618731 41580484446380991120928097)
      ·
        refine ⟨31185363334785743340696073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41580484446380991120928097 31185363334785743340696073)
        ·
          refine ⟨23389022501089307505522055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31185363334785743340696073 23389022501089307505522055)
          ·
            refine ⟨35083533751633961258283083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23389022501089307505522055 35083533751633961258283083)
            ·
              refine ⟨52625300627450941887424625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35083533751633961258283083 52625300627450941887424625)
              ·
                refine ⟨39468975470588206415568469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52625300627450941887424625 39468975470588206415568469)
                ·
                  refine ⟨462527056295955543932443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39468975470588206415568469 462527056295955543932443)
                  ·
                    rfl

theorem cell23_8106914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_8106914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106914 prefixEnd_8106914 := by exact prefixLift 8106914
  have htrace : WordTrace (prefixWord ++ tailWord_8106914) baseStart_8106914 baseEnd_8106914 := by
    simpa [prefixWord, tailWord_8106914, baseEnd_8106914] using wordTrace_append hprefix tailTrace_8106914
  have hstable : (prefixWord ++ tailWord_8106914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106914).length < 2 ^ (prefixWord ++ tailWord_8106914).sum := by decide
  have hdescent : baseEnd_8106914 < baseStart_8106914 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106948 : List Nat := [2, 3, 3, 3, 1, 1, 1, 3, 6]
def baseStart_8106948 : Nat := 118140960795 + 8106948 * 2 ^ 59
def prefixEnd_8106948 : Nat := 4983230072969 + 3 ^ 40 * 8106948 * 2
def baseEnd_8106948 : Nat := 462528996111761418040759

theorem tailTrace_8106948 : CollatzResearch.WordTrace tailWord_8106948 prefixEnd_8106948 462528996111761418040759 := by
  unfold tailWord_8106948
  simp only [CollatzResearch.WordTrace]
  refine ⟨147842342516959713666668749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197123123355946284888891665 147842342516959713666668749)
  ·
    refine ⟨55440878443859892625000781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147842342516959713666668749 55440878443859892625000781)
    ·
      refine ⟨20790329416447459734375293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55440878443859892625000781 20790329416447459734375293)
      ·
        refine ⟨7796373531167797400390735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20790329416447459734375293 7796373531167797400390735)
        ·
          refine ⟨11694560296751696100586103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7796373531167797400390735 11694560296751696100586103)
          ·
            refine ⟨17541840445127544150879155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11694560296751696100586103 17541840445127544150879155)
            ·
              refine ⟨26312760667691316226318733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17541840445127544150879155 26312760667691316226318733)
              ·
                refine ⟨9867285250384243584869525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26312760667691316226318733 9867285250384243584869525)
                ·
                  refine ⟨462528996111761418040759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9867285250384243584869525 462528996111761418040759)
                  ·
                    rfl

theorem cell23_8106948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 6].length) (baseStart_8106948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106948 prefixEnd_8106948 := by exact prefixLift 8106948
  have htrace : WordTrace (prefixWord ++ tailWord_8106948) baseStart_8106948 baseEnd_8106948 := by
    simpa [prefixWord, tailWord_8106948, baseEnd_8106948] using wordTrace_append hprefix tailTrace_8106948
  have hstable : (prefixWord ++ tailWord_8106948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106948).length < 2 ^ (prefixWord ++ tailWord_8106948).sum := by decide
  have hdescent : baseEnd_8106948 < baseStart_8106948 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106968 : List Nat := [2, 1, 2, 2, 2, 4, 2, 1, 2, 3, 2]
def baseStart_8106968 : Nat := 118140960795 + 8106968 * 2 ^ 59
def prefixEnd_8106968 : Nat := 4983230072969 + 3 ^ 40 * 8106968 * 2
def baseEnd_8106968 : Nat := 4162771234618942684116739

theorem tailTrace_8106968 : CollatzResearch.WordTrace tailWord_8106968 prefixEnd_8106968 4162771234618942684116739 := by
  unfold tailWord_8106968
  simp only [CollatzResearch.WordTrace]
  refine ⟨147842707246923485374532779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197123609662564647166043705 147842707246923485374532779)
  ·
    refine ⟨221764060870385228061799169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147842707246923485374532779 221764060870385228061799169)
    ·
      refine ⟨166323045652788921046349377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221764060870385228061799169 166323045652788921046349377)
      ·
        refine ⟨124742284239591690784762033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166323045652788921046349377 124742284239591690784762033)
        ·
          refine ⟨93556713179693768088571525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124742284239591690784762033 93556713179693768088571525)
          ·
            refine ⟨17541883721192581516607161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93556713179693768088571525 17541883721192581516607161)
            ·
              refine ⟨13156412790894436137455371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17541883721192581516607161 13156412790894436137455371)
              ·
                refine ⟨19734619186341654206183057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13156412790894436137455371 19734619186341654206183057)
                ·
                  refine ⟨14800964389756240654637293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19734619186341654206183057 14800964389756240654637293)
                  ·
                    refine ⟨5550361646158590245488985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14800964389756240654637293 5550361646158590245488985)
                    ·
                      refine ⟨4162771234618942684116739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5550361646158590245488985 4162771234618942684116739)
                      ·
                        rfl

theorem cell23_8106968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 2, 3, 2].length) (baseStart_8106968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106968 prefixEnd_8106968 := by exact prefixLift 8106968
  have htrace : WordTrace (prefixWord ++ tailWord_8106968) baseStart_8106968 baseEnd_8106968 := by
    simpa [prefixWord, tailWord_8106968, baseEnd_8106968] using wordTrace_append hprefix tailTrace_8106968
  have hstable : (prefixWord ++ tailWord_8106968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106968).length < 2 ^ (prefixWord ++ tailWord_8106968).sum := by decide
  have hdescent : baseEnd_8106968 < baseStart_8106968 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8106991 : List Nat := [1, 1, 2, 1, 4, 3, 1, 4, 2, 4]
def baseStart_8106991 : Nat := 118140960795 + 8106991 * 2 ^ 59
def prefixEnd_8106991 : Nat := 4983230072969 + 3 ^ 40 * 8106991 * 2
def baseEnd_8106991 : Nat := 1387594348224665364709711

theorem tailTrace_8106991 : CollatzResearch.WordTrace tailWord_8106991 prefixEnd_8106991 1387594348224665364709711 := by
  unfold tailWord_8106991
  simp only [CollatzResearch.WordTrace]
  refine ⟨295686253372763645677152827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197124168915175763784768551 295686253372763645677152827)
  ·
    refine ⟨443529380059145468515729241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295686253372763645677152827 443529380059145468515729241)
    ·
      refine ⟨332647035044359101386796931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443529380059145468515729241 332647035044359101386796931)
      ·
        refine ⟨498970552566538652080195397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332647035044359101386796931 498970552566538652080195397)
        ·
          refine ⟨93556978606225997265036637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 498970552566538652080195397 93556978606225997265036637)
          ·
            refine ⟨35083866977334748974388739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93556978606225997265036637 35083866977334748974388739)
            ·
              refine ⟨52625800466002123461583109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35083866977334748974388739 52625800466002123461583109)
              ·
                refine ⟨9867337587375398149046833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52625800466002123461583109 9867337587375398149046833)
                ·
                  refine ⟨7400503190531548611785125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9867337587375398149046833 7400503190531548611785125)
                  ·
                    refine ⟨1387594348224665364709711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7400503190531548611785125 1387594348224665364709711)
                    ·
                      rfl

theorem cell23_8106991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 2, 4].length) (baseStart_8106991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8106991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8106991 prefixEnd_8106991 := by exact prefixLift 8106991
  have htrace : WordTrace (prefixWord ++ tailWord_8106991) baseStart_8106991 baseEnd_8106991 := by
    simpa [prefixWord, tailWord_8106991, baseEnd_8106991] using wordTrace_append hprefix tailTrace_8106991
  have hstable : (prefixWord ++ tailWord_8106991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8106991).length < 2 ^ (prefixWord ++ tailWord_8106991).sum := by decide
  have hdescent : baseEnd_8106991 < baseStart_8106991 := by decide
  rcases family_descends (prefixWord ++ tailWord_8106991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107004 : List Nat := [2, 2, 2, 1, 2, 3, 3, 8]
def baseStart_8107004 : Nat := 118140960795 + 8107004 * 2 ^ 59
def prefixEnd_8107004 : Nat := 4983230072969 + 3 ^ 40 * 8107004 * 2
def baseEnd_8107004 : Nat := 154177397034166834935799

theorem tailTrace_8107004 : CollatzResearch.WordTrace tailWord_8107004 prefixEnd_8107004 154177397034166834935799 := by
  unfold tailWord_8107004
  simp only [CollatzResearch.WordTrace]
  refine ⟨147843363760858274448688033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197124485014477699264917377 147843363760858274448688033)
  ·
    refine ⟨110882522820643705836516025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147843363760858274448688033 110882522820643705836516025)
    ·
      refine ⟨83161892115482779377387019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110882522820643705836516025 83161892115482779377387019)
      ·
        refine ⟨124742838173224169066080529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83161892115482779377387019 124742838173224169066080529)
        ·
          refine ⟨93557128629918126799560397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124742838173224169066080529 93557128629918126799560397)
          ·
            refine ⟨35083923236219297549835149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93557128629918126799560397 35083923236219297549835149)
            ·
              refine ⟨13156471213582236581188181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35083923236219297549835149 13156471213582236581188181)
              ·
                refine ⟨154177397034166834935799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13156471213582236581188181 154177397034166834935799)
                ·
                  rfl

theorem cell23_8107004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 8].length) (baseStart_8107004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107004 prefixEnd_8107004 := by exact prefixLift 8107004
  have htrace : WordTrace (prefixWord ++ tailWord_8107004) baseStart_8107004 baseEnd_8107004 := by
    simpa [prefixWord, tailWord_8107004, baseEnd_8107004] using wordTrace_append hprefix tailTrace_8107004
  have hstable : (prefixWord ++ tailWord_8107004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107004).length < 2 ^ (prefixWord ++ tailWord_8107004).sum := by decide
  have hdescent : baseEnd_8107004 < baseStart_8107004 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107026 : List Nat := [3, 2, 5, 1, 1, 1, 2, 3, 1, 1, 3]
def baseStart_8107026 : Nat := 118140960795 + 8107026 * 2 ^ 59
def prefixEnd_8107026 : Nat := 4983230072969 + 3 ^ 40 * 8107026 * 2
def baseEnd_8107026 : Nat := 4162801016496903457191473

theorem tailTrace_8107026 : CollatzResearch.WordTrace tailWord_8107026 prefixEnd_8107026 4162801016496903457191473 := by
  unfold tailWord_8107026
  simp only [CollatzResearch.WordTrace]
  refine ⟨73921882481909211663669233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197125019951757897769784621 73921882481909211663669233)
  ·
    refine ⟨55441411861431908747751925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73921882481909211663669233 55441411861431908747751925)
    ·
      refine ⟨5197632362009241445101743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55441411861431908747751925 5197632362009241445101743)
      ·
        refine ⟨7796448543013862167652615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5197632362009241445101743 7796448543013862167652615)
        ·
          refine ⟨11694672814520793251478923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7796448543013862167652615 11694672814520793251478923)
          ·
            refine ⟨17542009221781189877218385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11694672814520793251478923 17542009221781189877218385)
            ·
              refine ⟨13156506916335892407913789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17542009221781189877218385 13156506916335892407913789)
              ·
                refine ⟨4933690093625959652967671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13156506916335892407913789 4933690093625959652967671)
                ·
                  refine ⟨7400535140438939479451507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4933690093625959652967671 7400535140438939479451507)
                  ·
                    refine ⟨11100802710658409219177261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7400535140438939479451507 11100802710658409219177261)
                    ·
                      refine ⟨4162801016496903457191473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11100802710658409219177261 4162801016496903457191473)
                      ·
                        rfl

theorem cell23_8107026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_8107026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107026 prefixEnd_8107026 := by exact prefixLift 8107026
  have htrace : WordTrace (prefixWord ++ tailWord_8107026) baseStart_8107026 baseEnd_8107026 := by
    simpa [prefixWord, tailWord_8107026, baseEnd_8107026] using wordTrace_append hprefix tailTrace_8107026
  have hstable : (prefixWord ++ tailWord_8107026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107026).length < 2 ^ (prefixWord ++ tailWord_8107026).sum := by decide
  have hdescent : baseEnd_8107026 < baseStart_8107026 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107032 : List Nat := [2, 1, 2, 3, 2, 3, 2, 3, 1, 2, 2]
def baseStart_8107032 : Nat := 118140960795 + 8107032 * 2 ^ 59
def prefixEnd_8107032 : Nat := 4983230072969 + 3 ^ 40 * 8107032 * 2
def baseEnd_8107032 : Nat := 4162804097380830433716445

theorem tailTrace_8107032 : CollatzResearch.WordTrace tailWord_8107032 prefixEnd_8107032 4162804097380830433716445 := by
  unfold tailWord_8107032
  simp only [CollatzResearch.WordTrace]
  refine ⟨147843874382807554839697675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197125165843743406452930233 147843874382807554839697675)
  ·
    refine ⟨221765811574211332259546513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147843874382807554839697675 221765811574211332259546513)
    ·
      refine ⟨166324358680658499194659885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221765811574211332259546513 166324358680658499194659885)
      ·
        refine ⟨62371634505246937197997457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166324358680658499194659885 62371634505246937197997457)
        ·
          refine ⟨46778725878935202898498093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62371634505246937197997457 46778725878935202898498093)
          ·
            refine ⟨17542022204600701086936785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46778725878935202898498093 17542022204600701086936785)
            ·
              refine ⟨13156516653450525815202589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17542022204600701086936785 13156516653450525815202589)
              ·
                refine ⟨4933693745043947180700971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13156516653450525815202589 4933693745043947180700971)
                ·
                  refine ⟨7400540617565920771051457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4933693745043947180700971 7400540617565920771051457)
                  ·
                    refine ⟨5550405463174440578288593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7400540617565920771051457 5550405463174440578288593)
                    ·
                      refine ⟨4162804097380830433716445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5550405463174440578288593 4162804097380830433716445)
                      ·
                        rfl

theorem cell23_8107032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_8107032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107032 prefixEnd_8107032 := by exact prefixLift 8107032
  have htrace : WordTrace (prefixWord ++ tailWord_8107032) baseStart_8107032 baseEnd_8107032 := by
    simpa [prefixWord, tailWord_8107032, baseEnd_8107032] using wordTrace_append hprefix tailTrace_8107032
  have hstable : (prefixWord ++ tailWord_8107032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107032).length < 2 ^ (prefixWord ++ tailWord_8107032).sum := by decide
  have hdescent : baseEnd_8107032 < baseStart_8107032 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107078 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_8107078 : Nat := 118140960795 + 8107078 * 2 ^ 59
def prefixEnd_8107078 : Nat := 4983230072969 + 3 ^ 40 * 8107078 * 2
def baseEnd_8107078 : Nat := 4162827717490937253741233

theorem tailTrace_8107078 : CollatzResearch.WordTrace tailWord_8107078 prefixEnd_8107078 4162827717490937253741233 := by
  unfold tailWord_8107078
  simp only [CollatzResearch.WordTrace]
  refine ⟨9240294578857764360486559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 197126284348965639690379925 9240294578857764360486559)
  ·
    refine ⟨13860441868286646540729839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9240294578857764360486559 13860441868286646540729839)
    ·
      refine ⟨20790662802429969811094759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13860441868286646540729839 20790662802429969811094759)
      ·
        refine ⟨31185994203644954716642139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20790662802429969811094759 31185994203644954716642139)
        ·
          refine ⟨46778991305467432074963209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31185994203644954716642139 46778991305467432074963209)
          ·
            refine ⟨35084243479100574056222407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46778991305467432074963209 35084243479100574056222407)
            ·
              refine ⟨52626365218650861084333611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35084243479100574056222407 52626365218650861084333611)
              ·
                refine ⟨78939547827976291626500417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52626365218650861084333611 78939547827976291626500417)
                ·
                  refine ⟨59204660870982218719875313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78939547827976291626500417 59204660870982218719875313)
                  ·
                    refine ⟨44403495653236664039906485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59204660870982218719875313 44403495653236664039906485)
                    ·
                      refine ⟨4162827717490937253741233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44403495653236664039906485 4162827717490937253741233)
                      ·
                        rfl

theorem cell23_8107078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_8107078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107078 prefixEnd_8107078 := by exact prefixLift 8107078
  have htrace : WordTrace (prefixWord ++ tailWord_8107078) baseStart_8107078 baseEnd_8107078 := by
    simpa [prefixWord, tailWord_8107078, baseEnd_8107078] using wordTrace_append hprefix tailTrace_8107078
  have hstable : (prefixWord ++ tailWord_8107078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107078).length < 2 ^ (prefixWord ++ tailWord_8107078).sum := by decide
  have hdescent : baseEnd_8107078 < baseStart_8107078 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107104 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 7]
def baseStart_8107104 : Nat := 118140960795 + 8107104 * 2 ^ 59
def prefixEnd_8107104 : Nat := 4983230072969 + 3 ^ 40 * 8107104 * 2
def baseEnd_8107104 : Nat := 4162841067987954152016113

theorem tailTrace_8107104 : CollatzResearch.WordTrace tailWord_8107104 prefixEnd_8107104 4162841067987954152016113 := by
  unfold tailWord_8107104
  simp only [CollatzResearch.WordTrace]
  refine ⟨147845187410677132988008183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197126916547569510650677577 147845187410677132988008183)
  ·
    refine ⟨221767781116015699482012275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147845187410677132988008183 221767781116015699482012275)
    ·
      refine ⟨332651671674023549223018413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221767781116015699482012275 332651671674023549223018413)
      ·
        refine ⟨124744376877758830958631905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332651671674023549223018413 124744376877758830958631905)
        ·
          refine ⟨93558282658319123218973929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124744376877758830958631905 93558282658319123218973929)
          ·
            refine ⟨70168711993739342414230447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93558282658319123218973929 70168711993739342414230447)
            ·
              refine ⟨105253067990609013621345671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70168711993739342414230447 105253067990609013621345671)
              ·
                refine ⟨157879601985913520432018507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105253067990609013621345671 157879601985913520432018507)
                ·
                  refine ⟨236819402978870280648027761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157879601985913520432018507 236819402978870280648027761)
                  ·
                    refine ⟨177614552234152710486020821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 236819402978870280648027761 177614552234152710486020821)
                    ·
                      refine ⟨4162841067987954152016113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 177614552234152710486020821 4162841067987954152016113)
                      ·
                        rfl

theorem cell23_8107104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_8107104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107104 prefixEnd_8107104 := by exact prefixLift 8107104
  have htrace : WordTrace (prefixWord ++ tailWord_8107104) baseStart_8107104 baseEnd_8107104 := by
    simpa [prefixWord, tailWord_8107104, baseEnd_8107104] using wordTrace_append hprefix tailTrace_8107104
  have hstable : (prefixWord ++ tailWord_8107104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107104).length < 2 ^ (prefixWord ++ tailWord_8107104).sum := by decide
  have hdescent : baseEnd_8107104 < baseStart_8107104 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107111 : List Nat := [1, 1, 5, 1, 1, 3, 3, 1, 7]
def baseStart_8107111 : Nat := 118140960795 + 8107111 * 2 ^ 59
def prefixEnd_8107111 : Nat := 4983230072969 + 3 ^ 40 * 8107111 * 2
def baseEnd_8107111 : Nat := 462538295816948402736509

theorem tailTrace_8107111 : CollatzResearch.WordTrace tailWord_8107111 prefixEnd_8107111 462538295816948402736509 := by
  unfold tailWord_8107111
  simp only [CollatzResearch.WordTrace]
  refine ⟨295690630132328906171521187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197127086754885937447680791 295690630132328906171521187)
  ·
    refine ⟨443535945198493359257281781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295690630132328906171521187 443535945198493359257281781)
    ·
      refine ⟨41581494862358752430370167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 443535945198493359257281781 41581494862358752430370167)
      ·
        refine ⟨62372242293538128645555251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41581494862358752430370167 62372242293538128645555251)
        ·
          refine ⟨93558363440307192968332877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62372242293538128645555251 93558363440307192968332877)
          ·
            refine ⟨35084386290115197363124829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93558363440307192968332877 35084386290115197363124829)
            ·
              refine ⟨13156644858793199011171811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35084386290115197363124829 13156644858793199011171811)
              ·
                refine ⟨19734967288189798516757717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13156644858793199011171811 19734967288189798516757717)
                ·
                  refine ⟨462538295816948402736509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19734967288189798516757717 462538295816948402736509)
                  ·
                    rfl

theorem cell23_8107111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 7].length) (baseStart_8107111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107111 prefixEnd_8107111 := by exact prefixLift 8107111
  have htrace : WordTrace (prefixWord ++ tailWord_8107111) baseStart_8107111 baseEnd_8107111 := by
    simpa [prefixWord, tailWord_8107111, baseEnd_8107111] using wordTrace_append hprefix tailTrace_8107111
  have hstable : (prefixWord ++ tailWord_8107111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107111).length < 2 ^ (prefixWord ++ tailWord_8107111).sum := by decide
  have hdescent : baseEnd_8107111 < baseStart_8107111 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107162 : List Nat := [3, 1, 1, 5, 1, 3, 2, 2, 5]
def baseStart_8107162 : Nat := 118140960795 + 8107162 * 2 ^ 59
def prefixEnd_8107162 : Nat := 4983230072969 + 3 ^ 40 * 8107162 * 2
def baseEnd_8107162 : Nat := 462541205540657213898983

theorem tailTrace_8107162 : CollatzResearch.WordTrace tailWord_8107162 prefixEnd_8107162 462541205540657213898983 := by
  unfold tailWord_8107162
  simp only [CollatzResearch.WordTrace]
  refine ⟨73923122563786035470406935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197128326836762761254418493 73923122563786035470406935)
  ·
    refine ⟨110884683845679053205610403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73923122563786035470406935 110884683845679053205610403)
    ·
      refine ⟨166327025768518579808415605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110884683845679053205610403 166327025768518579808415605)
      ·
        refine ⟨15593158665798616857038963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 166327025768518579808415605 15593158665798616857038963)
        ·
          refine ⟨23389737998697925285558445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15593158665798616857038963 23389737998697925285558445)
          ·
            refine ⟨8771151749511721982084417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23389737998697925285558445 8771151749511721982084417)
            ·
              refine ⟨6578363812133791486563313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8771151749511721982084417 6578363812133791486563313)
              ·
                refine ⟨4933772859100343614922485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6578363812133791486563313 4933772859100343614922485)
                ·
                  refine ⟨462541205540657213898983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4933772859100343614922485 462541205540657213898983)
                  ·
                    rfl

theorem cell23_8107162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 2, 5].length) (baseStart_8107162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107162 prefixEnd_8107162 := by exact prefixLift 8107162
  have htrace : WordTrace (prefixWord ++ tailWord_8107162) baseStart_8107162 baseEnd_8107162 := by
    simpa [prefixWord, tailWord_8107162, baseEnd_8107162] using wordTrace_append hprefix tailTrace_8107162
  have hstable : (prefixWord ++ tailWord_8107162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107162).length < 2 ^ (prefixWord ++ tailWord_8107162).sum := by decide
  have hdescent : baseEnd_8107162 < baseStart_8107162 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107171 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 7, 4]
def baseStart_8107171 : Nat := 118140960795 + 8107171 * 2 ^ 59
def prefixEnd_8107171 : Nat := 4983230072969 + 3 ^ 40 * 8107171 * 2
def baseEnd_8107171 : Nat := 1387625157063935129959435

theorem tailTrace_8107171 : CollatzResearch.WordTrace tailWord_8107171 prefixEnd_8107171 1387625157063935129959435 := by
  unfold tailWord_8107171
  simp only [CollatzResearch.WordTrace]
  refine ⟨295692818512111536418705367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197128545674741024279136911 295692818512111536418705367)
  ·
    refine ⟨443539227768167304628058051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295692818512111536418705367 443539227768167304628058051)
    ·
      refine ⟨665308841652250956942087077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443539227768167304628058051 665308841652250956942087077)
      ·
        refine ⟨124745407809797054426641327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 665308841652250956942087077 124745407809797054426641327)
        ·
          refine ⟨187118111714695581639961991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124745407809797054426641327 187118111714695581639961991)
          ·
            refine ⟨280677167572043372459942987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187118111714695581639961991 280677167572043372459942987)
            ·
              refine ⟨421015751358065058689914481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280677167572043372459942987 421015751358065058689914481)
              ·
                refine ⟨315761813518548794017435861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 421015751358065058689914481 315761813518548794017435861)
                ·
                  refine ⟨7400667504340987359783653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 315761813518548794017435861 7400667504340987359783653)
                  ·
                    refine ⟨1387625157063935129959435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7400667504340987359783653 1387625157063935129959435)
                    ·
                      rfl

theorem cell23_8107171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 7, 4].length) (baseStart_8107171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107171 prefixEnd_8107171 := by exact prefixLift 8107171
  have htrace : WordTrace (prefixWord ++ tailWord_8107171) baseStart_8107171 baseEnd_8107171 := by
    simpa [prefixWord, tailWord_8107171, baseEnd_8107171] using wordTrace_append hprefix tailTrace_8107171
  have hstable : (prefixWord ++ tailWord_8107171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107171).length < 2 ^ (prefixWord ++ tailWord_8107171).sum := by decide
  have hdescent : baseEnd_8107171 < baseStart_8107171 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107231 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 5, 5]
def baseStart_8107231 : Nat := 118140960795 + 8107231 * 2 ^ 59
def prefixEnd_8107231 : Nat := 4983230072969 + 3 ^ 40 * 8107231 * 2
def baseEnd_8107231 : Nat := 1387635426677025051709343

theorem tailTrace_8107231 : CollatzResearch.WordTrace tailWord_8107231 prefixEnd_8107231 1387635426677025051709343 := by
  unfold tailWord_8107231
  simp only [CollatzResearch.WordTrace]
  refine ⟨295695006891894166665889547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197130004594596111110593031 295695006891894166665889547)
  ·
    refine ⟨443542510337841249998834321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295695006891894166665889547 443542510337841249998834321)
    ·
      refine ⟨332656882753380937499125741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443542510337841249998834321 332656882753380937499125741)
      ·
        refine ⟨124746331032517851562172153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332656882753380937499125741 124746331032517851562172153)
        ·
          refine ⟨93559748274388388671629115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124746331032517851562172153 93559748274388388671629115)
          ·
            refine ⟨140339622411582583007443673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93559748274388388671629115 140339622411582583007443673)
            ·
              refine ⟨105254716808686937255582755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140339622411582583007443673 105254716808686937255582755)
              ·
                refine ⟨157882075213030405883374133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105254716808686937255582755 157882075213030405883374133)
                ·
                  refine ⟨14801444551221600551566325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157882075213030405883374133 14801444551221600551566325)
                  ·
                    refine ⟨1387635426677025051709343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14801444551221600551566325 1387635426677025051709343)
                    ·
                      rfl

theorem cell23_8107231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 5].length) (baseStart_8107231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107231 prefixEnd_8107231 := by exact prefixLift 8107231
  have htrace : WordTrace (prefixWord ++ tailWord_8107231) baseStart_8107231 baseEnd_8107231 := by
    simpa [prefixWord, tailWord_8107231, baseEnd_8107231] using wordTrace_append hprefix tailTrace_8107231
  have hstable : (prefixWord ++ tailWord_8107231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107231).length < 2 ^ (prefixWord ++ tailWord_8107231).sum := by decide
  have hdescent : baseEnd_8107231 < baseStart_8107231 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107272 : List Nat := [2, 1, 3, 2, 4, 1, 1, 2, 2, 3, 2]
def baseStart_8107272 : Nat := 118140960795 + 8107272 * 2 ^ 59
def prefixEnd_8107272 : Nat := 4983230072969 + 3 ^ 40 * 8107272 * 2
def baseEnd_8107272 : Nat := 4162927332737909494715341

theorem tailTrace_8107272 : CollatzResearch.WordTrace tailWord_8107272 prefixEnd_8107272 4162927332737909494715341 := by
  unfold tailWord_8107272
  simp only [CollatzResearch.WordTrace]
  refine ⟨147848251142372815334066035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197131001523163753778754713 147848251142372815334066035)
  ·
    refine ⟨221772376713559223001099053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147848251142372815334066035 221772376713559223001099053)
    ·
      refine ⟨83164641267584708625412145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221772376713559223001099053 83164641267584708625412145)
      ·
        refine ⟨62373480950688531469059109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83164641267584708625412145 62373480950688531469059109)
        ·
          refine ⟨11695027678254099650448583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62373480950688531469059109 11695027678254099650448583)
          ·
            refine ⟨17542541517381149475672875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11695027678254099650448583 17542541517381149475672875)
            ·
              refine ⟨26313812276071724213509313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17542541517381149475672875 26313812276071724213509313)
              ·
                refine ⟨19735359207053793160131985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26313812276071724213509313 19735359207053793160131985)
                ·
                  refine ⟨14801519405290344870098989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19735359207053793160131985 14801519405290344870098989)
                  ·
                    refine ⟨5550569776983879326287121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14801519405290344870098989 5550569776983879326287121)
                    ·
                      refine ⟨4162927332737909494715341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5550569776983879326287121 4162927332737909494715341)
                      ·
                        rfl

theorem cell23_8107272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_8107272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107272 prefixEnd_8107272 := by exact prefixLift 8107272
  have htrace : WordTrace (prefixWord ++ tailWord_8107272) baseStart_8107272 baseEnd_8107272 := by
    simpa [prefixWord, tailWord_8107272, baseEnd_8107272] using wordTrace_append hprefix tailTrace_8107272
  have hstable : (prefixWord ++ tailWord_8107272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107272).length < 2 ^ (prefixWord ++ tailWord_8107272).sum := by decide
  have hdescent : baseEnd_8107272 < baseStart_8107272 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107281 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 6]
def baseStart_8107281 : Nat := 118140960795 + 8107281 * 2 ^ 59
def prefixEnd_8107281 : Nat := 4983230072969 + 3 ^ 40 * 8107281 * 2
def baseEnd_8107281 : Nat := 4162931954063799959502799

theorem tailTrace_8107281 : CollatzResearch.WordTrace tailWord_8107281 prefixEnd_8107281 4162931954063799959502799 := by
  unfold tailWord_8107281
  simp only [CollatzResearch.WordTrace]
  refine ⟨295696830541713025205209697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197131220361142016803473131 295696830541713025205209697)
  ·
    refine ⟨221772622906284768903907273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295696830541713025205209697 221772622906284768903907273)
    ·
      refine ⟨166329467179713576677930455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221772622906284768903907273 166329467179713576677930455)
      ·
        refine ⟨249494200769570365016895683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166329467179713576677930455 249494200769570365016895683)
        ·
          refine ⟨374241301154355547525343525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249494200769570365016895683 374241301154355547525343525)
          ·
            refine ⟨70170243966441665161001911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 374241301154355547525343525 70170243966441665161001911)
            ·
              refine ⟨105255365949662497741502867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70170243966441665161001911 105255365949662497741502867)
              ·
                refine ⟨157883048924493746612254301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105255365949662497741502867 157883048924493746612254301)
                ·
                  refine ⟨59206143346685154979595363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157883048924493746612254301 59206143346685154979595363)
                  ·
                    refine ⟨88809215020027732469393045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59206143346685154979595363 88809215020027732469393045)
                    ·
                      refine ⟨4162931954063799959502799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88809215020027732469393045 4162931954063799959502799)
                      ·
                        rfl

theorem cell23_8107281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_8107281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107281 prefixEnd_8107281 := by exact prefixLift 8107281
  have htrace : WordTrace (prefixWord ++ tailWord_8107281) baseStart_8107281 baseEnd_8107281 := by
    simpa [prefixWord, tailWord_8107281, baseEnd_8107281] using wordTrace_append hprefix tailTrace_8107281
  have hstable : (prefixWord ++ tailWord_8107281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107281).length < 2 ^ (prefixWord ++ tailWord_8107281).sum := by decide
  have hdescent : baseEnd_8107281 < baseStart_8107281 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107288 : List Nat := [2, 1, 2, 3, 1, 3, 2, 2, 1, 1, 5]
def baseStart_8107288 : Nat := 118140960795 + 8107288 * 2 ^ 59
def prefixEnd_8107288 : Nat := 4983230072969 + 3 ^ 40 * 8107288 * 2
def baseEnd_8107288 : Nat := 4162935548428381432115267

theorem tailTrace_8107288 : CollatzResearch.WordTrace tailWord_8107288 prefixEnd_8107288 4162935548428381432115267 := by
  unfold tailWord_8107288
  simp only [CollatzResearch.WordTrace]
  refine ⟨147848542926343832700357259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197131390568458443600476345 147848542926343832700357259)
  ·
    refine ⟨221772814389515749050535889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147848542926343832700357259 221772814389515749050535889)
    ·
      refine ⟨166329610792136811787901917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221772814389515749050535889 166329610792136811787901917)
      ·
        refine ⟨62373604047051304420463219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166329610792136811787901917 62373604047051304420463219)
        ·
          refine ⟨93560406070576956630694829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62373604047051304420463219 93560406070576956630694829)
          ·
            refine ⟨35085152276466358736510561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93560406070576956630694829 35085152276466358736510561)
            ·
              refine ⟨26313864207349769052382921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35085152276466358736510561 26313864207349769052382921)
              ·
                refine ⟨19735398155512326789287191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26313864207349769052382921 19735398155512326789287191)
                ·
                  refine ⟨29603097233268490183930787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19735398155512326789287191 29603097233268490183930787)
                  ·
                    refine ⟨44404645849902735275896181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29603097233268490183930787 44404645849902735275896181)
                    ·
                      refine ⟨4162935548428381432115267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44404645849902735275896181 4162935548428381432115267)
                      ·
                        rfl

theorem cell23_8107288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_8107288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107288 prefixEnd_8107288 := by exact prefixLift 8107288
  have htrace : WordTrace (prefixWord ++ tailWord_8107288) baseStart_8107288 baseEnd_8107288 := by
    simpa [prefixWord, tailWord_8107288, baseEnd_8107288] using wordTrace_append hprefix tailTrace_8107288
  have hstable : (prefixWord ++ tailWord_8107288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107288).length < 2 ^ (prefixWord ++ tailWord_8107288).sum := by decide
  have hdescent : baseEnd_8107288 < baseStart_8107288 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107322 : List Nat := [3, 1, 1, 1, 4, 1, 5, 1, 1, 2, 3]
def baseStart_8107322 : Nat := 118140960795 + 8107322 * 2 ^ 59
def prefixEnd_8107322 : Nat := 4983230072969 + 3 ^ 40 * 8107322 * 2
def baseEnd_8107322 : Nat := 4162953006770634299090111

theorem tailTrace_8107322 : CollatzResearch.WordTrace tailWord_8107322 prefixEnd_8107322 4162953006770634299090111 := by
  unfold tailWord_8107322
  simp only [CollatzResearch.WordTrace]
  refine ⟨73924581483641122301863055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197132217289709659471634813 73924581483641122301863055)
  ·
    refine ⟨110886872225461683452794583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73924581483641122301863055 110886872225461683452794583)
    ·
      refine ⟨166330308338192525179191875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110886872225461683452794583 166330308338192525179191875)
      ·
        refine ⟨249495462507288787768787813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166330308338192525179191875 249495462507288787768787813)
        ·
          refine ⟨46780399220116647706647715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249495462507288787768787813 46780399220116647706647715)
          ·
            refine ⟨70170598830174971559971573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46780399220116647706647715 70170598830174971559971573)
            ·
              refine ⟨6578493640328903583747335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70170598830174971559971573 6578493640328903583747335)
              ·
                refine ⟨9867740460493355375621003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6578493640328903583747335 9867740460493355375621003)
                ·
                  refine ⟨14801610690740033063431505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9867740460493355375621003 14801610690740033063431505)
                  ·
                    refine ⟨11101208018055024797573629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14801610690740033063431505 11101208018055024797573629)
                    ·
                      refine ⟨4162953006770634299090111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11101208018055024797573629 4162953006770634299090111)
                      ·
                        rfl

theorem cell23_8107322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 1, 2, 3].length) (baseStart_8107322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107322 prefixEnd_8107322 := by exact prefixLift 8107322
  have htrace : WordTrace (prefixWord ++ tailWord_8107322) baseStart_8107322 baseEnd_8107322 := by
    simpa [prefixWord, tailWord_8107322, baseEnd_8107322] using wordTrace_append hprefix tailTrace_8107322
  have hstable : (prefixWord ++ tailWord_8107322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107322).length < 2 ^ (prefixWord ++ tailWord_8107322).sum := by decide
  have hdescent : baseEnd_8107322 < baseStart_8107322 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107325 : List Nat := [1, 4, 1, 5, 2, 10]
def baseStart_8107325 : Nat := 118140960795 + 8107325 * 2 ^ 59
def prefixEnd_8107325 : Nat := 4983230072969 + 3 ^ 40 * 8107325 * 2
def baseEnd_8107325 : Nat := 17131500194290525873879

theorem tailTrace_8107325 : CollatzResearch.WordTrace tailWord_8107325 prefixEnd_8107325 17131500194290525873879 := by
  unfold tailWord_8107325
  simp only [CollatzResearch.WordTrace]
  refine ⟨295698435353553620719811429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197132290235702413813207619 295698435353553620719811429)
  ·
    refine ⟨55443456628791303884964643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 295698435353553620719811429 55443456628791303884964643)
    ·
      refine ⟨83165184943186955827446965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55443456628791303884964643 83165184943186955827446965)
      ·
        refine ⟨7796736088423777108823153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83165184943186955827446965 7796736088423777108823153)
        ·
          refine ⟨5847552066317832831617365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7796736088423777108823153 5847552066317832831617365)
          ·
            refine ⟨17131500194290525873879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5847552066317832831617365 17131500194290525873879)
            ·
              rfl

theorem cell23_8107325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 10].length) (baseStart_8107325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107325 prefixEnd_8107325 := by exact prefixLift 8107325
  have htrace : WordTrace (prefixWord ++ tailWord_8107325) baseStart_8107325 baseEnd_8107325 := by
    simpa [prefixWord, tailWord_8107325, baseEnd_8107325] using wordTrace_append hprefix tailTrace_8107325
  have hstable : (prefixWord ++ tailWord_8107325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107325).length < 2 ^ (prefixWord ++ tailWord_8107325).sum := by decide
  have hdescent : baseEnd_8107325 < baseStart_8107325 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107345 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 5, 3, 2]
def baseStart_8107345 : Nat := 118140960795 + 8107345 * 2 ^ 59
def prefixEnd_8107345 : Nat := 4983230072969 + 3 ^ 40 * 8107345 * 2
def baseEnd_8107345 : Nat := 4162964816825687709102505

theorem tailTrace_8107345 : CollatzResearch.WordTrace tailWord_8107345 prefixEnd_8107345 4162964816825687709102505 := by
  unfold tailWord_8107345
  simp only [CollatzResearch.WordTrace]
  refine ⟨295699164813481164135539489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197132776542320776090359659 295699164813481164135539489)
  ·
    refine ⟨221774373610110873101654617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295699164813481164135539489 221774373610110873101654617)
    ·
      refine ⟨166330780207583154826240963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221774373610110873101654617 166330780207583154826240963)
      ·
        refine ⟨249496170311374732239361445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166330780207583154826240963 249496170311374732239361445)
        ·
          refine ⟨46780531933382762294880271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249496170311374732239361445 46780531933382762294880271)
          ·
            refine ⟨70170797900074143442320407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46780531933382762294880271 70170797900074143442320407)
            ·
              refine ⟨105256196850111215163480611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70170797900074143442320407 105256196850111215163480611)
              ·
                refine ⟨157884295275166822745220917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105256196850111215163480611 157884295275166822745220917)
                ·
                  refine ⟨14801652682046889632364461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157884295275166822745220917 14801652682046889632364461)
                  ·
                    refine ⟨5550619755767583612136673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14801652682046889632364461 5550619755767583612136673)
                    ·
                      refine ⟨4162964816825687709102505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5550619755767583612136673 4162964816825687709102505)
                      ·
                        rfl

theorem cell23_8107345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 3, 2].length) (baseStart_8107345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107345 prefixEnd_8107345 := by exact prefixLift 8107345
  have htrace : WordTrace (prefixWord ++ tailWord_8107345) baseStart_8107345 baseEnd_8107345 := by
    simpa [prefixWord, tailWord_8107345, baseEnd_8107345] using wordTrace_append hprefix tailTrace_8107345
  have hstable : (prefixWord ++ tailWord_8107345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107345).length < 2 ^ (prefixWord ++ tailWord_8107345).sum := by decide
  have hdescent : baseEnd_8107345 < baseStart_8107345 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107362 : List Nat := [3, 3, 2, 1, 1, 1, 1, 3, 3, 3, 2]
def baseStart_8107362 : Nat := 118140960795 + 8107362 * 2 ^ 59
def prefixEnd_8107362 : Nat := 4983230072969 + 3 ^ 40 * 8107362 * 2
def baseEnd_8107362 : Nat := 4162973545996814142589927

theorem tailTrace_8107362 : CollatzResearch.WordTrace tailWord_8107362 prefixEnd_8107362 4162973545996814142589927 := by
  unfold tailWord_8107362
  simp only [CollatzResearch.WordTrace]
  refine ⟨73924946213604894009727085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197133189902946384025938893 73924946213604894009727085)
  ·
    refine ⟨27721854830101835253647657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73924946213604894009727085 27721854830101835253647657)
    ·
      refine ⟨20791391122576376440235743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27721854830101835253647657 20791391122576376440235743)
      ·
        refine ⟨31187086683864564660353615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20791391122576376440235743 31187086683864564660353615)
        ·
          refine ⟨46780630025796846990530423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31187086683864564660353615 46780630025796846990530423)
          ·
            refine ⟨70170945038695270485795635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46780630025796846990530423 70170945038695270485795635)
            ·
              refine ⟨105256417558042905728693453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70170945038695270485795635 105256417558042905728693453)
              ·
                refine ⟨39471156584266089648260045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105256417558042905728693453 39471156584266089648260045)
                ·
                  refine ⟨14801683719099783618097517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39471156584266089648260045 14801683719099783618097517)
                  ·
                    refine ⟨5550631394662418856786569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14801683719099783618097517 5550631394662418856786569)
                    ·
                      refine ⟨4162973545996814142589927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5550631394662418856786569 4162973545996814142589927)
                      ·
                        rfl

theorem cell23_8107362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_8107362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107362 prefixEnd_8107362 := by exact prefixLift 8107362
  have htrace : WordTrace (prefixWord ++ tailWord_8107362) baseStart_8107362 baseEnd_8107362 := by
    simpa [prefixWord, tailWord_8107362, baseEnd_8107362] using wordTrace_append hprefix tailTrace_8107362
  have hstable : (prefixWord ++ tailWord_8107362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107362).length < 2 ^ (prefixWord ++ tailWord_8107362).sum := by decide
  have hdescent : baseEnd_8107362 < baseStart_8107362 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107375 : List Nat := [1, 1, 2, 1, 3, 1, 3, 4, 1, 4, 2]
def baseStart_8107375 : Nat := 118140960795 + 8107375 * 2 ^ 59
def prefixEnd_8107375 : Nat := 4983230072969 + 3 ^ 40 * 8107375 * 2
def baseEnd_8107375 : Nat := 4162980221245322591727367

theorem tailTrace_8107375 : CollatzResearch.WordTrace tailWord_8107375 prefixEnd_8107375 4162980221245322591727367 := by
  unfold tailWord_8107375
  simp only [CollatzResearch.WordTrace]
  refine ⟨295700259003372479259131579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197133506002248319506087719 295700259003372479259131579)
  ·
    refine ⟨443550388505058718888697369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 295700259003372479259131579 443550388505058718888697369)
    ·
      refine ⟨332662791378794039166523027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 443550388505058718888697369 332662791378794039166523027)
      ·
        refine ⟨498994187068191058749784541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332662791378794039166523027 498994187068191058749784541)
        ·
          refine ⟨187122820150571647031169203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 498994187068191058749784541 187122820150571647031169203)
          ·
            refine ⟨280684230225857470546753805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187122820150571647031169203 280684230225857470546753805)
            ·
              refine ⟨105256586334696551455032677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280684230225857470546753805 105256586334696551455032677)
              ·
                refine ⟨19735609937755603397818627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105256586334696551455032677 19735609937755603397818627)
                ·
                  refine ⟨29603414906633405096727941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19735609937755603397818627 29603414906633405096727941)
                  ·
                    refine ⟨5550640294993763455636489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29603414906633405096727941 5550640294993763455636489)
                    ·
                      refine ⟨4162980221245322591727367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5550640294993763455636489 4162980221245322591727367)
                      ·
                        rfl

theorem cell23_8107375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 4, 2].length) (baseStart_8107375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107375 prefixEnd_8107375 := by exact prefixLift 8107375
  have htrace : WordTrace (prefixWord ++ tailWord_8107375) baseStart_8107375 baseEnd_8107375 := by
    simpa [prefixWord, tailWord_8107375, baseEnd_8107375] using wordTrace_append hprefix tailTrace_8107375
  have hstable : (prefixWord ++ tailWord_8107375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107375).length < 2 ^ (prefixWord ++ tailWord_8107375).sum := by decide
  have hdescent : baseEnd_8107375 < baseStart_8107375 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107378 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 1, 3, 5]
def baseStart_8107378 : Nat := 118140960795 + 8107378 * 2 ^ 59
def prefixEnd_8107378 : Nat := 4983230072969 + 3 ^ 40 * 8107378 * 2
def baseEnd_8107378 : Nat := 4162981761687286079989853

theorem tailTrace_8107378 : CollatzResearch.WordTrace tailWord_8107378 prefixEnd_8107378 4162981761687286079989853 := by
  unfold tailWord_8107378
  simp only [CollatzResearch.WordTrace]
  refine ⟨73925092105590402692872697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197133578948241073847660525 73925092105590402692872697)
  ·
    refine ⟨55443819079192802019654523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73925092105590402692872697 55443819079192802019654523)
    ·
      refine ⟨83165728618789203029481785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55443819079192802019654523 83165728618789203029481785)
      ·
        refine ⟨62374296464091902272111339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83165728618789203029481785 62374296464091902272111339)
        ·
          refine ⟨93561444696137853408167009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62374296464091902272111339 93561444696137853408167009)
          ·
            refine ⟨70171083522103390056125257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93561444696137853408167009 70171083522103390056125257)
            ·
              refine ⟨52628312641577542542093943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70171083522103390056125257 52628312641577542542093943)
              ·
                refine ⟨78942468962366313813140915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52628312641577542542093943 78942468962366313813140915)
                ·
                  refine ⟨118413703443549470719711373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78942468962366313813140915 118413703443549470719711373)
                  ·
                    refine ⟨44405138791331051519891765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 118413703443549470719711373 44405138791331051519891765)
                    ·
                      refine ⟨4162981761687286079989853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44405138791331051519891765 4162981761687286079989853)
                      ·
                        rfl

theorem cell23_8107378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_8107378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107378 prefixEnd_8107378 := by exact prefixLift 8107378
  have htrace : WordTrace (prefixWord ++ tailWord_8107378) baseStart_8107378 baseEnd_8107378 := by
    simpa [prefixWord, tailWord_8107378, baseEnd_8107378] using wordTrace_append hprefix tailTrace_8107378
  have hstable : (prefixWord ++ tailWord_8107378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107378).length < 2 ^ (prefixWord ++ tailWord_8107378).sum := by decide
  have hdescent : baseEnd_8107378 < baseStart_8107378 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107388 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 4, 2, 4]
def baseStart_8107388 : Nat := 118140960795 + 8107388 * 2 ^ 59
def prefixEnd_8107388 : Nat := 4983230072969 + 3 ^ 40 * 8107388 * 2
def baseEnd_8107388 : Nat := 4162986896493831040864807

theorem tailTrace_8107388 : CollatzResearch.WordTrace tailWord_8107388 prefixEnd_8107388 4162986896493831040864807 := by
  unfold tailWord_8107388
  simp only [CollatzResearch.WordTrace]
  refine ⟨147850366576162691239677409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197133822101550254986236545 147850366576162691239677409)
  ·
    refine ⟨110887774932122018429758057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147850366576162691239677409 110887774932122018429758057)
    ·
      refine ⟨83165831199091513822318543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110887774932122018429758057 83165831199091513822318543)
      ·
        refine ⟨124748746798637270733477815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83165831199091513822318543 124748746798637270733477815)
        ·
          refine ⟨187123120197955906100216723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124748746798637270733477815 187123120197955906100216723)
          ·
            refine ⟨280684680296933859150325085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187123120197955906100216723 280684680296933859150325085)
            ·
              refine ⟨105256755111350197181371907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280684680296933859150325085 105256755111350197181371907)
              ·
                refine ⟨157885132667025295772057861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105256755111350197181371907 157885132667025295772057861)
                ·
                  refine ⟨29603462375067242957260849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157885132667025295772057861 29603462375067242957260849)
                  ·
                    refine ⟨22202596781300432217945637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29603462375067242957260849 22202596781300432217945637)
                    ·
                      refine ⟨4162986896493831040864807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22202596781300432217945637 4162986896493831040864807)
                      ·
                        rfl

theorem cell23_8107388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_8107388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107388 prefixEnd_8107388 := by exact prefixLift 8107388
  have htrace : WordTrace (prefixWord ++ tailWord_8107388) baseStart_8107388 baseEnd_8107388 := by
    simpa [prefixWord, tailWord_8107388, baseEnd_8107388] using wordTrace_append hprefix tailTrace_8107388
  have hstable : (prefixWord ++ tailWord_8107388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107388).length < 2 ^ (prefixWord ++ tailWord_8107388).sum := by decide
  have hdescent : baseEnd_8107388 < baseStart_8107388 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107445 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 4, 5]
def baseStart_8107445 : Nat := 118140960795 + 8107445 * 2 ^ 59
def prefixEnd_8107445 : Nat := 4983230072969 + 3 ^ 40 * 8107445 * 2
def baseEnd_8107445 : Nat := 1387672054963712439284015

theorem tailTrace_8107445 : CollatzResearch.WordTrace tailWord_8107445 prefixEnd_8107445 1387672054963712439284015 := by
  unfold tailWord_8107445
  simp only [CollatzResearch.WordTrace]
  refine ⟨295702812113118881214179789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197135208075412587476119859 295702812113118881214179789)
  ·
    refine ⟨110888554542419580455317421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 295702812113118881214179789 110888554542419580455317421)
    ·
      refine ⟨41583207953407342670744033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110888554542419580455317421 41583207953407342670744033)
      ·
        refine ⟨31187405965055507003058025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41583207953407342670744033 31187405965055507003058025)
        ·
          refine ⟨23390554473791630252293519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31187405965055507003058025 23390554473791630252293519)
          ·
            refine ⟨35085831710687445378440279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23390554473791630252293519 35085831710687445378440279)
            ·
              refine ⟨52628747566031168067660419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35085831710687445378440279 52628747566031168067660419)
              ·
                refine ⟨78943121349046752101490629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52628747566031168067660419 78943121349046752101490629)
                ·
                  refine ⟨14801835252946266019029493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78943121349046752101490629 14801835252946266019029493)
                  ·
                    refine ⟨1387672054963712439284015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14801835252946266019029493 1387672054963712439284015)
                    ·
                      rfl

theorem cell23_8107445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_8107445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107445 prefixEnd_8107445 := by exact prefixLift 8107445
  have htrace : WordTrace (prefixWord ++ tailWord_8107445) baseStart_8107445 baseEnd_8107445 := by
    simpa [prefixWord, tailWord_8107445, baseEnd_8107445] using wordTrace_append hprefix tailTrace_8107445
  have hstable : (prefixWord ++ tailWord_8107445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107445).length < 2 ^ (prefixWord ++ tailWord_8107445).sum := by decide
  have hdescent : baseEnd_8107445 < baseStart_8107445 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107449 : List Nat := [1, 2, 1, 4, 4, 1, 3, 2, 5]
def baseStart_8107449 : Nat := 118140960795 + 8107449 * 2 ^ 59
def prefixEnd_8107449 : Nat := 4983230072969 + 3 ^ 40 * 8107449 * 2
def baseEnd_8107449 : Nat := 462557579868195033578003

theorem tailTrace_8107449 : CollatzResearch.WordTrace tailWord_8107449 prefixEnd_8107449 462557579868195033578003 := by
  unfold tailWord_8107449
  simp only [CollatzResearch.WordTrace]
  refine ⟨295702958005104389897325401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197135305336736259931550267 295702958005104389897325401)
  ·
    refine ⟨221777218503828292422994051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295702958005104389897325401 221777218503828292422994051)
    ·
      refine ⟨332665827755742438634491077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221777218503828292422994051 332665827755742438634491077)
      ·
        refine ⟨62374842704201707243967077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 332665827755742438634491077 62374842704201707243967077)
        ·
          refine ⟨11695283007037820108243827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62374842704201707243967077 11695283007037820108243827)
          ·
            refine ⟨17542924510556730162365741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11695283007037820108243827 17542924510556730162365741)
            ·
              refine ⟨6578596691458773810887153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17542924510556730162365741 6578596691458773810887153)
              ·
                refine ⟨4933947518594080358165365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6578596691458773810887153 4933947518594080358165365)
                ·
                  refine ⟨462557579868195033578003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4933947518594080358165365 462557579868195033578003)
                  ·
                    rfl

theorem cell23_8107449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 2, 5].length) (baseStart_8107449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107449 prefixEnd_8107449 := by exact prefixLift 8107449
  have htrace : WordTrace (prefixWord ++ tailWord_8107449) baseStart_8107449 baseEnd_8107449 := by
    simpa [prefixWord, tailWord_8107449, baseEnd_8107449] using wordTrace_append hprefix tailTrace_8107449
  have hstable : (prefixWord ++ tailWord_8107449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107449).length < 2 ^ (prefixWord ++ tailWord_8107449).sum := by decide
  have hdescent : baseEnd_8107449 < baseStart_8107449 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107465 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 1, 6, 2]
def baseStart_8107465 : Nat := 118140960795 + 8107465 * 2 ^ 59
def prefixEnd_8107465 : Nat := 4983230072969 + 3 ^ 40 * 8107465 * 2
def baseEnd_8107465 : Nat := 4163026434504227239601953

theorem tailTrace_8107465 : CollatzResearch.WordTrace tailWord_8107465 prefixEnd_8107465 4163026434504227239601953 := by
  unfold tailWord_8107465
  simp only [CollatzResearch.WordTrace]
  refine ⟨295703541573046424629907849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197135694382030949753271899 295703541573046424629907849)
  ·
    refine ⟨221777656179784818472430887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295703541573046424629907849 221777656179784818472430887)
    ·
      refine ⟨332666484269677227708646331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221777656179784818472430887 332666484269677227708646331)
      ·
        refine ⟨498999726404515841562969497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332666484269677227708646331 498999726404515841562969497)
        ·
          refine ⟨374249794803386881172227123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 498999726404515841562969497 374249794803386881172227123)
          ·
            refine ⟨561374692205080321758340685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374249794803386881172227123 561374692205080321758340685)
            ·
              refine ⟨210515509576905120659377757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 561374692205080321758340685 210515509576905120659377757)
              ·
                refine ⟨78943316091339420247266659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 210515509576905120659377757 78943316091339420247266659)
                ·
                  refine ⟨118414974137009130370899989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78943316091339420247266659 118414974137009130370899989)
                  ·
                    refine ⟨5550701912672302986135937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 118414974137009130370899989 5550701912672302986135937)
                    ·
                      refine ⟨4163026434504227239601953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5550701912672302986135937 4163026434504227239601953)
                      ·
                        rfl

theorem cell23_8107465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 6, 2].length) (baseStart_8107465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107465 prefixEnd_8107465 := by exact prefixLift 8107465
  have htrace : WordTrace (prefixWord ++ tailWord_8107465) baseStart_8107465 baseEnd_8107465 := by
    simpa [prefixWord, tailWord_8107465, baseEnd_8107465] using wordTrace_append hprefix tailTrace_8107465
  have hstable : (prefixWord ++ tailWord_8107465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107465).length < 2 ^ (prefixWord ++ tailWord_8107465).sum := by decide
  have hdescent : baseEnd_8107465 < baseStart_8107465 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107482 : List Nat := [3, 1, 1, 2, 3, 3, 2, 1, 2, 1, 4]
def baseStart_8107482 : Nat := 118140960795 + 8107482 * 2 ^ 59
def prefixEnd_8107482 : Nat := 4983230072969 + 3 ^ 40 * 8107482 * 2
def baseEnd_8107482 : Nat := 4163035163675353673089375

theorem tailTrace_8107482 : CollatzResearch.WordTrace tailWord_8107482 prefixEnd_8107482 4163035163675353673089375 := by
  unfold tailWord_8107482
  simp only [CollatzResearch.WordTrace]
  refine ⟨73926040403496209133319175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 197136107742656557688851133 73926040403496209133319175)
  ·
    refine ⟨110889060605244313699978763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73926040403496209133319175 110889060605244313699978763)
    ·
      refine ⟨166333590907866470549968145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110889060605244313699978763 166333590907866470549968145)
      ·
        refine ⟨124750193180899852912476109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166333590907866470549968145 124750193180899852912476109)
        ·
          refine ⟨46781322442837444842178541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124750193180899852912476109 46781322442837444842178541)
          ·
            refine ⟨17542995916064041815816953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46781322442837444842178541 17542995916064041815816953)
            ·
              refine ⟨13157246937048031361862715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17542995916064041815816953 13157246937048031361862715)
              ·
                refine ⟨19735870405572047042794073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13157246937048031361862715 19735870405572047042794073)
                ·
                  refine ⟨14801902804179035282095555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19735870405572047042794073 14801902804179035282095555)
                  ·
                    refine ⟨22202854206268552923143333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14801902804179035282095555 22202854206268552923143333)
                    ·
                      refine ⟨4163035163675353673089375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22202854206268552923143333 4163035163675353673089375)
                      ·
                        rfl

theorem cell23_8107482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_8107482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107482 prefixEnd_8107482 := by exact prefixLift 8107482
  have htrace : WordTrace (prefixWord ++ tailWord_8107482) baseStart_8107482 baseEnd_8107482 := by
    simpa [prefixWord, tailWord_8107482, baseEnd_8107482] using wordTrace_append hprefix tailTrace_8107482
  have hstable : (prefixWord ++ tailWord_8107482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107482).length < 2 ^ (prefixWord ++ tailWord_8107482).sum := by decide
  have hdescent : baseEnd_8107482 < baseStart_8107482 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107488 : List Nat := [2, 1, 1, 3, 1, 1, 2, 4, 8]
def baseStart_8107488 : Nat := 118140960795 + 8107488 * 2 ^ 59
def prefixEnd_8107488 : Nat := 4983230072969 + 3 ^ 40 * 8107488 * 2
def baseEnd_8107488 : Nat := 462559804951031183290483

theorem tailTrace_8107488 : CollatzResearch.WordTrace tailWord_8107488 prefixEnd_8107488 462559804951031183290483 := by
  unfold tailWord_8107488
  simp only [CollatzResearch.WordTrace]
  refine ⟨147852190225981549778997559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 197136253634642066371996745 147852190225981549778997559)
  ·
    refine ⟨221778285338972324668496339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147852190225981549778997559 221778285338972324668496339)
    ·
      refine ⟨332667428008458487002744509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221778285338972324668496339 332667428008458487002744509)
      ·
        refine ⟨124750285503171932626029191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 332667428008458487002744509 124750285503171932626029191)
        ·
          refine ⟨187125428254757898939043787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124750285503171932626029191 187125428254757898939043787)
          ·
            refine ⟨280688142382136848408565681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187125428254757898939043787 280688142382136848408565681)
            ·
              refine ⟨210516106786602636306424261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 280688142382136848408565681 210516106786602636306424261)
              ·
                refine ⟨39471770022487994307454549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 210516106786602636306424261 39471770022487994307454549)
                ·
                  refine ⟨462559804951031183290483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39471770022487994307454549 462559804951031183290483)
                  ·
                    rfl

theorem cell23_8107488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 8].length) (baseStart_8107488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107488 prefixEnd_8107488 := by exact prefixLift 8107488
  have htrace : WordTrace (prefixWord ++ tailWord_8107488) baseStart_8107488 baseEnd_8107488 := by
    simpa [prefixWord, tailWord_8107488, baseEnd_8107488] using wordTrace_append hprefix tailTrace_8107488
  have hstable : (prefixWord ++ tailWord_8107488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107488).length < 2 ^ (prefixWord ++ tailWord_8107488).sum := by decide
  have hdescent : baseEnd_8107488 < baseStart_8107488 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107502 : List Nat := [4, 1, 2, 1, 2, 1, 1, 4, 2, 2, 3]
def baseStart_8107502 : Nat := 118140960795 + 8107502 * 2 ^ 59
def prefixEnd_8107502 : Nat := 4983230072969 + 3 ^ 40 * 8107502 * 2
def baseEnd_8107502 : Nat := 4163045433288443594839283

theorem tailTrace_8107502 : CollatzResearch.WordTrace tailWord_8107502 prefixEnd_8107502 4163045433288443594839283 := by
  unfold tailWord_8107502
  simp only [CollatzResearch.WordTrace]
  refine ⟨36963111384239047493625595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 197136594049274919966003173 36963111384239047493625595)
  ·
    refine ⟨55444667076358571240438393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36963111384239047493625595 55444667076358571240438393)
    ·
      refine ⟨41583500307268928430328795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55444667076358571240438393 41583500307268928430328795)
      ·
        refine ⟨62375250460903392645493193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41583500307268928430328795 62375250460903392645493193)
        ·
          refine ⟨46781437845677544484119895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62375250460903392645493193 46781437845677544484119895)
          ·
            refine ⟨70172156768516316726179843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46781437845677544484119895 70172156768516316726179843)
            ·
              refine ⟨105258235152774475089269765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70172156768516316726179843 105258235152774475089269765)
              ·
                refine ⟨19735919091145214079238081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105258235152774475089269765 19735919091145214079238081)
                ·
                  refine ⟨14801939318358910559428561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19735919091145214079238081 14801939318358910559428561)
                  ·
                    refine ⟨11101454488769182919571421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14801939318358910559428561 11101454488769182919571421)
                    ·
                      refine ⟨4163045433288443594839283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11101454488769182919571421 4163045433288443594839283)
                      ·
                        rfl

theorem cell23_8107502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_8107502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107502 prefixEnd_8107502 := by exact prefixLift 8107502
  have htrace : WordTrace (prefixWord ++ tailWord_8107502) baseStart_8107502 baseEnd_8107502 := by
    simpa [prefixWord, tailWord_8107502, baseEnd_8107502] using wordTrace_append hprefix tailTrace_8107502
  have hstable : (prefixWord ++ tailWord_8107502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107502).length < 2 ^ (prefixWord ++ tailWord_8107502).sum := by decide
  have hdescent : baseEnd_8107502 < baseStart_8107502 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107505 : List Nat := [1, 2, 2, 2, 3, 2, 1, 4, 6]
def baseStart_8107505 : Nat := 118140960795 + 8107505 * 2 ^ 59
def prefixEnd_8107505 : Nat := 4983230072969 + 3 ^ 40 * 8107505 * 2
def baseEnd_8107505 : Nat := 462560774858934120344641

theorem tailTrace_8107505 : CollatzResearch.WordTrace tailWord_8107505 prefixEnd_8107505 462560774858934120344641 := by
  unfold tailWord_8107505
  simp only [CollatzResearch.WordTrace]
  refine ⟨295705000492901511461363969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197136666995267674307575979 295705000492901511461363969)
  ·
    refine ⟨221778750369676133596022977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 295705000492901511461363969 221778750369676133596022977)
    ·
      refine ⟨166334062777257100197017233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 221778750369676133596022977 166334062777257100197017233)
      ·
        refine ⟨124750547082942825147762925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166334062777257100197017233 124750547082942825147762925)
        ·
          refine ⟨46781455156103559430411097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124750547082942825147762925 46781455156103559430411097)
          ·
            refine ⟨35086091367077669572808323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46781455156103559430411097 35086091367077669572808323)
            ·
              refine ⟨52629137050616504359212485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35086091367077669572808323 52629137050616504359212485)
              ·
                refine ⟨9867963196990594567352341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52629137050616504359212485 9867963196990594567352341)
                ·
                  refine ⟨462560774858934120344641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9867963196990594567352341 462560774858934120344641)
                  ·
                    rfl

theorem cell23_8107505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 6].length) (baseStart_8107505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107505 prefixEnd_8107505 := by exact prefixLift 8107505
  have htrace : WordTrace (prefixWord ++ tailWord_8107505) baseStart_8107505 baseEnd_8107505 := by
    simpa [prefixWord, tailWord_8107505, baseEnd_8107505] using wordTrace_append hprefix tailTrace_8107505
  have hstable : (prefixWord ++ tailWord_8107505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107505).length < 2 ^ (prefixWord ++ tailWord_8107505).sum := by decide
  have hdescent : baseEnd_8107505 < baseStart_8107505 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8107533 : List Nat := [1, 7, 1, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_8107533 : Nat := 118140960795 + 8107533 * 2 ^ 59
def prefixEnd_8107533 : Nat := 4983230072969 + 3 ^ 40 * 8107533 * 2
def baseEnd_8107533 : Nat := 4163061351188732973551641

theorem tailTrace_8107533 : CollatzResearch.WordTrace tailWord_8107533 prefixEnd_8107533 4163061351188732973551641 := by
  unfold tailWord_8107533
  simp only [CollatzResearch.WordTrace]
  refine ⟨295706021736800072243383253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 197137347824533381495588835 295706021736800072243383253)
  ·
    refine ⟨6930609884456251693204295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 295706021736800072243383253 6930609884456251693204295)
    ·
      refine ⟨10395914826684377539806443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6930609884456251693204295 10395914826684377539806443)
      ·
        refine ⟨15593872240026566309709665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10395914826684377539806443 15593872240026566309709665)
        ·
          refine ⟨11695404180019924732282249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15593872240026566309709665 11695404180019924732282249)
          ·
            refine ⟨8771553135014943549211687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11695404180019924732282249 8771553135014943549211687)
            ·
              refine ⟨13157329702522415323817531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8771553135014943549211687 13157329702522415323817531)
              ·
                refine ⟨19735994553783622985726297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13157329702522415323817531 19735994553783622985726297)
                ·
                  refine ⟨14801995915337717239294723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19735994553783622985726297 14801995915337717239294723)
                  ·
                    refine ⟨22202993873006575858942085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14801995915337717239294723 22202993873006575858942085)
                    ·
                      refine ⟨4163061351188732973551641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22202993873006575858942085 4163061351188732973551641)
                      ·
                        rfl

theorem cell23_8107533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_8107533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8107533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8107533 prefixEnd_8107533 := by exact prefixLift 8107533
  have htrace : WordTrace (prefixWord ++ tailWord_8107533) baseStart_8107533 baseEnd_8107533 := by
    simpa [prefixWord, tailWord_8107533, baseEnd_8107533] using wordTrace_append hprefix tailTrace_8107533
  have hstable : (prefixWord ++ tailWord_8107533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8107533).length < 2 ^ (prefixWord ++ tailWord_8107533).sum := by decide
  have hdescent : baseEnd_8107533 < baseStart_8107533 := by decide
  rcases family_descends (prefixWord ++ tailWord_8107533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
