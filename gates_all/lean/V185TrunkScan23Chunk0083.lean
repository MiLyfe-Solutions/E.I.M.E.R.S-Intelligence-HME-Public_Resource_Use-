import V185TrunkScan23Chunk0082

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_492828 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 2, 2, 6]
def baseStart_492828 : Nat := 118140960795 + 492828 * 2 ^ 59
def prefixEnd_492828 : Nat := 4983230072969 + 3 ^ 40 * 492828 * 2
def baseEnd_492828 : Nat := 253057643994103041883531

theorem tailTrace_492828 : CollatzResearch.WordTrace tailWord_492828 prefixEnd_492828 253057643994103041883531 := by
  unfold tailWord_492828
  simp only [CollatzResearch.WordTrace]
  refine ⟨8987456929287899583263569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11983275905717199444351425 8987456929287899583263569)
  ·
    refine ⟨6740592696965924687447677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8987456929287899583263569 6740592696965924687447677)
    ·
      refine ⟨2527722261362221757792879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6740592696965924687447677 2527722261362221757792879)
      ·
        refine ⟨3791583392043332636689319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2527722261362221757792879 3791583392043332636689319)
        ·
          refine ⟨5687375088064998955033979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3791583392043332636689319 5687375088064998955033979)
          ·
            refine ⟨8531062632097498432550969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5687375088064998955033979 8531062632097498432550969)
            ·
              refine ⟨6398296974073123824413227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8531062632097498432550969 6398296974073123824413227)
              ·
                refine ⟨9597445461109685736619841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6398296974073123824413227 9597445461109685736619841)
                ·
                  refine ⟨7198084095832264302464881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9597445461109685736619841 7198084095832264302464881)
                  ·
                    refine ⟨5398563071874198226848661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7198084095832264302464881 5398563071874198226848661)
                    ·
                      refine ⟨253057643994103041883531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5398563071874198226848661 253057643994103041883531)
                      ·
                        rfl

theorem cell23_492828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_492828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492828 prefixEnd_492828 := by exact prefixLift 492828
  have htrace : WordTrace (prefixWord ++ tailWord_492828) baseStart_492828 baseEnd_492828 := by
    simpa [prefixWord, tailWord_492828, baseEnd_492828] using wordTrace_append hprefix tailTrace_492828
  have hstable : (prefixWord ++ tailWord_492828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492828).length < 2 ^ (prefixWord ++ tailWord_492828).sum := by decide
  have hdescent : baseEnd_492828 < baseStart_492828 := by decide
  rcases family_descends (prefixWord ++ tailWord_492828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492832 : List Nat := [2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 4]
def baseStart_492832 : Nat := 118140960795 + 492832 * 2 ^ 59
def prefixEnd_492832 : Nat := 4983230072969 + 3 ^ 40 * 492832 * 2
def baseEnd_492832 : Nat := 253059697916721026233513

theorem tailTrace_492832 : CollatzResearch.WordTrace tailWord_492832 prefixEnd_492832 253059697916721026233513 := by
  unfold tailWord_492832
  simp only [CollatzResearch.WordTrace]
  refine ⟨8987529875280653924836375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11983373167040871899781833 8987529875280653924836375)
  ·
    refine ⟨13481294812920980887254563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8987529875280653924836375 13481294812920980887254563)
    ·
      refine ⟨20221942219381471330881845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13481294812920980887254563 20221942219381471330881845)
      ·
        refine ⟨1895807083067012937270173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20221942219381471330881845 1895807083067012937270173)
        ·
          refine ⟨710927656150129851476315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1895807083067012937270173 710927656150129851476315)
          ·
            refine ⟨1066391484225194777214473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710927656150129851476315 1066391484225194777214473)
            ·
              refine ⟨799793613168896082910855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1066391484225194777214473 799793613168896082910855)
              ·
                refine ⟨1199690419753344124366283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 799793613168896082910855 1199690419753344124366283)
                ·
                  refine ⟨1799535629630016186549425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1199690419753344124366283 1799535629630016186549425)
                  ·
                    refine ⟨1349651722222512139912069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1799535629630016186549425 1349651722222512139912069)
                    ·
                      refine ⟨253059697916721026233513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1349651722222512139912069 253059697916721026233513)
                      ·
                        rfl

theorem cell23_492832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_492832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492832 prefixEnd_492832 := by exact prefixLift 492832
  have htrace : WordTrace (prefixWord ++ tailWord_492832) baseStart_492832 baseEnd_492832 := by
    simpa [prefixWord, tailWord_492832, baseEnd_492832] using wordTrace_append hprefix tailTrace_492832
  have hstable : (prefixWord ++ tailWord_492832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492832).length < 2 ^ (prefixWord ++ tailWord_492832).sum := by decide
  have hdescent : baseEnd_492832 < baseStart_492832 := by decide
  rcases family_descends (prefixWord ++ tailWord_492832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492835 : List Nat := [1, 1, 1, 4, 2, 3, 1, 3, 1, 3, 3]
def baseStart_492835 : Nat := 118140960795 + 492835 * 2 ^ 59
def prefixEnd_492835 : Nat := 4983230072969 + 3 ^ 40 * 492835 * 2
def baseEnd_492835 : Nat := 253061238358684514495999

theorem tailTrace_492835 : CollatzResearch.WordTrace tailWord_492835 prefixEnd_492835 253061238358684514495999 := by
  unfold tailWord_492835
  simp only [CollatzResearch.WordTrace]
  refine ⟨17975169169550439362031959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11983446113033626241354639 17975169169550439362031959)
  ·
    refine ⟨26962753754325659043047939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17975169169550439362031959 26962753754325659043047939)
    ·
      refine ⟨40444130631488488564571909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26962753754325659043047939 40444130631488488564571909)
      ·
        refine ⟨7583274493404091605857233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40444130631488488564571909 7583274493404091605857233)
        ·
          refine ⟨5687455870053068704392925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7583274493404091605857233 5687455870053068704392925)
          ·
            refine ⟨2132795951269900764147347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5687455870053068704392925 2132795951269900764147347)
            ·
              refine ⟨3199193926904851146221021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2132795951269900764147347 3199193926904851146221021)
              ·
                refine ⟨1199697722589319179832883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3199193926904851146221021 1199697722589319179832883)
                ·
                  refine ⟨1799546583883978769749325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1199697722589319179832883 1799546583883978769749325)
                  ·
                    refine ⟨674829968956492038655997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1799546583883978769749325 674829968956492038655997)
                    ·
                      refine ⟨253061238358684514495999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 674829968956492038655997 253061238358684514495999)
                      ·
                        rfl

theorem cell23_492835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_492835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492835 prefixEnd_492835 := by exact prefixLift 492835
  have htrace : WordTrace (prefixWord ++ tailWord_492835) baseStart_492835 baseEnd_492835 := by
    simpa [prefixWord, tailWord_492835, baseEnd_492835] using wordTrace_append hprefix tailTrace_492835
  have hstable : (prefixWord ++ tailWord_492835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492835).length < 2 ^ (prefixWord ++ tailWord_492835).sum := by decide
  have hdescent : baseEnd_492835 < baseStart_492835 := by decide
  rcases family_descends (prefixWord ++ tailWord_492835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492842 : List Nat := [3, 1, 4, 2, 1, 2, 3, 7]
def baseStart_492842 : Nat := 118140960795 + 492842 * 2 ^ 59
def prefixEnd_492842 : Nat := 4983230072969 + 3 ^ 40 * 492842 * 2
def baseEnd_492842 : Nat := 9372771582343184707721

theorem tailTrace_492842 : CollatzResearch.WordTrace tailWord_492842 prefixEnd_492842 9372771582343184707721 := by
  unfold tailWord_492842
  simp only [CollatzResearch.WordTrace]
  refine ⟨4493856120131269889384195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11983616320350053038357853 4493856120131269889384195)
  ·
    refine ⟨6740784180196904834076293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4493856120131269889384195 6740784180196904834076293)
    ·
      refine ⟨1263897033786919656389305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6740784180196904834076293 1263897033786919656389305)
      ·
        refine ⟨947922775340189742291979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1263897033786919656389305 947922775340189742291979)
        ·
          refine ⟨1421884163010284613437969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947922775340189742291979 1421884163010284613437969)
          ·
            refine ⟨1066413122257713460078477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1421884163010284613437969 1066413122257713460078477)
            ·
              refine ⟨399904920846642547529429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1066413122257713460078477 399904920846642547529429)
              ·
                refine ⟨9372771582343184707721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 399904920846642547529429 9372771582343184707721)
                ·
                  rfl

theorem cell23_492842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 7].length) (baseStart_492842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492842 prefixEnd_492842 := by exact prefixLift 492842
  have htrace : WordTrace (prefixWord ++ tailWord_492842) baseStart_492842 baseEnd_492842 := by
    simpa [prefixWord, tailWord_492842, baseEnd_492842] using wordTrace_append hprefix tailTrace_492842
  have hstable : (prefixWord ++ tailWord_492842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492842).length < 2 ^ (prefixWord ++ tailWord_492842).sum := by decide
  have hdescent : baseEnd_492842 < baseStart_492842 := by decide
  rcases family_descends (prefixWord ++ tailWord_492842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492848 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 5]
def baseStart_492848 : Nat := 118140960795 + 492848 * 2 ^ 59
def prefixEnd_492848 : Nat := 4983230072969 + 3 ^ 40 * 492848 * 2
def baseEnd_492848 : Nat := 253067913607192963633439

theorem tailTrace_492848 : CollatzResearch.WordTrace tailWord_492848 prefixEnd_492848 253067913607192963633439 := by
  unfold tailWord_492848
  simp only [CollatzResearch.WordTrace]
  refine ⟨8987821659251671291127599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11983762212335561721503465 8987821659251671291127599)
  ·
    refine ⟨13481732488877506936691399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8987821659251671291127599 13481732488877506936691399)
    ·
      refine ⟨20222598733316260405037099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13481732488877506936691399 20222598733316260405037099)
      ·
        refine ⟨30333898099974390607555649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20222598733316260405037099 30333898099974390607555649)
        ·
          refine ⟨22750423574980792955666737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30333898099974390607555649 22750423574980792955666737)
          ·
            refine ⟨17062817681235594716750053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22750423574980792955666737 17062817681235594716750053)
            ·
              refine ⟨3199278315231674009390635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17062817681235594716750053 3199278315231674009390635)
              ·
                refine ⟨4798917472847511014085953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3199278315231674009390635 4798917472847511014085953)
                ·
                  refine ⟨3599188104635633260564465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4798917472847511014085953 3599188104635633260564465)
                  ·
                    refine ⟨2699391078476724945423349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3599188104635633260564465 2699391078476724945423349)
                    ·
                      refine ⟨253067913607192963633439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2699391078476724945423349 253067913607192963633439)
                      ·
                        rfl

theorem cell23_492848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 5].length) (baseStart_492848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492848 prefixEnd_492848 := by exact prefixLift 492848
  have htrace : WordTrace (prefixWord ++ tailWord_492848) baseStart_492848 baseEnd_492848 := by
    simpa [prefixWord, tailWord_492848, baseEnd_492848] using wordTrace_append hprefix tailTrace_492848
  have hstable : (prefixWord ++ tailWord_492848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492848).length < 2 ^ (prefixWord ++ tailWord_492848).sum := by decide
  have hdescent : baseEnd_492848 < baseStart_492848 := by decide
  rcases family_descends (prefixWord ++ tailWord_492848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492852 : List Nat := [2, 5, 1, 1, 1, 1, 1, 4, 1, 3, 3]
def baseStart_492852 : Nat := 118140960795 + 492852 * 2 ^ 59
def prefixEnd_492852 : Nat := 4983230072969 + 3 ^ 40 * 492852 * 2
def baseEnd_492852 : Nat := 253069967529810947983421

theorem tailTrace_492852 : CollatzResearch.WordTrace tailWord_492852 prefixEnd_492852 253069967529810947983421 := by
  unfold tailWord_492852
  simp only [CollatzResearch.WordTrace]
  refine ⟨8987894605244425632700405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11983859473659234176933873 8987894605244425632700405)
  ·
    refine ⟨842615119241664903065663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8987894605244425632700405 842615119241664903065663)
    ·
      refine ⟨1263922678862497354598495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 842615119241664903065663 1263922678862497354598495)
      ·
        refine ⟨1895884018293746031897743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1263922678862497354598495 1895884018293746031897743)
        ·
          refine ⟨2843826027440619047846615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1895884018293746031897743 2843826027440619047846615)
          ·
            refine ⟨4265739041160928571769923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2843826027440619047846615 4265739041160928571769923)
            ·
              refine ⟨6398608561741392857654885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4265739041160928571769923 6398608561741392857654885)
              ·
                refine ⟨1199739105326511160810291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6398608561741392857654885 1199739105326511160810291)
                ·
                  refine ⟨1799608657989766741215437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1199739105326511160810291 1799608657989766741215437)
                  ·
                    refine ⟨674853246746162527955789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1799608657989766741215437 674853246746162527955789)
                    ·
                      refine ⟨253069967529810947983421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 674853246746162527955789 253069967529810947983421)
                      ·
                        rfl

theorem cell23_492852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_492852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492852 prefixEnd_492852 := by exact prefixLift 492852
  have htrace : WordTrace (prefixWord ++ tailWord_492852) baseStart_492852 baseEnd_492852 := by
    simpa [prefixWord, tailWord_492852, baseEnd_492852] using wordTrace_append hprefix tailTrace_492852
  have hstable : (prefixWord ++ tailWord_492852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492852).length < 2 ^ (prefixWord ++ tailWord_492852).sum := by decide
  have hdescent : baseEnd_492852 < baseStart_492852 := by decide
  rcases family_descends (prefixWord ++ tailWord_492852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492870 : List Nat := [6, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2]
def baseStart_492870 : Nat := 118140960795 + 492870 * 2 ^ 59
def prefixEnd_492870 : Nat := 4983230072969 + 3 ^ 40 * 492870 * 2
def baseEnd_492870 : Nat := 253079210181591877558339

theorem tailTrace_492870 : CollatzResearch.WordTrace tailWord_492870 prefixEnd_492870 253079210181591877558339 := by
  unfold tailWord_492870
  simp only [CollatzResearch.WordTrace]
  refine ⟨561763928888238760611127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11984297149615760226370709 561763928888238760611127)
  ·
    refine ⟨842645893332358140916691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 561763928888238760611127 842645893332358140916691)
    ·
      refine ⟨1263968839998537211375037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 842645893332358140916691 1263968839998537211375037)
      ·
        refine ⟨473988314999451454265639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1263968839998537211375037 473988314999451454265639)
        ·
          refine ⟨710982472499177181398459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473988314999451454265639 710982472499177181398459)
          ·
            refine ⟨1066473708748765772097689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710982472499177181398459 1066473708748765772097689)
            ·
              refine ⟨799855281561574329073267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1066473708748765772097689 799855281561574329073267)
              ·
                refine ⟨1199782922342361493609901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 799855281561574329073267 1199782922342361493609901)
                ·
                  refine ⟨449918595878385560103713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1199782922342361493609901 449918595878385560103713)
                  ·
                    refine ⟨337438946908789170077785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 449918595878385560103713 337438946908789170077785)
                    ·
                      refine ⟨253079210181591877558339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 337438946908789170077785 253079210181591877558339)
                      ·
                        rfl

theorem cell23_492870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_492870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492870 prefixEnd_492870 := by exact prefixLift 492870
  have htrace : WordTrace (prefixWord ++ tailWord_492870) baseStart_492870 baseEnd_492870 := by
    simpa [prefixWord, tailWord_492870, baseEnd_492870] using wordTrace_append hprefix tailTrace_492870
  have hstable : (prefixWord ++ tailWord_492870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492870).length < 2 ^ (prefixWord ++ tailWord_492870).sum := by decide
  have hdescent : baseEnd_492870 < baseStart_492870 := by decide
  rcases family_descends (prefixWord ++ tailWord_492870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492885 : List Nat := [1, 3, 2, 2, 3, 1, 2, 1, 2, 6]
def baseStart_492885 : Nat := 118140960795 + 492885 * 2 ^ 59
def prefixEnd_492885 : Nat := 4983230072969 + 3 ^ 40 * 492885 * 2
def baseEnd_492885 : Nat := 84362304130469772956923

theorem tailTrace_492885 : CollatzResearch.WordTrace tailWord_492885 prefixEnd_492885 84362304130469772956923 := by
  unfold tailWord_492885
  simp only [CollatzResearch.WordTrace]
  refine ⟨17976992819369297901352109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11984661879579531934234739 17976992819369297901352109)
  ·
    refine ⟨6741372307263486713007041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17976992819369297901352109 6741372307263486713007041)
    ·
      refine ⟨5056029230447615034755281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6741372307263486713007041 5056029230447615034755281)
      ·
        refine ⟨3792021922835711276066461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5056029230447615034755281 3792021922835711276066461)
        ·
          refine ⟨1422008221063391728524923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3792021922835711276066461 1422008221063391728524923)
          ·
            refine ⟨2133012331595087592787385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1422008221063391728524923 2133012331595087592787385)
            ·
              refine ⟨1599759248696315694590539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2133012331595087592787385 1599759248696315694590539)
              ·
                refine ⟨2399638873044473541885809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1599759248696315694590539 2399638873044473541885809)
                ·
                  refine ⟨1799729154783355156414357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2399638873044473541885809 1799729154783355156414357)
                  ·
                    refine ⟨84362304130469772956923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1799729154783355156414357 84362304130469772956923)
                    ·
                      rfl

theorem cell23_492885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_492885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492885 prefixEnd_492885 := by exact prefixLift 492885
  have htrace : WordTrace (prefixWord ++ tailWord_492885) baseStart_492885 baseEnd_492885 := by
    simpa [prefixWord, tailWord_492885, baseEnd_492885] using wordTrace_append hprefix tailTrace_492885
  have hstable : (prefixWord ++ tailWord_492885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492885).length < 2 ^ (prefixWord ++ tailWord_492885).sum := by decide
  have hdescent : baseEnd_492885 < baseStart_492885 := by decide
  rcases family_descends (prefixWord ++ tailWord_492885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492893 : List Nat := [1, 4, 5, 1, 2, 1, 2, 7]
def baseStart_492893 : Nat := 118140960795 + 492893 * 2 ^ 59
def prefixEnd_492893 : Nat := 4983230072969 + 3 ^ 40 * 492893 * 2
def baseEnd_492893 : Nat := 9373741490246121761879

theorem tailTrace_492893 : CollatzResearch.WordTrace tailWord_492893 prefixEnd_492893 9373741490246121761879 := by
  unfold tailWord_492893
  simp only [CollatzResearch.WordTrace]
  refine ⟨17977284603340315267643333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11984856402226876845095555 17977284603340315267643333)
  ·
    refine ⟨3370740863126309112683125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17977284603340315267643333 3370740863126309112683125)
    ·
      refine ⟨316006955918091479314043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3370740863126309112683125 316006955918091479314043)
      ·
        refine ⟨474010433877137218971065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316006955918091479314043 474010433877137218971065)
        ·
          refine ⟨355507825407852914228299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 474010433877137218971065 355507825407852914228299)
          ·
            refine ⟨533261738111779371342449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355507825407852914228299 533261738111779371342449)
            ·
              refine ⟨399946303583834528506837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533261738111779371342449 399946303583834528506837)
              ·
                refine ⟨9373741490246121761879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 399946303583834528506837 9373741490246121761879)
                ·
                  rfl

theorem cell23_492893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 7].length) (baseStart_492893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492893 prefixEnd_492893 := by exact prefixLift 492893
  have htrace : WordTrace (prefixWord ++ tailWord_492893) baseStart_492893 baseEnd_492893 := by
    simpa [prefixWord, tailWord_492893, baseEnd_492893] using wordTrace_append hprefix tailTrace_492893
  have hstable : (prefixWord ++ tailWord_492893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492893).length < 2 ^ (prefixWord ++ tailWord_492893).sum := by decide
  have hdescent : baseEnd_492893 < baseStart_492893 := by decide
  rcases family_descends (prefixWord ++ tailWord_492893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492909 : List Nat := [1, 5, 1, 1, 1, 3, 1, 2, 4, 2, 2]
def baseStart_492909 : Nat := 118140960795 + 492909 * 2 ^ 59
def prefixEnd_492909 : Nat := 4983230072969 + 3 ^ 40 * 492909 * 2
def baseEnd_492909 : Nat := 253099235927117224970659

theorem tailTrace_492909 : CollatzResearch.WordTrace tailWord_492909 prefixEnd_492909 253099235927117224970659 := by
  unfold tailWord_492909
  simp only [CollatzResearch.WordTrace]
  refine ⟨17977868171282350000225781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11985245447521566666817187 17977868171282350000225781)
  ·
    refine ⟨1685425141057720312521167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17977868171282350000225781 1685425141057720312521167)
    ·
      refine ⟨2528137711586580468781751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1685425141057720312521167 2528137711586580468781751)
      ·
        refine ⟨3792206567379870703172627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2528137711586580468781751 3792206567379870703172627)
        ·
          refine ⟨5688309851069806054758941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3792206567379870703172627 5688309851069806054758941)
          ·
            refine ⟨2133116194151177270534603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5688309851069806054758941 2133116194151177270534603)
            ·
              refine ⟨3199674291226765905801905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2133116194151177270534603 3199674291226765905801905)
              ·
                refine ⟨2399755718420074429351429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3199674291226765905801905 2399755718420074429351429)
                ·
                  refine ⟨449954197203763955503393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2399755718420074429351429 449954197203763955503393)
                  ·
                    refine ⟨337465647902822966627545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 449954197203763955503393 337465647902822966627545)
                    ·
                      refine ⟨253099235927117224970659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 337465647902822966627545 253099235927117224970659)
                      ·
                        rfl

theorem cell23_492909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_492909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492909 prefixEnd_492909 := by exact prefixLift 492909
  have htrace : WordTrace (prefixWord ++ tailWord_492909) baseStart_492909 baseEnd_492909 := by
    simpa [prefixWord, tailWord_492909, baseEnd_492909] using wordTrace_append hprefix tailTrace_492909
  have hstable : (prefixWord ++ tailWord_492909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492909).length < 2 ^ (prefixWord ++ tailWord_492909).sum := by decide
  have hdescent : baseEnd_492909 < baseStart_492909 := by decide
  rcases family_descends (prefixWord ++ tailWord_492909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492932 : List Nat := [2, 3, 2, 1, 1, 5, 1, 1, 7]
def baseStart_492932 : Nat := 118140960795 + 492932 * 2 ^ 59
def prefixEnd_492932 : Nat := 4983230072969 + 3 ^ 40 * 492932 * 2
def baseEnd_492932 : Nat := 28123449553574514998117

theorem tailTrace_492932 : CollatzResearch.WordTrace tailWord_492932 prefixEnd_492932 28123449553574514998117 := by
  unfold tailWord_492932
  simp only [CollatzResearch.WordTrace]
  refine ⟨8989353525099512464156525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11985804700132683285542033 8989353525099512464156525)
  ·
    refine ⟨3371007571912317174058697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8989353525099512464156525 3371007571912317174058697)
    ·
      refine ⟨2528255678934237880544023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3371007571912317174058697 2528255678934237880544023)
      ·
        refine ⟨3792383518401356820816035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2528255678934237880544023 3792383518401356820816035)
        ·
          refine ⟨5688575277602035231224053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3792383518401356820816035 5688575277602035231224053)
          ·
            refine ⟨533303932275190802927255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5688575277602035231224053 533303932275190802927255)
            ·
              refine ⟨799955898412786204390883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533303932275190802927255 799955898412786204390883)
              ·
                refine ⟨1199933847619179306586325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 799955898412786204390883 1199933847619179306586325)
                ·
                  refine ⟨28123449553574514998117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1199933847619179306586325 28123449553574514998117)
                  ·
                    rfl

theorem cell23_492932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 7].length) (baseStart_492932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492932 prefixEnd_492932 := by exact prefixLift 492932
  have htrace : WordTrace (prefixWord ++ tailWord_492932) baseStart_492932 baseEnd_492932 := by
    simpa [prefixWord, tailWord_492932, baseEnd_492932] using wordTrace_append hprefix tailTrace_492932
  have hstable : (prefixWord ++ tailWord_492932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492932).length < 2 ^ (prefixWord ++ tailWord_492932).sum := by decide
  have hdescent : baseEnd_492932 < baseStart_492932 := by decide
  rcases family_descends (prefixWord ++ tailWord_492932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_492962 : List Nat := [3, 3, 1, 2, 1, 2, 1, 3, 2, 5]
def baseStart_492962 : Nat := 118140960795 + 492962 * 2 ^ 59
def prefixEnd_492962 : Nat := 4983230072969 + 3 ^ 40 * 492962 * 2
def baseEnd_492962 : Nat := 84375483467268505869305

theorem tailTrace_492962 : CollatzResearch.WordTrace tailWord_492962 prefixEnd_492962 84375483467268505869305 := by
  unfold tailWord_492962
  simp only [CollatzResearch.WordTrace]
  refine ⟨4494950310022585012976285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11986534160060226701270093 4494950310022585012976285)
  ·
    refine ⟨1685606366258469379866107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4494950310022585012976285 1685606366258469379866107)
    ·
      refine ⟨2528409549387704069799161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1685606366258469379866107 2528409549387704069799161)
      ·
        refine ⟨1896307162040778052349371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2528409549387704069799161 1896307162040778052349371)
        ·
          refine ⟨2844460743061167078524057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1896307162040778052349371 2844460743061167078524057)
          ·
            refine ⟨2133345557295875308893043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2844460743061167078524057 2133345557295875308893043)
            ·
              refine ⟨3200018335943812963339565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2133345557295875308893043 3200018335943812963339565)
              ·
                refine ⟨1200006875978929861252337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3200018335943812963339565 1200006875978929861252337)
                ·
                  refine ⟨900005156984197395939253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1200006875978929861252337 900005156984197395939253)
                  ·
                    refine ⟨84375483467268505869305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 900005156984197395939253 84375483467268505869305)
                    ·
                      rfl

theorem cell23_492962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_492962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_492962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_492962 prefixEnd_492962 := by exact prefixLift 492962
  have htrace : WordTrace (prefixWord ++ tailWord_492962) baseStart_492962 baseEnd_492962 := by
    simpa [prefixWord, tailWord_492962, baseEnd_492962] using wordTrace_append hprefix tailTrace_492962
  have hstable : (prefixWord ++ tailWord_492962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_492962).length < 2 ^ (prefixWord ++ tailWord_492962).sum := by decide
  have hdescent : baseEnd_492962 < baseStart_492962 := by decide
  rcases family_descends (prefixWord ++ tailWord_492962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493035 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 5, 5]
def baseStart_493035 : Nat := 118140960795 + 493035 * 2 ^ 59
def prefixEnd_493035 : Nat := 4983230072969 + 3 ^ 40 * 493035 * 2
def baseEnd_493035 : Nat := 84387978163194577331693

theorem tailTrace_493035 : CollatzResearch.WordTrace tailWord_493035 prefixEnd_493035 84387978163194577331693 := by
  unfold tailWord_493035
  simp only [CollatzResearch.WordTrace]
  refine ⟨17982463768825873519312559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11988309179217249012875039 17982463768825873519312559)
  ·
    refine ⟨26973695653238810278968839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17982463768825873519312559 26973695653238810278968839)
    ·
      refine ⟨40460543479858215418453259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26973695653238810278968839 40460543479858215418453259)
      ·
        refine ⟨60690815219787323127679889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40460543479858215418453259 60690815219787323127679889)
        ·
          refine ⟨45518111414840492345759917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60690815219787323127679889 45518111414840492345759917)
          ·
            refine ⟨17069291780565184629659969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45518111414840492345759917 17069291780565184629659969)
            ·
              refine ⟨12801968835423888472244977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17069291780565184629659969 12801968835423888472244977)
              ·
                refine ⟨9601476626567916354183733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12801968835423888472244977 9601476626567916354183733)
                ·
                  refine ⟨900138433740742158204725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9601476626567916354183733 900138433740742158204725)
                  ·
                    refine ⟨84387978163194577331693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 900138433740742158204725 84387978163194577331693)
                    ·
                      rfl

theorem cell23_493035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 5].length) (baseStart_493035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493035 prefixEnd_493035 := by exact prefixLift 493035
  have htrace : WordTrace (prefixWord ++ tailWord_493035) baseStart_493035 baseEnd_493035 := by
    simpa [prefixWord, tailWord_493035, baseEnd_493035] using wordTrace_append hprefix tailTrace_493035
  have hstable : (prefixWord ++ tailWord_493035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493035).length < 2 ^ (prefixWord ++ tailWord_493035).sum := by decide
  have hdescent : baseEnd_493035 < baseStart_493035 := by decide
  rcases family_descends (prefixWord ++ tailWord_493035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493042 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 1, 2, 6]
def baseStart_493042 : Nat := 118140960795 + 493042 * 2 ^ 59
def prefixEnd_493042 : Nat := 4983230072969 + 3 ^ 40 * 493042 * 2
def baseEnd_493042 : Nat := 253167528854165204607547

theorem tailTrace_493042 : CollatzResearch.WordTrace tailWord_493042 prefixEnd_493042 253167528854165204607547 := by
  unfold tailWord_493042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4495679769950128428704345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11988479386533675809878253 4495679769950128428704345)
  ·
    refine ⟨3371759827462596321528259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4495679769950128428704345 3371759827462596321528259)
    ·
      refine ⟨5057639741193894482292389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3371759827462596321528259 5057639741193894482292389)
      ·
        refine ⟨948307451473855215429823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5057639741193894482292389 948307451473855215429823)
        ·
          refine ⟨1422461177210782823144735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948307451473855215429823 1422461177210782823144735)
          ·
            refine ⟨2133691765816174234717103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1422461177210782823144735 2133691765816174234717103)
            ·
              refine ⟨3200537648724261352075655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2133691765816174234717103 3200537648724261352075655)
              ·
                refine ⟨4800806473086392028113483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3200537648724261352075655 4800806473086392028113483)
                ·
                  refine ⟨7201209709629588042170225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4800806473086392028113483 7201209709629588042170225)
                  ·
                    refine ⟨5400907282222191031627669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7201209709629588042170225 5400907282222191031627669)
                    ·
                      refine ⟨253167528854165204607547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5400907282222191031627669 253167528854165204607547)
                      ·
                        rfl

theorem cell23_493042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_493042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493042 prefixEnd_493042 := by exact prefixLift 493042
  have htrace : WordTrace (prefixWord ++ tailWord_493042) baseStart_493042 baseEnd_493042 := by
    simpa [prefixWord, tailWord_493042, baseEnd_493042] using wordTrace_append hprefix tailTrace_493042
  have hstable : (prefixWord ++ tailWord_493042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493042).length < 2 ^ (prefixWord ++ tailWord_493042).sum := by decide
  have hdescent : baseEnd_493042 < baseStart_493042 := by decide
  rcases family_descends (prefixWord ++ tailWord_493042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493055 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 4]
def baseStart_493055 : Nat := 118140960795 + 493055 * 2 ^ 59
def prefixEnd_493055 : Nat := 4983230072969 + 3 ^ 40 * 493055 * 2
def baseEnd_493055 : Nat := 253174204102673653744987

theorem tailTrace_493055 : CollatzResearch.WordTrace tailWord_493055 prefixEnd_493055 253174204102673653744987 := by
  unfold tailWord_493055
  simp only [CollatzResearch.WordTrace]
  refine ⟨17983193228753416935040619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11988795485835611290027079 17983193228753416935040619)
  ·
    refine ⟨26974789843130125402560929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17983193228753416935040619 26974789843130125402560929)
    ·
      refine ⟨20231092382347594051920697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26974789843130125402560929 20231092382347594051920697)
      ·
        refine ⟨15173319286760695538940523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20231092382347594051920697 15173319286760695538940523)
        ·
          refine ⟨22759978930141043308410785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15173319286760695538940523 22759978930141043308410785)
          ·
            refine ⟨17069984197605782481308089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22759978930141043308410785 17069984197605782481308089)
            ·
              refine ⟨12802488148204336860981067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17069984197605782481308089 12802488148204336860981067)
              ·
                refine ⟨19203732222306505291471601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12802488148204336860981067 19203732222306505291471601)
                ·
                  refine ⟨14402799166729878968603701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19203732222306505291471601 14402799166729878968603701)
                  ·
                    refine ⟨1350262421880926153306597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14402799166729878968603701 1350262421880926153306597)
                    ·
                      refine ⟨253174204102673653744987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1350262421880926153306597 253174204102673653744987)
                      ·
                        rfl

theorem cell23_493055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_493055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493055 prefixEnd_493055 := by exact prefixLift 493055
  have htrace : WordTrace (prefixWord ++ tailWord_493055) baseStart_493055 baseEnd_493055 := by
    simpa [prefixWord, tailWord_493055, baseEnd_493055] using wordTrace_append hprefix tailTrace_493055
  have hstable : (prefixWord ++ tailWord_493055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493055).length < 2 ^ (prefixWord ++ tailWord_493055).sum := by decide
  have hdescent : baseEnd_493055 < baseStart_493055 := by decide
  rcases family_descends (prefixWord ++ tailWord_493055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493089 : List Nat := [1, 2, 3, 2, 2, 2, 2, 3, 1, 1, 4]
def baseStart_493089 : Nat := 118140960795 + 493089 * 2 ^ 59
def prefixEnd_493089 : Nat := 4983230072969 + 3 ^ 40 * 493089 * 2
def baseEnd_493089 : Nat := 253191662444926520719831

theorem tailTrace_493089 : CollatzResearch.WordTrace tailWord_493089 prefixEnd_493089 253191662444926520719831 := by
  unfold tailWord_493089
  simp only [CollatzResearch.WordTrace]
  refine ⟨17984433310630240741778321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11989622207086827161185547 17984433310630240741778321)
  ·
    refine ⟨13488324982972680556333741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17984433310630240741778321 13488324982972680556333741)
    ·
      refine ⟨5058121868614755208625153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13488324982972680556333741 5058121868614755208625153)
      ·
        refine ⟨3793591401461066406468865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5058121868614755208625153 3793591401461066406468865)
        ·
          refine ⟨2845193551095799804851649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3793591401461066406468865 2845193551095799804851649)
          ·
            refine ⟨2133895163321849853638737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2845193551095799804851649 2133895163321849853638737)
            ·
              refine ⟨1600421372491387390229053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2133895163321849853638737 1600421372491387390229053)
              ·
                refine ⟨600158014684270271335895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1600421372491387390229053 600158014684270271335895)
                ·
                  refine ⟨900237022026405407003843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 600158014684270271335895 900237022026405407003843)
                  ·
                    refine ⟨1350355533039608110505765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 900237022026405407003843 1350355533039608110505765)
                    ·
                      refine ⟨253191662444926520719831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1350355533039608110505765 253191662444926520719831)
                      ·
                        rfl

theorem cell23_493089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_493089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493089 prefixEnd_493089 := by exact prefixLift 493089
  have htrace : WordTrace (prefixWord ++ tailWord_493089) baseStart_493089 baseEnd_493089 := by
    simpa [prefixWord, tailWord_493089, baseEnd_493089] using wordTrace_append hprefix tailTrace_493089
  have hstable : (prefixWord ++ tailWord_493089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493089).length < 2 ^ (prefixWord ++ tailWord_493089).sum := by decide
  have hdescent : baseEnd_493089 < baseStart_493089 := by decide
  rcases family_descends (prefixWord ++ tailWord_493089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493112 : List Nat := [2, 1, 2, 1, 4, 3, 2, 8]
def baseStart_493112 : Nat := 118140960795 + 493112 * 2 ^ 59
def prefixEnd_493112 : Nat := 4983230072969 + 3 ^ 40 * 493112 * 2
def baseEnd_493112 : Nat := 9377906388888145582675

theorem tailTrace_493112 : CollatzResearch.WordTrace tailWord_493112 prefixEnd_493112 9377906388888145582675 := by
  unfold tailWord_493112
  simp only [CollatzResearch.WordTrace]
  refine ⟨8992636094773457834932795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11990181459697943779910393 8992636094773457834932795)
  ·
    refine ⟨13488954142160186752399193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8992636094773457834932795 13488954142160186752399193)
    ·
      refine ⟨10116715606620140064299395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13488954142160186752399193 10116715606620140064299395)
      ·
        refine ⟨15175073409930210096449093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10116715606620140064299395 15175073409930210096449093)
        ·
          refine ⟨2845326264361914393084205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15175073409930210096449093 2845326264361914393084205)
          ·
            refine ⟨1066997349135717897406577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2845326264361914393084205 1066997349135717897406577)
            ·
              refine ⟨800248011851788423054933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1066997349135717897406577 800248011851788423054933)
              ·
                refine ⟨9377906388888145582675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 800248011851788423054933 9377906388888145582675)
                ·
                  rfl

theorem cell23_493112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 8].length) (baseStart_493112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493112 prefixEnd_493112 := by exact prefixLift 493112
  have htrace : WordTrace (prefixWord ++ tailWord_493112) baseStart_493112 baseEnd_493112 := by
    simpa [prefixWord, tailWord_493112, baseEnd_493112] using wordTrace_append hprefix tailTrace_493112
  have hstable : (prefixWord ++ tailWord_493112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493112).length < 2 ^ (prefixWord ++ tailWord_493112).sum := by decide
  have hdescent : baseEnd_493112 < baseStart_493112 := by decide
  rcases family_descends (prefixWord ++ tailWord_493112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493116 : List Nat := [2, 2, 2, 2, 4, 1, 1, 3, 2, 4]
def baseStart_493116 : Nat := 118140960795 + 493116 * 2 ^ 59
def prefixEnd_493116 : Nat := 4983230072969 + 3 ^ 40 * 493116 * 2
def baseEnd_493116 : Nat := 84401842140865971694069

theorem tailTrace_493116 : CollatzResearch.WordTrace tailWord_493116 prefixEnd_493116 84401842140865971694069 := by
  unfold tailWord_493116
  simp only [CollatzResearch.WordTrace]
  refine ⟨8992709040766212176505601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11990278721021616235340801 8992709040766212176505601)
  ·
    refine ⟨6744531780574659132379201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8992709040766212176505601 6744531780574659132379201)
    ·
      refine ⟨5058398835430994349284401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6744531780574659132379201 5058398835430994349284401)
      ·
        refine ⟨3793799126573245761963301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5058398835430994349284401 3793799126573245761963301)
        ·
          refine ⟨711337336232483580368119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3793799126573245761963301 711337336232483580368119)
          ·
            refine ⟨1067006004348725370552179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711337336232483580368119 1067006004348725370552179)
            ·
              refine ⟨1600509006523088055828269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1067006004348725370552179 1600509006523088055828269)
              ·
                refine ⟨600190877446158020935601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1600509006523088055828269 600190877446158020935601)
                ·
                  refine ⟨450143158084618515701701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 600190877446158020935601 450143158084618515701701)
                  ·
                    refine ⟨84401842140865971694069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 450143158084618515701701 84401842140865971694069)
                    ·
                      rfl

theorem cell23_493116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_493116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493116 prefixEnd_493116 := by exact prefixLift 493116
  have htrace : WordTrace (prefixWord ++ tailWord_493116) baseStart_493116 baseEnd_493116 := by
    simpa [prefixWord, tailWord_493116, baseEnd_493116] using wordTrace_append hprefix tailTrace_493116
  have hstable : (prefixWord ++ tailWord_493116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493116).length < 2 ^ (prefixWord ++ tailWord_493116).sum := by decide
  have hdescent : baseEnd_493116 < baseStart_493116 := by decide
  rcases family_descends (prefixWord ++ tailWord_493116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493156 : List Nat := [2, 3, 1, 1, 2, 3, 1, 4, 2, 1, 3]
def baseStart_493156 : Nat := 118140960795 + 493156 * 2 ^ 59
def prefixEnd_493156 : Nat := 4983230072969 + 3 ^ 40 * 493156 * 2
def baseEnd_493156 : Nat := 253226065648777758582023

theorem tailTrace_493156 : CollatzResearch.WordTrace tailWord_493156 prefixEnd_493156 253226065648777758582023 := by
  unfold tailWord_493156
  simp only [CollatzResearch.WordTrace]
  refine ⟨8993438500693755592233661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11991251334258340789644881 8993438500693755592233661)
  ·
    refine ⟨3372539437760158347087623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8993438500693755592233661 3372539437760158347087623)
    ·
      refine ⟨5058809156640237520631435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3372539437760158347087623 5058809156640237520631435)
      ·
        refine ⟨7588213734960356280947153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5058809156640237520631435 7588213734960356280947153)
        ·
          refine ⟨5691160301220267210710365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7588213734960356280947153 5691160301220267210710365)
          ·
            refine ⟨2134185112957600204016387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5691160301220267210710365 2134185112957600204016387)
            ·
              refine ⟨3201277669436400306024581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2134185112957600204016387 3201277669436400306024581)
              ·
                refine ⟨600239563019325057379609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3201277669436400306024581 600239563019325057379609)
                ·
                  refine ⟨450179672264493793034707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 600239563019325057379609 450179672264493793034707)
                  ·
                    refine ⟨675269508396740689552061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 450179672264493793034707 675269508396740689552061)
                    ·
                      refine ⟨253226065648777758582023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 675269508396740689552061 253226065648777758582023)
                      ·
                        rfl

theorem cell23_493156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_493156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493156 prefixEnd_493156 := by exact prefixLift 493156
  have htrace : WordTrace (prefixWord ++ tailWord_493156) baseStart_493156 baseEnd_493156 := by
    simpa [prefixWord, tailWord_493156, baseEnd_493156] using wordTrace_append hprefix tailTrace_493156
  have hstable : (prefixWord ++ tailWord_493156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493156).length < 2 ^ (prefixWord ++ tailWord_493156).sum := by decide
  have hdescent : baseEnd_493156 < baseStart_493156 := by decide
  rcases family_descends (prefixWord ++ tailWord_493156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493157 : List Nat := [1, 3, 1, 3, 3, 3, 2, 2, 1, 2, 2]
def baseStart_493157 : Nat := 118140960795 + 493157 * 2 ^ 59
def prefixEnd_493157 : Nat := 4983230072969 + 3 ^ 40 * 493157 * 2
def baseEnd_493157 : Nat := 253226579129432254669519

theorem tailTrace_493157 : CollatzResearch.WordTrace tailWord_493157 prefixEnd_493157 253226579129432254669519 := by
  unfold tailWord_493157
  simp only [CollatzResearch.WordTrace]
  refine ⟨17986913474383888355253725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11991275649589258903502483 17986913474383888355253725)
  ·
    refine ⟨6745092552893958133220147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17986913474383888355253725 6745092552893958133220147)
    ·
      refine ⟨10117638829340937199830221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6745092552893958133220147 10117638829340937199830221)
      ·
        refine ⟨3794114561002851449936333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10117638829340937199830221 3794114561002851449936333)
        ·
          refine ⟨1422792960376069293726125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3794114561002851449936333 1422792960376069293726125)
          ·
            refine ⟨533547360141025985147297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1422792960376069293726125 533547360141025985147297)
            ·
              refine ⟨400160520105769488860473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533547360141025985147297 400160520105769488860473)
              ·
                refine ⟨300120390079327116645355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 400160520105769488860473 300120390079327116645355)
                ·
                  refine ⟨450180585118990674968033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 300120390079327116645355 450180585118990674968033)
                  ·
                    refine ⟨337635438839243006226025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 450180585118990674968033 337635438839243006226025)
                    ·
                      refine ⟨253226579129432254669519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 337635438839243006226025 253226579129432254669519)
                      ·
                        rfl

theorem cell23_493157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_493157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493157 prefixEnd_493157 := by exact prefixLift 493157
  have htrace : WordTrace (prefixWord ++ tailWord_493157) baseStart_493157 baseEnd_493157 := by
    simpa [prefixWord, tailWord_493157, baseEnd_493157] using wordTrace_append hprefix tailTrace_493157
  have hstable : (prefixWord ++ tailWord_493157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493157).length < 2 ^ (prefixWord ++ tailWord_493157).sum := by decide
  have hdescent : baseEnd_493157 < baseStart_493157 := by decide
  rcases family_descends (prefixWord ++ tailWord_493157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493173 : List Nat := [1, 3, 4, 2, 1, 1, 2, 3, 2, 1, 3]
def baseStart_493173 : Nat := 118140960795 + 493173 * 2 ^ 59
def prefixEnd_493173 : Nat := 4983230072969 + 3 ^ 40 * 493173 * 2
def baseEnd_493173 : Nat := 253234794819904192069445

theorem tailTrace_493173 : CollatzResearch.WordTrace tailWord_493173 prefixEnd_493173 253234794819904192069445 := by
  unfold tailWord_493173
  simp only [CollatzResearch.WordTrace]
  refine ⟨17987497042325923087836173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11991664694883948725224115 17987497042325923087836173)
  ·
    refine ⟨6745311390872221157938565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17987497042325923087836173 6745311390872221157938565)
    ·
      refine ⟨1264745885788541467113481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6745311390872221157938565 1264745885788541467113481)
      ·
        refine ⟨948559414341406100335111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1264745885788541467113481 948559414341406100335111)
        ·
          refine ⟨1422839121512109150502667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948559414341406100335111 1422839121512109150502667)
          ·
            refine ⟨2134258682268163725754001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1422839121512109150502667 2134258682268163725754001)
            ·
              refine ⟨1600694011701122794315501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2134258682268163725754001 1600694011701122794315501)
              ·
                refine ⟨600260254387921047868313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1600694011701122794315501 600260254387921047868313)
                ·
                  refine ⟨450195190790940785901235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 600260254387921047868313 450195190790940785901235)
                  ·
                    refine ⟨675292786186411178851853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 450195190790940785901235 675292786186411178851853)
                    ·
                      refine ⟨253234794819904192069445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 675292786186411178851853 253234794819904192069445)
                      ·
                        rfl

theorem cell23_493173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_493173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493173 prefixEnd_493173 := by exact prefixLift 493173
  have htrace : WordTrace (prefixWord ++ tailWord_493173) baseStart_493173 baseEnd_493173 := by
    simpa [prefixWord, tailWord_493173, baseEnd_493173] using wordTrace_append hprefix tailTrace_493173
  have hstable : (prefixWord ++ tailWord_493173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493173).length < 2 ^ (prefixWord ++ tailWord_493173).sum := by decide
  have hdescent : baseEnd_493173 < baseStart_493173 := by decide
  rcases family_descends (prefixWord ++ tailWord_493173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493196 : List Nat := [2, 2, 1, 2, 1, 1, 4, 2, 4, 2, 2]
def baseStart_493196 : Nat := 118140960795 + 493196 * 2 ^ 59
def prefixEnd_493196 : Nat := 4983230072969 + 3 ^ 40 * 493196 * 2
def baseEnd_493196 : Nat := 253246604874957602081839

theorem tailTrace_493196 : CollatzResearch.WordTrace tailWord_493196 prefixEnd_493196 253246604874957602081839 := by
  unfold tailWord_493196
  simp only [CollatzResearch.WordTrace]
  refine ⟨8994167960621299007961721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11992223947495065343948961 8994167960621299007961721)
  ·
    refine ⟨6745625970465974255971291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8994167960621299007961721 6745625970465974255971291)
    ·
      refine ⟨10118438955698961383956937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6745625970465974255971291 10118438955698961383956937)
      ·
        refine ⟨7588829216774221037967703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10118438955698961383956937 7588829216774221037967703)
        ·
          refine ⟨11383243825161331556951555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7588829216774221037967703 11383243825161331556951555)
          ·
            refine ⟨17074865737741997335427333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11383243825161331556951555 17074865737741997335427333)
            ·
              refine ⟨3201537325826624500392625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17074865737741997335427333 3201537325826624500392625)
              ·
                refine ⟨2401152994369968375294469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3201537325826624500392625 2401152994369968375294469)
                ·
                  refine ⟨450216186444369070367713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2401152994369968375294469 450216186444369070367713)
                  ·
                    refine ⟨337662139833276802775785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 450216186444369070367713 337662139833276802775785)
                    ·
                      refine ⟨253246604874957602081839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 337662139833276802775785 253246604874957602081839)
                      ·
                        rfl

theorem cell23_493196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 4, 2, 2].length) (baseStart_493196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493196 prefixEnd_493196 := by exact prefixLift 493196
  have htrace : WordTrace (prefixWord ++ tailWord_493196) baseStart_493196 baseEnd_493196 := by
    simpa [prefixWord, tailWord_493196, baseEnd_493196] using wordTrace_append hprefix tailTrace_493196
  have hstable : (prefixWord ++ tailWord_493196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493196).length < 2 ^ (prefixWord ++ tailWord_493196).sum := by decide
  have hdescent : baseEnd_493196 < baseStart_493196 := by decide
  rcases family_descends (prefixWord ++ tailWord_493196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493219 : List Nat := [1, 1, 1, 4, 1, 1, 3, 6, 5]
def baseStart_493219 : Nat := 118140960795 + 493219 * 2 ^ 59
def prefixEnd_493219 : Nat := 4983230072969 + 3 ^ 40 * 493219 * 2
def baseEnd_493219 : Nat := 28139823881112334677137

theorem tailTrace_493219 : CollatzResearch.WordTrace tailWord_493219 prefixEnd_493219 28139823881112334677137 := by
  unfold tailWord_493219
  simp only [CollatzResearch.WordTrace]
  refine ⟨17989174800159272944010711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11992783200106181962673807 17989174800159272944010711)
  ·
    refine ⟨26983762200238909416016067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17989174800159272944010711 26983762200238909416016067)
    ·
      refine ⟨40475643300358364124024101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26983762200238909416016067 40475643300358364124024101)
      ·
        refine ⟨7589183118817193273254519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40475643300358364124024101 7589183118817193273254519)
        ·
          refine ⟨11383774678225789909881779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7589183118817193273254519 11383774678225789909881779)
          ·
            refine ⟨17075662017338684864822669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11383774678225789909881779 17075662017338684864822669)
            ·
              refine ⟨6403373256502006824308501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17075662017338684864822669 6403373256502006824308501)
              ·
                refine ⟨300158121398531569889461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6403373256502006824308501 300158121398531569889461)
                ·
                  refine ⟨28139823881112334677137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 300158121398531569889461 28139823881112334677137)
                  ·
                    rfl

theorem cell23_493219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 6, 5].length) (baseStart_493219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493219 prefixEnd_493219 := by exact prefixLift 493219
  have htrace : WordTrace (prefixWord ++ tailWord_493219) baseStart_493219 baseEnd_493219 := by
    simpa [prefixWord, tailWord_493219, baseEnd_493219] using wordTrace_append hprefix tailTrace_493219
  have hstable : (prefixWord ++ tailWord_493219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493219).length < 2 ^ (prefixWord ++ tailWord_493219).sum := by decide
  have hdescent : baseEnd_493219 < baseStart_493219 := by decide
  rcases family_descends (prefixWord ++ tailWord_493219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493224 : List Nat := [2, 1, 7, 1, 1, 1, 3, 1, 2, 1, 3]
def baseStart_493224 : Nat := 118140960795 + 493224 * 2 ^ 59
def prefixEnd_493224 : Nat := 4983230072969 + 3 ^ 40 * 493224 * 2
def baseEnd_493224 : Nat := 253260982333283492531711

theorem tailTrace_493224 : CollatzResearch.WordTrace tailWord_493224 prefixEnd_493224 253260982333283492531711 := by
  unfold tailWord_493224
  simp only [CollatzResearch.WordTrace]
  refine ⟨8994678582570579398971363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11992904776760772531961817 8994678582570579398971363)
  ·
    refine ⟨13492017873855869098457045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8994678582570579398971363 13492017873855869098457045)
    ·
      refine ⟨316219168918496931995087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 13492017873855869098457045 316219168918496931995087)
      ·
        refine ⟨474328753377745397992631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316219168918496931995087 474328753377745397992631)
        ·
          refine ⟨711493130066618096988947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474328753377745397992631 711493130066618096988947)
          ·
            refine ⟨1067239695099927145483421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711493130066618096988947 1067239695099927145483421)
            ·
              refine ⟨400214885662472679556283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1067239695099927145483421 400214885662472679556283)
              ·
                refine ⟨600322328493709019334425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400214885662472679556283 600322328493709019334425)
                ·
                  refine ⟨450241746370281764500819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 600322328493709019334425 450241746370281764500819)
                  ·
                    refine ⟨675362619555422646751229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 450241746370281764500819 675362619555422646751229)
                    ·
                      refine ⟨253260982333283492531711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 675362619555422646751229 253260982333283492531711)
                      ·
                        rfl

theorem cell23_493224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_493224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493224 prefixEnd_493224 := by exact prefixLift 493224
  have htrace : WordTrace (prefixWord ++ tailWord_493224) baseStart_493224 baseEnd_493224 := by
    simpa [prefixWord, tailWord_493224, baseEnd_493224] using wordTrace_append hprefix tailTrace_493224
  have hstable : (prefixWord ++ tailWord_493224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493224).length < 2 ^ (prefixWord ++ tailWord_493224).sum := by decide
  have hdescent : baseEnd_493224 < baseStart_493224 := by decide
  rcases family_descends (prefixWord ++ tailWord_493224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493232 : List Nat := [2, 1, 1, 1, 2, 1, 5, 2, 1, 7]
def baseStart_493232 : Nat := 118140960795 + 493232 * 2 ^ 59
def prefixEnd_493232 : Nat := 4983230072969 + 3 ^ 40 * 493232 * 2
def baseEnd_493232 : Nat := 84421696726173153743891

theorem tailTrace_493232 : CollatzResearch.WordTrace tailWord_493232 prefixEnd_493232 84421696726173153743891 := by
  unfold tailWord_493232
  simp only [CollatzResearch.WordTrace]
  refine ⟨8994824474556088082116975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11993099299408117442822633 8994824474556088082116975)
  ·
    refine ⟨13492236711834132123175463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8994824474556088082116975 13492236711834132123175463)
    ·
      refine ⟨20238355067751198184763195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13492236711834132123175463 20238355067751198184763195)
      ·
        refine ⟨30357532601626797277144793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20238355067751198184763195 30357532601626797277144793)
        ·
          refine ⟨22768149451220097957858595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30357532601626797277144793 22768149451220097957858595)
          ·
            refine ⟨34152224176830146936787893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22768149451220097957858595 34152224176830146936787893)
            ·
              refine ⟨3201771016577826275323865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34152224176830146936787893 3201771016577826275323865)
              ·
                refine ⟨2401328262433369706492899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3201771016577826275323865 2401328262433369706492899)
                ·
                  refine ⟨3601992393650054559739349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2401328262433369706492899 3601992393650054559739349)
                  ·
                    refine ⟨84421696726173153743891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3601992393650054559739349 84421696726173153743891)
                    ·
                      rfl

theorem cell23_493232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 1, 7].length) (baseStart_493232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493232 prefixEnd_493232 := by exact prefixLift 493232
  have htrace : WordTrace (prefixWord ++ tailWord_493232) baseStart_493232 baseEnd_493232 := by
    simpa [prefixWord, tailWord_493232, baseEnd_493232] using wordTrace_append hprefix tailTrace_493232
  have hstable : (prefixWord ++ tailWord_493232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493232).length < 2 ^ (prefixWord ++ tailWord_493232).sum := by decide
  have hdescent : baseEnd_493232 < baseStart_493232 := by decide
  rcases family_descends (prefixWord ++ tailWord_493232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493250 : List Nat := [3, 5, 1, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_493250 : Nat := 118140960795 + 493250 * 2 ^ 59
def prefixEnd_493250 : Nat := 4983230072969 + 3 ^ 40 * 493250 * 2
def baseEnd_493250 : Nat := 253274332830300390806591

theorem tailTrace_493250 : CollatzResearch.WordTrace tailWord_493250 prefixEnd_493250 253274332830300390806591 := by
  unfold tailWord_493250
  simp only [CollatzResearch.WordTrace]
  refine ⟨4497576365761741309597301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11993536975364643492259469 4497576365761741309597301)
  ·
    refine ⟨421647784290163247774747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4497576365761741309597301 421647784290163247774747)
    ·
      refine ⟨632471676435244871662121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421647784290163247774747 632471676435244871662121)
      ·
        refine ⟨474353757326433653746591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 632471676435244871662121 474353757326433653746591)
        ·
          refine ⟨711530635989650480619887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474353757326433653746591 711530635989650480619887)
          ·
            refine ⟨1067295953984475720929831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711530635989650480619887 1067295953984475720929831)
            ·
              refine ⟨1600943930976713581394747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1067295953984475720929831 1600943930976713581394747)
              ·
                refine ⟨2401415896465070372092121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1600943930976713581394747 2401415896465070372092121)
                ·
                  refine ⟨1801061922348802779069091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2401415896465070372092121 1801061922348802779069091)
                  ·
                    refine ⟨2701592883523204168603637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1801061922348802779069091 2701592883523204168603637)
                    ·
                      refine ⟨253274332830300390806591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2701592883523204168603637 253274332830300390806591)
                      ·
                        rfl

theorem cell23_493250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_493250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493250 prefixEnd_493250 := by exact prefixLift 493250
  have htrace : WordTrace (prefixWord ++ tailWord_493250) baseStart_493250 baseEnd_493250 := by
    simpa [prefixWord, tailWord_493250, baseEnd_493250] using wordTrace_append hprefix tailTrace_493250
  have hstable : (prefixWord ++ tailWord_493250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493250).length < 2 ^ (prefixWord ++ tailWord_493250).sum := by decide
  have hdescent : baseEnd_493250 < baseStart_493250 := by decide
  rcases family_descends (prefixWord ++ tailWord_493250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493266 : List Nat := [3, 2, 2, 2, 2, 2, 1, 2, 2, 5]
def baseStart_493266 : Nat := 118140960795 + 493266 * 2 ^ 59
def prefixEnd_493266 : Nat := 4983230072969 + 3 ^ 40 * 493266 * 2
def baseEnd_493266 : Nat := 84427516173590776068839

theorem tailTrace_493266 : CollatzResearch.WordTrace tailWord_493266 prefixEnd_493266 84427516173590776068839 := by
  unfold tailWord_493266
  simp only [CollatzResearch.WordTrace]
  refine ⟨4497722257747249992742913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11993926020659333313981101 4497722257747249992742913)
  ·
    refine ⟨3373291693310437494557185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4497722257747249992742913 3373291693310437494557185)
    ·
      refine ⟨2529968769982828120917889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3373291693310437494557185 2529968769982828120917889)
      ·
        refine ⟨1897476577487121090688417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2529968769982828120917889 1897476577487121090688417)
        ·
          refine ⟨1423107433115340818016313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1897476577487121090688417 1423107433115340818016313)
          ·
            refine ⟨1067330574836505613512235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1423107433115340818016313 1067330574836505613512235)
            ·
              refine ⟨1600995862254758420268353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1067330574836505613512235 1600995862254758420268353)
              ·
                refine ⟨1200746896691068815201265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1600995862254758420268353 1200746896691068815201265)
                ·
                  refine ⟨900560172518301611400949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1200746896691068815201265 900560172518301611400949)
                  ·
                    refine ⟨84427516173590776068839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 900560172518301611400949 84427516173590776068839)
                    ·
                      rfl

theorem cell23_493266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_493266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493266 prefixEnd_493266 := by exact prefixLift 493266
  have htrace : WordTrace (prefixWord ++ tailWord_493266) baseStart_493266 baseEnd_493266 := by
    simpa [prefixWord, tailWord_493266, baseEnd_493266] using wordTrace_append hprefix tailTrace_493266
  have hstable : (prefixWord ++ tailWord_493266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493266).length < 2 ^ (prefixWord ++ tailWord_493266).sum := by decide
  have hdescent : baseEnd_493266 < baseStart_493266 := by decide
  rcases family_descends (prefixWord ++ tailWord_493266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493270 : List Nat := [5, 2, 1, 3, 1, 2, 1, 1, 7]
def baseStart_493270 : Nat := 118140960795 + 493270 * 2 ^ 59
def prefixEnd_493270 : Nat := 4983230072969 + 3 ^ 40 * 493270 * 2
def baseEnd_493270 : Nat := 28142733604821145839611

theorem tailTrace_493270 : CollatzResearch.WordTrace tailWord_493270 prefixEnd_493270 28142733604821145839611 := by
  unfold tailWord_493270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1124439682685906790882329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11994023281983005769411509 1124439682685906790882329)
  ·
    refine ⟨843329762014430093161747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1124439682685906790882329 843329762014430093161747)
    ·
      refine ⟨1264994643021645139742621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 843329762014430093161747 1264994643021645139742621)
      ·
        refine ⟨474372991133116927403483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1264994643021645139742621 474372991133116927403483)
        ·
          refine ⟨711559486699675391105225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474372991133116927403483 711559486699675391105225)
          ·
            refine ⟨533669615024756543328919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 711559486699675391105225 533669615024756543328919)
            ·
              refine ⟨800504422537134814993379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533669615024756543328919 800504422537134814993379)
              ·
                refine ⟨1200756633805702222490069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 800504422537134814993379 1200756633805702222490069)
                ·
                  refine ⟨28142733604821145839611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1200756633805702222490069 28142733604821145839611)
                  ·
                    rfl

theorem cell23_493270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_493270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493270 prefixEnd_493270 := by exact prefixLift 493270
  have htrace : WordTrace (prefixWord ++ tailWord_493270) baseStart_493270 baseEnd_493270 := by
    simpa [prefixWord, tailWord_493270, baseEnd_493270] using wordTrace_append hprefix tailTrace_493270
  have hstable : (prefixWord ++ tailWord_493270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493270).length < 2 ^ (prefixWord ++ tailWord_493270).sum := by decide
  have hdescent : baseEnd_493270 < baseStart_493270 := by decide
  rcases family_descends (prefixWord ++ tailWord_493270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493289 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 6, 2, 3]
def baseStart_493289 : Nat := 118140960795 + 493289 * 2 ^ 59
def prefixEnd_493289 : Nat := 4983230072969 + 3 ^ 40 * 493289 * 2
def baseEnd_493289 : Nat := 253294358575825738218911

theorem tailTrace_493289 : CollatzResearch.WordTrace tailWord_493289 prefixEnd_493289 253294358575825738218911 := by
  unfold tailWord_493289
  simp only [CollatzResearch.WordTrace]
  refine ⟨17991727909905674899058921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11994485273270449932705947 17991727909905674899058921)
  ·
    refine ⟨13493795932429256174294191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17991727909905674899058921 13493795932429256174294191)
    ·
      refine ⟨20240693898643884261441287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13493795932429256174294191 20240693898643884261441287)
      ·
        refine ⟨30361040847965826392161931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20240693898643884261441287 30361040847965826392161931)
        ·
          refine ⟨45541561271948739588242897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30361040847965826392161931 45541561271948739588242897)
          ·
            refine ⟨34156170953961554691182173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45541561271948739588242897 34156170953961554691182173)
            ·
              refine ⟨12808564107735583009193315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34156170953961554691182173 12808564107735583009193315)
              ·
                refine ⟨19212846161603374513789973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12808564107735583009193315 19212846161603374513789973)
                ·
                  refine ⟨900602163825158180333905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19212846161603374513789973 900602163825158180333905)
                  ·
                    refine ⟨675451622868868635250429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 900602163825158180333905 675451622868868635250429)
                    ·
                      refine ⟨253294358575825738218911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 675451622868868635250429 253294358575825738218911)
                      ·
                        rfl

theorem cell23_493289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 2, 3].length) (baseStart_493289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493289 prefixEnd_493289 := by exact prefixLift 493289
  have htrace : WordTrace (prefixWord ++ tailWord_493289) baseStart_493289 baseEnd_493289 := by
    simpa [prefixWord, tailWord_493289, baseEnd_493289] using wordTrace_append hprefix tailTrace_493289
  have hstable : (prefixWord ++ tailWord_493289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493289).length < 2 ^ (prefixWord ++ tailWord_493289).sum := by decide
  have hdescent : baseEnd_493289 < baseStart_493289 := by decide
  rcases family_descends (prefixWord ++ tailWord_493289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493300 : List Nat := [2, 6, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_493300 : Nat := 118140960795 + 493300 * 2 ^ 59
def prefixEnd_493300 : Nat := 4983230072969 + 3 ^ 40 * 493300 * 2
def baseEnd_493300 : Nat := 84433335621008398393787

theorem tailTrace_493300 : CollatzResearch.WordTrace tailWord_493300 prefixEnd_493300 84433335621008398393787 := by
  unfold tailWord_493300
  simp only [CollatzResearch.WordTrace]
  refine ⟨8996064556432911888854677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11994752741910549185139569 8996064556432911888854677)
  ·
    refine ⟨421690526082792744790063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8996064556432911888854677 421690526082792744790063)
    ·
      refine ⟨632535789124189117185095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421690526082792744790063 632535789124189117185095)
      ·
        refine ⟨948803683686283675777643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632535789124189117185095 948803683686283675777643)
        ·
          refine ⟨1423205525529425513666465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948803683686283675777643 1423205525529425513666465)
          ·
            refine ⟨1067404144147069135249849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1423205525529425513666465 1067404144147069135249849)
            ·
              refine ⟨800553108110301851437387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1067404144147069135249849 800553108110301851437387)
              ·
                refine ⟨1200829662165452777156081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 800553108110301851437387 1200829662165452777156081)
                ·
                  refine ⟨900622246624089582867061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1200829662165452777156081 900622246624089582867061)
                  ·
                    refine ⟨84433335621008398393787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 900622246624089582867061 84433335621008398393787)
                    ·
                      rfl

theorem cell23_493300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_493300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493300 prefixEnd_493300 := by exact prefixLift 493300
  have htrace : WordTrace (prefixWord ++ tailWord_493300) baseStart_493300 baseEnd_493300 := by
    simpa [prefixWord, tailWord_493300, baseEnd_493300] using wordTrace_append hprefix tailTrace_493300
  have hstable : (prefixWord ++ tailWord_493300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493300).length < 2 ^ (prefixWord ++ tailWord_493300).sum := by decide
  have hdescent : baseEnd_493300 < baseStart_493300 := by decide
  rcases family_descends (prefixWord ++ tailWord_493300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493363 : List Nat := [1, 1, 1, 2, 7, 1, 1, 1, 1, 5, 2]
def baseStart_493363 : Nat := 118140960795 + 493363 * 2 ^ 59
def prefixEnd_493363 : Nat := 4983230072969 + 3 ^ 40 * 493363 * 2
def baseEnd_493363 : Nat := 253332356144258448693571

theorem tailTrace_493363 : CollatzResearch.WordTrace tailWord_493363 prefixEnd_493363 253332356144258448693571 := by
  unfold tailWord_493363
  simp only [CollatzResearch.WordTrace]
  refine ⟨17994426911637585537252743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11996284607758390358168495 17994426911637585537252743)
  ·
    refine ⟨26991640367456378305879115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17994426911637585537252743 26991640367456378305879115)
    ·
      refine ⟨40487460551184567458818673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26991640367456378305879115 40487460551184567458818673)
      ·
        refine ⟨30365595413388425594114005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40487460551184567458818673 30365595413388425594114005)
        ·
          refine ⟨711693642501291224862047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 30365595413388425594114005 711693642501291224862047)
          ·
            refine ⟨1067540463751936837293071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711693642501291224862047 1067540463751936837293071)
            ·
              refine ⟨1601310695627905255939607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1067540463751936837293071 1601310695627905255939607)
              ·
                refine ⟨2401966043441857883909411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1601310695627905255939607 2401966043441857883909411)
                ·
                  refine ⟨3602949065162786825864117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2401966043441857883909411 3602949065162786825864117)
                  ·
                    refine ⟨337776474859011264924761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3602949065162786825864117 337776474859011264924761)
                    ·
                      refine ⟨253332356144258448693571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 337776474859011264924761 253332356144258448693571)
                      ·
                        rfl

theorem cell23_493363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 5, 2].length) (baseStart_493363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493363 prefixEnd_493363 := by exact prefixLift 493363
  have htrace : WordTrace (prefixWord ++ tailWord_493363) baseStart_493363 baseEnd_493363 := by
    simpa [prefixWord, tailWord_493363, baseEnd_493363] using wordTrace_append hprefix tailTrace_493363
  have hstable : (prefixWord ++ tailWord_493363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493363).length < 2 ^ (prefixWord ++ tailWord_493363).sum := by decide
  have hdescent : baseEnd_493363 < baseStart_493363 := by decide
  rcases family_descends (prefixWord ++ tailWord_493363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493370 : List Nat := [3, 1, 1, 1, 5, 1, 1, 5, 1, 1, 3]
def baseStart_493370 : Nat := 118140960795 + 493370 * 2 ^ 59
def prefixEnd_493370 : Nat := 4983230072969 + 3 ^ 40 * 493370 * 2
def baseEnd_493370 : Nat := 253335950508839921306039

theorem tailTrace_493370 : CollatzResearch.WordTrace tailWord_493370 prefixEnd_493370 253335950508839921306039 := by
  unfold tailWord_493370
  simp only [CollatzResearch.WordTrace]
  refine ⟨4498670555653056433189391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11996454815074817155171709 4498670555653056433189391)
  ·
    refine ⟨6748005833479584649784087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4498670555653056433189391 6748005833479584649784087)
    ·
      refine ⟨10122008750219376974676131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6748005833479584649784087 10122008750219376974676131)
      ·
        refine ⟨15183013125329065462014197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10122008750219376974676131 15183013125329065462014197)
        ·
          refine ⟨1423407480499599887063831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15183013125329065462014197 1423407480499599887063831)
          ·
            refine ⟨2135111220749399830595747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1423407480499599887063831 2135111220749399830595747)
            ·
              refine ⟨3202666831124099745893621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2135111220749399830595747 3202666831124099745893621)
              ·
                refine ⟨300250015417884351177527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3202666831124099745893621 300250015417884351177527)
                ·
                  refine ⟨450375023126826526766291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 300250015417884351177527 450375023126826526766291)
                  ·
                    refine ⟨675562534690239790149437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 450375023126826526766291 675562534690239790149437)
                    ·
                      refine ⟨253335950508839921306039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 675562534690239790149437 253335950508839921306039)
                      ·
                        rfl

theorem cell23_493370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 5, 1, 1, 3].length) (baseStart_493370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493370 prefixEnd_493370 := by exact prefixLift 493370
  have htrace : WordTrace (prefixWord ++ tailWord_493370) baseStart_493370 baseEnd_493370 := by
    simpa [prefixWord, tailWord_493370, baseEnd_493370] using wordTrace_append hprefix tailTrace_493370
  have hstable : (prefixWord ++ tailWord_493370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493370).length < 2 ^ (prefixWord ++ tailWord_493370).sum := by decide
  have hdescent : baseEnd_493370 < baseStart_493370 := by decide
  rcases family_descends (prefixWord ++ tailWord_493370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493373 : List Nat := [1, 4, 1, 4, 1, 2, 1, 3, 1, 5]
def baseStart_493373 : Nat := 118140960795 + 493373 * 2 ^ 59
def prefixEnd_493373 : Nat := 4983230072969 + 3 ^ 40 * 493373 * 2
def baseEnd_493373 : Nat := 84445830316934469856175

theorem tailTrace_493373 : CollatzResearch.WordTrace tailWord_493373 prefixEnd_493373 84445830316934469856175 := by
  unfold tailWord_493373
  simp only [CollatzResearch.WordTrace]
  refine ⟨17994791641601357245116773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11996527761067571496744515 17994791641601357245116773)
  ·
    refine ⟨3374023432800254483459395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17994791641601357245116773 3374023432800254483459395)
    ·
      refine ⟨5061035149200381725189093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3374023432800254483459395 5061035149200381725189093)
      ·
        refine ⟨948944090475071573472955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5061035149200381725189093 948944090475071573472955)
        ·
          refine ⟨1423416135712607360209433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 948944090475071573472955 1423416135712607360209433)
          ·
            refine ⟨1067562101784455520157075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1423416135712607360209433 1067562101784455520157075)
            ·
              refine ⟨1601343152676683280235613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1067562101784455520157075 1601343152676683280235613)
              ·
                refine ⟨600503682253756230088355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1601343152676683280235613 600503682253756230088355)
                ·
                  refine ⟨900755523380634345132533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 600503682253756230088355 900755523380634345132533)
                  ·
                    refine ⟨84445830316934469856175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 900755523380634345132533 84445830316934469856175)
                    ·
                      rfl

theorem cell23_493373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_493373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493373 prefixEnd_493373 := by exact prefixLift 493373
  have htrace : WordTrace (prefixWord ++ tailWord_493373) baseStart_493373 baseEnd_493373 := by
    simpa [prefixWord, tailWord_493373, baseEnd_493373] using wordTrace_append hprefix tailTrace_493373
  have hstable : (prefixWord ++ tailWord_493373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493373).length < 2 ^ (prefixWord ++ tailWord_493373).sum := by decide
  have hdescent : baseEnd_493373 < baseStart_493373 := by decide
  rcases family_descends (prefixWord ++ tailWord_493373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493386 : List Nat := [3, 1, 2, 1, 1, 1, 5, 1, 4, 4]
def baseStart_493386 : Nat := 118140960795 + 493386 * 2 ^ 59
def prefixEnd_493386 : Nat := 4983230072969 + 3 ^ 40 * 493386 * 2
def baseEnd_493386 : Nat := 84448055399770619568655

theorem tailTrace_493386 : CollatzResearch.WordTrace tailWord_493386 prefixEnd_493386 84448055399770619568655 := by
  unfold tailWord_493386
  simp only [CollatzResearch.WordTrace]
  refine ⟨4498816447638565116335003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11996843860369506976893341 4498816447638565116335003)
  ·
    refine ⟨6748224671457847674502505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4498816447638565116335003 6748224671457847674502505)
    ·
      refine ⟨5061168503593385755876879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6748224671457847674502505 5061168503593385755876879)
      ·
        refine ⟨7591752755390078633815319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5061168503593385755876879 7591752755390078633815319)
        ·
          refine ⟨11387629133085117950722979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7591752755390078633815319 11387629133085117950722979)
          ·
            refine ⟨17081443699627676926084469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11387629133085117950722979 17081443699627676926084469)
            ·
              refine ⟨1601385346840094711820419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17081443699627676926084469 1601385346840094711820419)
              ·
                refine ⟨2402078020260142067730629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1601385346840094711820419 2402078020260142067730629)
                ·
                  refine ⟨450389628798776637699493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2402078020260142067730629 450389628798776637699493)
                  ·
                    refine ⟨84448055399770619568655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 450389628798776637699493 84448055399770619568655)
                    ·
                      rfl

theorem cell23_493386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_493386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493386 prefixEnd_493386 := by exact prefixLift 493386
  have htrace : WordTrace (prefixWord ++ tailWord_493386) baseStart_493386 baseEnd_493386 := by
    simpa [prefixWord, tailWord_493386, baseEnd_493386] using wordTrace_append hprefix tailTrace_493386
  have hstable : (prefixWord ++ tailWord_493386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493386).length < 2 ^ (prefixWord ++ tailWord_493386).sum := by decide
  have hdescent : baseEnd_493386 < baseStart_493386 := by decide
  rcases family_descends (prefixWord ++ tailWord_493386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493396 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 3, 1, 5]
def baseStart_493396 : Nat := 118140960795 + 493396 * 2 ^ 59
def prefixEnd_493396 : Nat := 4983230072969 + 3 ^ 40 * 493396 * 2
def baseEnd_493396 : Nat := 253349301005856819580919

theorem tailTrace_493396 : CollatzResearch.WordTrace tailWord_493396 prefixEnd_493396 253349301005856819580919 := by
  unfold tailWord_493396
  simp only [CollatzResearch.WordTrace]
  refine ⟨8997815260259016086602021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11997087013678688115469361 8997815260259016086602021)
  ·
    refine ⟨1687090361298565516237879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8997815260259016086602021 1687090361298565516237879)
    ·
      refine ⟨2530635541947848274356819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1687090361298565516237879 2530635541947848274356819)
      ·
        refine ⟨3795953312921772411535229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2530635541947848274356819 3795953312921772411535229)
        ·
          refine ⟨1423482492345664654325711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3795953312921772411535229 1423482492345664654325711)
          ·
            refine ⟨2135223738518496981488567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1423482492345664654325711 2135223738518496981488567)
            ·
              refine ⟨3202835607777745472232851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2135223738518496981488567 3202835607777745472232851)
              ·
                refine ⟨4804253411666618208349277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3202835607777745472232851 4804253411666618208349277)
                ·
                  refine ⟨1801595029374981828130979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4804253411666618208349277 1801595029374981828130979)
                  ·
                    refine ⟨2702392544062472742196469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1801595029374981828130979 2702392544062472742196469)
                    ·
                      refine ⟨253349301005856819580919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2702392544062472742196469 253349301005856819580919)
                      ·
                        rfl

theorem cell23_493396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_493396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493396 prefixEnd_493396 := by exact prefixLift 493396
  have htrace : WordTrace (prefixWord ++ tailWord_493396) baseStart_493396 baseEnd_493396 := by
    simpa [prefixWord, tailWord_493396, baseEnd_493396] using wordTrace_append hprefix tailTrace_493396
  have hstable : (prefixWord ++ tailWord_493396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493396).length < 2 ^ (prefixWord ++ tailWord_493396).sum := by decide
  have hdescent : baseEnd_493396 < baseStart_493396 := by decide
  rcases family_descends (prefixWord ++ tailWord_493396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493410 : List Nat := [3, 3, 2, 1, 2, 2, 2, 2, 1, 1, 4]
def baseStart_493410 : Nat := 118140960795 + 493410 * 2 ^ 59
def prefixEnd_493410 : Nat := 4983230072969 + 3 ^ 40 * 493410 * 2
def baseEnd_493410 : Nat := 253356489735019764805855

theorem tailTrace_493410 : CollatzResearch.WordTrace tailWord_493410 prefixEnd_493410 253356489735019764805855 := by
  unfold tailWord_493410
  simp only [CollatzResearch.WordTrace]
  refine ⟨4499035285616828141053421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11997427428311541709475789 4499035285616828141053421)
  ·
    refine ⟨1687138232106310552895033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4499035285616828141053421 1687138232106310552895033)
    ·
      refine ⟨1265353674079732914671275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1687138232106310552895033 1265353674079732914671275)
      ·
        refine ⟨1898030511119599372006913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1265353674079732914671275 1898030511119599372006913)
        ·
          refine ⟨1423522883339699529005185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1898030511119599372006913 1423522883339699529005185)
          ·
            refine ⟨1067642162504774646753889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1423522883339699529005185 1067642162504774646753889)
            ·
              refine ⟨800731621878580985065417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1067642162504774646753889 800731621878580985065417)
              ·
                refine ⟨600548716408935738799063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 800731621878580985065417 600548716408935738799063)
                ·
                  refine ⟨900823074613403608198595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 600548716408935738799063 900823074613403608198595)
                  ·
                    refine ⟨1351234611920105412297893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 900823074613403608198595 1351234611920105412297893)
                    ·
                      refine ⟨253356489735019764805855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1351234611920105412297893 253356489735019764805855)
                      ·
                        rfl

theorem cell23_493410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_493410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493410 prefixEnd_493410 := by exact prefixLift 493410
  have htrace : WordTrace (prefixWord ++ tailWord_493410) baseStart_493410 baseEnd_493410 := by
    simpa [prefixWord, tailWord_493410, baseEnd_493410] using wordTrace_append hprefix tailTrace_493410
  have hstable : (prefixWord ++ tailWord_493410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493410).length < 2 ^ (prefixWord ++ tailWord_493410).sum := by decide
  have hdescent : baseEnd_493410 < baseStart_493410 := by decide
  rcases family_descends (prefixWord ++ tailWord_493410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493426 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 3, 3, 3]
def baseStart_493426 : Nat := 118140960795 + 493426 * 2 ^ 59
def prefixEnd_493426 : Nat := 4983230072969 + 3 ^ 40 * 493426 * 2
def baseEnd_493426 : Nat := 253364705425491702205781

theorem tailTrace_493426 : CollatzResearch.WordTrace tailWord_493426 prefixEnd_493426 253364705425491702205781 := by
  unfold tailWord_493426
  simp only [CollatzResearch.WordTrace]
  refine ⟨4499181177602336824199033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11997816473606231531197421 4499181177602336824199033)
  ·
    refine ⟨3374385883201752618149275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4499181177602336824199033 3374385883201752618149275)
    ·
      refine ⟨5061578824802628927223913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3374385883201752618149275 5061578824802628927223913)
      ·
        refine ⟨3796184118601971695417935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5061578824802628927223913 3796184118601971695417935)
        ·
          refine ⟨5694276177902957543126903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3796184118601971695417935 5694276177902957543126903)
          ·
            refine ⟨8541414266854436314690355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5694276177902957543126903 8541414266854436314690355)
            ·
              refine ⟨12812121400281654472035533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8541414266854436314690355 12812121400281654472035533)
              ·
                refine ⟨4804545525105620427013325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12812121400281654472035533 4804545525105620427013325)
                ·
                  refine ⟨1801704571914607660129997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4804545525105620427013325 1801704571914607660129997)
                  ·
                    refine ⟨675639214467977872548749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1801704571914607660129997 675639214467977872548749)
                    ·
                      refine ⟨253364705425491702205781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 675639214467977872548749 253364705425491702205781)
                      ·
                        rfl

theorem cell23_493426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_493426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493426 prefixEnd_493426 := by exact prefixLift 493426
  have htrace : WordTrace (prefixWord ++ tailWord_493426) baseStart_493426 baseEnd_493426 := by
    simpa [prefixWord, tailWord_493426, baseEnd_493426] using wordTrace_append hprefix tailTrace_493426
  have hstable : (prefixWord ++ tailWord_493426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493426).length < 2 ^ (prefixWord ++ tailWord_493426).sum := by decide
  have hdescent : baseEnd_493426 < baseStart_493426 := by decide
  rcases family_descends (prefixWord ++ tailWord_493426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493430 : List Nat := [5, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5]
def baseStart_493430 : Nat := 118140960795 + 493430 * 2 ^ 59
def prefixEnd_493430 : Nat := 4983230072969 + 3 ^ 40 * 493430 * 2
def baseEnd_493430 : Nat := 253366759348109686555763

theorem tailTrace_493430 : CollatzResearch.WordTrace tailWord_493430 prefixEnd_493430 253366759348109686555763 := by
  unfold tailWord_493430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1124804412649678498746359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11997913734929903986627829 1124804412649678498746359)
  ·
    refine ⟨1687206618974517748119539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1124804412649678498746359 1687206618974517748119539)
    ·
      refine ⟨2530809928461776622179309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1687206618974517748119539 2530809928461776622179309)
      ·
        refine ⟨949053723173166233317241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2530809928461776622179309 949053723173166233317241)
        ·
          refine ⟨711790292379874674987931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 949053723173166233317241 711790292379874674987931)
          ·
            refine ⟨1067685438569812012481897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711790292379874674987931 1067685438569812012481897)
            ·
              refine ⟨800764078927359009361423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1067685438569812012481897 800764078927359009361423)
              ·
                refine ⟨1201146118391038514042135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 800764078927359009361423 1201146118391038514042135)
                ·
                  refine ⟨1801719177586557771063203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1201146118391038514042135 1801719177586557771063203)
                  ·
                    refine ⟨2702578766379836656594805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1801719177586557771063203 2702578766379836656594805)
                    ·
                      refine ⟨253366759348109686555763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2702578766379836656594805 253366759348109686555763)
                      ·
                        rfl

theorem cell23_493430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_493430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493430 prefixEnd_493430 := by exact prefixLift 493430
  have htrace : WordTrace (prefixWord ++ tailWord_493430) baseStart_493430 baseEnd_493430 := by
    simpa [prefixWord, tailWord_493430, baseEnd_493430] using wordTrace_append hprefix tailTrace_493430
  have hstable : (prefixWord ++ tailWord_493430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493430).length < 2 ^ (prefixWord ++ tailWord_493430).sum := by decide
  have hdescent : baseEnd_493430 < baseStart_493430 := by decide
  rcases family_descends (prefixWord ++ tailWord_493430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493439 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 5]
def baseStart_493439 : Nat := 118140960795 + 493439 * 2 ^ 59
def prefixEnd_493439 : Nat := 4983230072969 + 3 ^ 40 * 493439 * 2
def baseEnd_493439 : Nat := 253371380674000151343221

theorem tailTrace_493439 : CollatzResearch.WordTrace tailWord_493439 prefixEnd_493439 253371380674000151343221 := by
  unfold tailWord_493439
  simp only [CollatzResearch.WordTrace]
  refine ⟨17997198859362250517019371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11998132572908167011346247 17997198859362250517019371)
  ·
    refine ⟨26995798289043375775529057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17997198859362250517019371 26995798289043375775529057)
    ·
      refine ⟨20246848716782531831646793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26995798289043375775529057 20246848716782531831646793)
      ·
        refine ⟨15185136537586898873735095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20246848716782531831646793 15185136537586898873735095)
        ·
          refine ⟨22777704806380348310602643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15185136537586898873735095 22777704806380348310602643)
          ·
            refine ⟨34166557209570522465903965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22777704806380348310602643 34166557209570522465903965)
            ·
              refine ⟨12812458953588945924713987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34166557209570522465903965 12812458953588945924713987)
              ·
                refine ⟨19218688430383418887070981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12812458953588945924713987 19218688430383418887070981)
                ·
                  refine ⟨3603504080696891041325809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19218688430383418887070981 3603504080696891041325809)
                  ·
                    refine ⟨2702628060522668280994357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3603504080696891041325809 2702628060522668280994357)
                    ·
                      refine ⟨253371380674000151343221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2702628060522668280994357 253371380674000151343221)
                      ·
                        rfl

theorem cell23_493439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_493439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493439 prefixEnd_493439 := by exact prefixLift 493439
  have htrace : WordTrace (prefixWord ++ tailWord_493439) baseStart_493439 baseEnd_493439 := by
    simpa [prefixWord, tailWord_493439, baseEnd_493439] using wordTrace_append hprefix tailTrace_493439
  have hstable : (prefixWord ++ tailWord_493439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493439).length < 2 ^ (prefixWord ++ tailWord_493439).sum := by decide
  have hdescent : baseEnd_493439 < baseStart_493439 := by decide
  rcases family_descends (prefixWord ++ tailWord_493439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493443 : List Nat := [1, 1, 1, 3, 4, 2, 2, 1, 4, 1, 3]
def baseStart_493443 : Nat := 118140960795 + 493443 * 2 ^ 59
def prefixEnd_493443 : Nat := 4983230072969 + 3 ^ 40 * 493443 * 2
def baseEnd_493443 : Nat := 253373434596618135693203

theorem tailTrace_493443 : CollatzResearch.WordTrace tailWord_493443 prefixEnd_493443 253373434596618135693203 := by
  unfold tailWord_493443
  simp only [CollatzResearch.WordTrace]
  refine ⟨17997344751347759200164983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11998229834231839466776655 17997344751347759200164983)
  ·
    refine ⟨26996017127021638800247475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17997344751347759200164983 26996017127021638800247475)
    ·
      refine ⟨40494025690532458200371213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26996017127021638800247475 40494025690532458200371213)
      ·
        refine ⟨15185259633949671825139205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40494025690532458200371213 15185259633949671825139205)
        ·
          refine ⟨2847236181365563467213601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15185259633949671825139205 2847236181365563467213601)
          ·
            refine ⟨2135427136024172600410201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2847236181365563467213601 2135427136024172600410201)
            ·
              refine ⟨1601570352018129450307651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2135427136024172600410201 1601570352018129450307651)
              ·
                refine ⟨2402355528027194175461477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1601570352018129450307651 2402355528027194175461477)
                ·
                  refine ⟨450441661505098907899027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2402355528027194175461477 450441661505098907899027)
                  ·
                    refine ⟨675662492257648361848541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 450441661505098907899027 675662492257648361848541)
                    ·
                      refine ⟨253373434596618135693203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 675662492257648361848541 253373434596618135693203)
                      ·
                        rfl

theorem cell23_493443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 4, 1, 3].length) (baseStart_493443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493443 prefixEnd_493443 := by exact prefixLift 493443
  have htrace : WordTrace (prefixWord ++ tailWord_493443) baseStart_493443 baseEnd_493443 := by
    simpa [prefixWord, tailWord_493443, baseEnd_493443] using wordTrace_append hprefix tailTrace_493443
  have hstable : (prefixWord ++ tailWord_493443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493443).length < 2 ^ (prefixWord ++ tailWord_493443).sum := by decide
  have hdescent : baseEnd_493443 < baseStart_493443 := by decide
  rcases family_descends (prefixWord ++ tailWord_493443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493454 : List Nat := [4, 1, 1, 5, 1, 2, 2, 1, 2, 4]
def baseStart_493454 : Nat := 118140960795 + 493454 * 2 ^ 59
def prefixEnd_493454 : Nat := 4983230072969 + 3 ^ 40 * 493454 * 2
def baseEnd_493454 : Nat := 84459694294605864218551

theorem tailTrace_493454 : CollatzResearch.WordTrace tailWord_493454 prefixEnd_493454 84459694294605864218551 := by
  unfold tailWord_493454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2249718244288488509851927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11998497302871938719210277 2249718244288488509851927)
  ·
    refine ⟨3374577366432732764777891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2249718244288488509851927 3374577366432732764777891)
    ·
      refine ⟨5061866049649099147166837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3374577366432732764777891 5061866049649099147166837)
      ·
        refine ⟨474549942154603045046891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5061866049649099147166837 474549942154603045046891)
        ·
          refine ⟨711824913231904567570337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474549942154603045046891 711824913231904567570337)
          ·
            refine ⟨533868684923928425677753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 711824913231904567570337 533868684923928425677753)
            ·
              refine ⟨400401513692946319258315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533868684923928425677753 400401513692946319258315)
              ·
                refine ⟨600602270539419478887473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400401513692946319258315 600602270539419478887473)
                ·
                  refine ⟨450451702904564609165605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 600602270539419478887473 450451702904564609165605)
                  ·
                    refine ⟨84459694294605864218551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 450451702904564609165605 84459694294605864218551)
                    ·
                      rfl

theorem cell23_493454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_493454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493454 prefixEnd_493454 := by exact prefixLift 493454
  have htrace : WordTrace (prefixWord ++ tailWord_493454) baseStart_493454 baseEnd_493454 := by
    simpa [prefixWord, tailWord_493454, baseEnd_493454] using wordTrace_append hprefix tailTrace_493454
  have hstable : (prefixWord ++ tailWord_493454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493454).length < 2 ^ (prefixWord ++ tailWord_493454).sum := by decide
  have hdescent : baseEnd_493454 < baseStart_493454 := by decide
  rcases family_descends (prefixWord ++ tailWord_493454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493459 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 6, 6]
def baseStart_493459 : Nat := 118140960795 + 493459 * 2 ^ 59
def prefixEnd_493459 : Nat := 4983230072969 + 3 ^ 40 * 493459 * 2
def baseEnd_493459 : Nat := 84460550095696691031043

theorem tailTrace_493459 : CollatzResearch.WordTrace tailWord_493459 prefixEnd_493459 84460550095696691031043 := by
  unfold tailWord_493459
  simp only [CollatzResearch.WordTrace]
  refine ⟨17997928319289793932747431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11998618879526529288498287 17997928319289793932747431)
  ·
    refine ⟨26996892478934690899121147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17997928319289793932747431 26996892478934690899121147)
    ·
      refine ⟨40495338718402036348681721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26996892478934690899121147 40495338718402036348681721)
      ·
        refine ⟨30371504038801527261511291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40495338718402036348681721 30371504038801527261511291)
        ·
          refine ⟨45557256058202290892266937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30371504038801527261511291 45557256058202290892266937)
          ·
            refine ⟨34167942043651718169200203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45557256058202290892266937 34167942043651718169200203)
            ·
              refine ⟨51251913065477577253800305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34167942043651718169200203 51251913065477577253800305)
              ·
                refine ⟨38438934799108182940350229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51251913065477577253800305 38438934799108182940350229)
                ·
                  refine ⟨1801825068708196075328917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38438934799108182940350229 1801825068708196075328917)
                  ·
                    refine ⟨84460550095696691031043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1801825068708196075328917 84460550095696691031043)
                    ·
                      rfl

theorem cell23_493459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 6].length) (baseStart_493459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493459 prefixEnd_493459 := by exact prefixLift 493459
  have htrace : WordTrace (prefixWord ++ tailWord_493459) baseStart_493459 baseEnd_493459 := by
    simpa [prefixWord, tailWord_493459, baseEnd_493459] using wordTrace_append hprefix tailTrace_493459
  have hstable : (prefixWord ++ tailWord_493459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493459).length < 2 ^ (prefixWord ++ tailWord_493459).sum := by decide
  have hdescent : baseEnd_493459 < baseStart_493459 := by decide
  rcases family_descends (prefixWord ++ tailWord_493459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493464 : List Nat := [2, 1, 2, 6, 2, 1, 1, 2, 1, 2, 3]
def baseStart_493464 : Nat := 118140960795 + 493464 * 2 ^ 59
def prefixEnd_493464 : Nat := 4983230072969 + 3 ^ 40 * 493464 * 2
def baseEnd_493464 : Nat := 253384217690362553530607

theorem tailTrace_493464 : CollatzResearch.WordTrace tailWord_493464 prefixEnd_493464 253384217690362553530607 := by
  unfold tailWord_493464
  simp only [CollatzResearch.WordTrace]
  refine ⟨8999055342135839893339723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11998740456181119857786297 8999055342135839893339723)
  ·
    refine ⟨13498583013203759840009585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8999055342135839893339723 13498583013203759840009585)
    ·
      refine ⟨10123937259902819880007189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13498583013203759840009585 10123937259902819880007189)
      ·
        refine ⟨474559559057944681875337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10123937259902819880007189 474559559057944681875337)
        ·
          refine ⟨355919669293458511406503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 474559559057944681875337 355919669293458511406503)
          ·
            refine ⟨533879503940187767109755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355919669293458511406503 533879503940187767109755)
            ·
              refine ⟨800819255910281650664633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533879503940187767109755 800819255910281650664633)
              ·
                refine ⟨600614441932711237998475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 800819255910281650664633 600614441932711237998475)
                ·
                  refine ⟨900921662899066856997713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 600614441932711237998475 900921662899066856997713)
                  ·
                    refine ⟨675691247174300142748285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 900921662899066856997713 675691247174300142748285)
                    ·
                      refine ⟨253384217690362553530607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 675691247174300142748285 253384217690362553530607)
                      ·
                        rfl

theorem cell23_493464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_493464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493464 prefixEnd_493464 := by exact prefixLift 493464
  have htrace : WordTrace (prefixWord ++ tailWord_493464) baseStart_493464 baseEnd_493464 := by
    simpa [prefixWord, tailWord_493464, baseEnd_493464] using wordTrace_append hprefix tailTrace_493464
  have hstable : (prefixWord ++ tailWord_493464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493464).length < 2 ^ (prefixWord ++ tailWord_493464).sum := by decide
  have hdescent : baseEnd_493464 < baseStart_493464 := by decide
  rcases family_descends (prefixWord ++ tailWord_493464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493496 : List Nat := [2, 1, 2, 1, 2, 3, 2, 2, 2, 2, 4]
def baseStart_493496 : Nat := 118140960795 + 493496 * 2 ^ 59
def prefixEnd_493496 : Nat := 4983230072969 + 3 ^ 40 * 493496 * 2
def baseEnd_493496 : Nat := 253400649071306428330459

theorem tailTrace_493496 : CollatzResearch.WordTrace tailWord_493496 prefixEnd_493496 253400649071306428330459 := by
  unfold tailWord_493496
  simp only [CollatzResearch.WordTrace]
  refine ⟨8999638910077874625922171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11999518546770499501229561 8999638910077874625922171)
  ·
    refine ⟨13499458365116811938883257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8999638910077874625922171 13499458365116811938883257)
    ·
      refine ⟨10124593773837608954162443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13499458365116811938883257 10124593773837608954162443)
      ·
        refine ⟨15186890660756413431243665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10124593773837608954162443 15186890660756413431243665)
        ·
          refine ⟨11390167995567310073432749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15186890660756413431243665 11390167995567310073432749)
          ·
            refine ⟨4271312998337741277537281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11390167995567310073432749 4271312998337741277537281)
            ·
              refine ⟨3203484748753305958152961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4271312998337741277537281 3203484748753305958152961)
              ·
                refine ⟨2402613561564979468614721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3203484748753305958152961 2402613561564979468614721)
                ·
                  refine ⟨1801960171173734601461041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2402613561564979468614721 1801960171173734601461041)
                  ·
                    refine ⟨1351470128380300951095781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1801960171173734601461041 1351470128380300951095781)
                    ·
                      refine ⟨253400649071306428330459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1351470128380300951095781 253400649071306428330459)
                      ·
                        rfl

theorem cell23_493496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_493496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493496 prefixEnd_493496 := by exact prefixLift 493496
  have htrace : WordTrace (prefixWord ++ tailWord_493496) baseStart_493496 baseEnd_493496 := by
    simpa [prefixWord, tailWord_493496, baseEnd_493496] using wordTrace_append hprefix tailTrace_493496
  have hstable : (prefixWord ++ tailWord_493496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493496).length < 2 ^ (prefixWord ++ tailWord_493496).sum := by decide
  have hdescent : baseEnd_493496 < baseStart_493496 := by decide
  rcases family_descends (prefixWord ++ tailWord_493496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493499 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 9]
def baseStart_493499 : Nat := 118140960795 + 493499 * 2 ^ 59
def prefixEnd_493499 : Nat := 4983230072969 + 3 ^ 40 * 493499 * 2
def baseEnd_493499 : Nat := 253402189513269916592945

theorem tailTrace_493499 : CollatzResearch.WordTrace tailWord_493499 prefixEnd_493499 253402189513269916592945 := by
  unfold tailWord_493499
  simp only [CollatzResearch.WordTrace]
  refine ⟨17999387239144880764203551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11999591492763253842802367 17999387239144880764203551)
  ·
    refine ⟨26999080858717321146305327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17999387239144880764203551 26999080858717321146305327)
    ·
      refine ⟨40498621288075981719457991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26999080858717321146305327 40498621288075981719457991)
      ·
        refine ⟨60747931932113972579186987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40498621288075981719457991 60747931932113972579186987)
        ·
          refine ⟨91121897898170958868780481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60747931932113972579186987 91121897898170958868780481)
          ·
            refine ⟨68341423423628219151585361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91121897898170958868780481 68341423423628219151585361)
            ·
              refine ⟨51256067567721164363689021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68341423423628219151585361 51256067567721164363689021)
              ·
                refine ⟨19221025337895436636383383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51256067567721164363689021 19221025337895436636383383)
                ·
                  refine ⟨28831538006843154954575075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19221025337895436636383383 28831538006843154954575075)
                  ·
                    refine ⟨43247307010264732431862613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28831538006843154954575075 43247307010264732431862613)
                    ·
                      refine ⟨253402189513269916592945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 43247307010264732431862613 253402189513269916592945)
                      ·
                        rfl

theorem cell23_493499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 9].length) (baseStart_493499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493499 prefixEnd_493499 := by exact prefixLift 493499
  have htrace : WordTrace (prefixWord ++ tailWord_493499) baseStart_493499 baseEnd_493499 := by
    simpa [prefixWord, tailWord_493499, baseEnd_493499] using wordTrace_append hprefix tailTrace_493499
  have hstable : (prefixWord ++ tailWord_493499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493499).length < 2 ^ (prefixWord ++ tailWord_493499).sum := by decide
  have hdescent : baseEnd_493499 < baseStart_493499 := by decide
  rcases family_descends (prefixWord ++ tailWord_493499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493538 : List Nat := [3, 3, 3, 1, 3, 1, 2, 1, 1, 3, 2]
def baseStart_493538 : Nat := 118140960795 + 493538 * 2 ^ 59
def prefixEnd_493538 : Nat := 4983230072969 + 3 ^ 40 * 493538 * 2
def baseEnd_493538 : Nat := 253422215258795264005267

theorem tailTrace_493538 : CollatzResearch.WordTrace tailWord_493538 prefixEnd_493538 253422215258795264005267 := by
  unfold tailWord_493538
  simp only [CollatzResearch.WordTrace]
  refine ⟨4500202421500897606218317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12000539790669060283248845 4500202421500897606218317)
  ·
    refine ⟨1687575908062836602331869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4500202421500897606218317 1687575908062836602331869)
    ·
      refine ⟨632840965523563725874451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1687575908062836602331869 632840965523563725874451)
      ·
        refine ⟨949261448285345588811677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632840965523563725874451 949261448285345588811677)
        ·
          refine ⟨355973043107004595804379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 949261448285345588811677 355973043107004595804379)
          ·
            refine ⟨533959564660506893706569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355973043107004595804379 533959564660506893706569)
            ·
              refine ⟨400469673495380170279927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 533959564660506893706569 400469673495380170279927)
              ·
                refine ⟨600704510243070255419891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400469673495380170279927 600704510243070255419891)
                ·
                  refine ⟨901056765364605383129837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 600704510243070255419891 901056765364605383129837)
                  ·
                    refine ⟨337896287011727018673689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 901056765364605383129837 337896287011727018673689)
                    ·
                      refine ⟨253422215258795264005267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 337896287011727018673689 253422215258795264005267)
                      ·
                        rfl

theorem cell23_493538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_493538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493538 prefixEnd_493538 := by exact prefixLift 493538
  have htrace : WordTrace (prefixWord ++ tailWord_493538) baseStart_493538 baseEnd_493538 := by
    simpa [prefixWord, tailWord_493538, baseEnd_493538] using wordTrace_append hprefix tailTrace_493538
  have hstable : (prefixWord ++ tailWord_493538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493538).length < 2 ^ (prefixWord ++ tailWord_493538).sum := by decide
  have hdescent : baseEnd_493538 < baseStart_493538 := by decide
  rcases family_descends (prefixWord ++ tailWord_493538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493593 : List Nat := [1, 2, 1, 2, 1, 1, 3, 5, 2, 2, 3]
def baseStart_493593 : Nat := 118140960795 + 493593 * 2 ^ 59
def prefixEnd_493593 : Nat := 4983230072969 + 3 ^ 40 * 493593 * 2
def baseEnd_493593 : Nat := 253450456694792548817513

theorem tailTrace_493593 : CollatzResearch.WordTrace tailWord_493593 prefixEnd_493593 253450456694792548817513 := by
  unfold tailWord_493593
  simp only [CollatzResearch.WordTrace]
  refine ⟨18002815700804334818125433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12001877133869556545416955 18002815700804334818125433)
  ·
    refine ⟨13502111775603251113594075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18002815700804334818125433 13502111775603251113594075)
    ·
      refine ⟨20253167663404876670391113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13502111775603251113594075 20253167663404876670391113)
      ·
        refine ⟨15189875747553657502793335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20253167663404876670391113 15189875747553657502793335)
        ·
          refine ⟨22784813621330486254190003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15189875747553657502793335 22784813621330486254190003)
          ·
            refine ⟨34177220431995729381285005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22784813621330486254190003 34177220431995729381285005)
            ·
              refine ⟨12816457661998398517981877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34177220431995729381285005 12816457661998398517981877)
              ·
                refine ⟨1201542905812349861060801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12816457661998398517981877 1201542905812349861060801)
                ·
                  refine ⟨901157179359262395795601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1201542905812349861060801 901157179359262395795601)
                  ·
                    refine ⟨675867884519446796846701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 901157179359262395795601 675867884519446796846701)
                    ·
                      refine ⟨253450456694792548817513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 675867884519446796846701 253450456694792548817513)
                      ·
                        rfl

theorem cell23_493593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 2, 3].length) (baseStart_493593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493593 prefixEnd_493593 := by exact prefixLift 493593
  have htrace : WordTrace (prefixWord ++ tailWord_493593) baseStart_493593 baseEnd_493593 := by
    simpa [prefixWord, tailWord_493593, baseEnd_493593] using wordTrace_append hprefix tailTrace_493593
  have hstable : (prefixWord ++ tailWord_493593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493593).length < 2 ^ (prefixWord ++ tailWord_493593).sum := by decide
  have hdescent : baseEnd_493593 < baseStart_493593 := by decide
  rcases family_descends (prefixWord ++ tailWord_493593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493607 : List Nat := [1, 1, 7, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_493607 : Nat := 118140960795 + 493607 * 2 ^ 59
def prefixEnd_493607 : Nat := 4983230072969 + 3 ^ 40 * 493607 * 2
def baseEnd_493607 : Nat := 253457645423955494042449

theorem tailTrace_493607 : CollatzResearch.WordTrace tailWord_493607 prefixEnd_493607 253457645423955494042449 := by
  unfold tailWord_493607
  simp only [CollatzResearch.WordTrace]
  refine ⟨18003326322753615209135075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12002217548502410139423383 18003326322753615209135075)
  ·
    refine ⟨27004989484130422813702613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18003326322753615209135075 27004989484130422813702613)
    ·
      refine ⟨632929441034306784696155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 27004989484130422813702613 632929441034306784696155)
      ·
        refine ⟨949394161551460177044233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 632929441034306784696155 949394161551460177044233)
        ·
          refine ⟨712045621163595132783175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 949394161551460177044233 712045621163595132783175)
          ·
            refine ⟨1068068431745392699174763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712045621163595132783175 1068068431745392699174763)
            ·
              refine ⟨1602102647618089048762145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068068431745392699174763 1602102647618089048762145)
              ·
                refine ⟨1201576985713566786571609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1602102647618089048762145 1201576985713566786571609)
                ·
                  refine ⟨901182739285175089928707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1201576985713566786571609 901182739285175089928707)
                  ·
                    refine ⟨1351774108927762634893061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 901182739285175089928707 1351774108927762634893061)
                    ·
                      refine ⟨253457645423955494042449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1351774108927762634893061 253457645423955494042449)
                      ·
                        rfl

theorem cell23_493607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_493607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493607 prefixEnd_493607 := by exact prefixLift 493607
  have htrace : WordTrace (prefixWord ++ tailWord_493607) baseStart_493607 baseEnd_493607 := by
    simpa [prefixWord, tailWord_493607, baseEnd_493607] using wordTrace_append hprefix tailTrace_493607
  have hstable : (prefixWord ++ tailWord_493607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493607).length < 2 ^ (prefixWord ++ tailWord_493607).sum := by decide
  have hdescent : baseEnd_493607 < baseStart_493607 := by decide
  rcases family_descends (prefixWord ++ tailWord_493607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493610 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 4, 2, 3]
def baseStart_493610 : Nat := 118140960795 + 493610 * 2 ^ 59
def prefixEnd_493610 : Nat := 4983230072969 + 3 ^ 40 * 493610 * 2
def baseEnd_493610 : Nat := 253459185865918982304935

theorem tailTrace_493610 : CollatzResearch.WordTrace tailWord_493610 prefixEnd_493610 253459185865918982304935 := by
  unfold tailWord_493610
  simp only [CollatzResearch.WordTrace]
  refine ⟨4500858935435686680373571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12002290494495164480996189 4500858935435686680373571)
  ·
    refine ⟨6751288403153530020560357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4500858935435686680373571 6751288403153530020560357)
    ·
      refine ⟨1265866575591286878855067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6751288403153530020560357 1265866575591286878855067)
      ·
        refine ⟨1898799863386930318282601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1265866575591286878855067 1898799863386930318282601)
        ·
          refine ⟨1424099897540197738711951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1898799863386930318282601 1424099897540197738711951)
          ·
            refine ⟨2136149846310296608067927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424099897540197738711951 2136149846310296608067927)
            ·
              refine ⟨3204224769465444912101891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2136149846310296608067927 3204224769465444912101891)
              ·
                refine ⟨4806337154198167368152837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3204224769465444912101891 4806337154198167368152837)
                ·
                  refine ⟨901188216412156381528657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4806337154198167368152837 901188216412156381528657)
                  ·
                    refine ⟨675891162309117286146493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 901188216412156381528657 675891162309117286146493)
                    ·
                      refine ⟨253459185865918982304935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 675891162309117286146493 253459185865918982304935)
                      ·
                        rfl

theorem cell23_493610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_493610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493610 prefixEnd_493610 := by exact prefixLift 493610
  have htrace : WordTrace (prefixWord ++ tailWord_493610) baseStart_493610 baseEnd_493610 := by
    simpa [prefixWord, tailWord_493610, baseEnd_493610] using wordTrace_append hprefix tailTrace_493610
  have hstable : (prefixWord ++ tailWord_493610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493610).length < 2 ^ (prefixWord ++ tailWord_493610).sum := by decide
  have hdescent : baseEnd_493610 < baseStart_493610 := by decide
  rcases family_descends (prefixWord ++ tailWord_493610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493626 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 2, 9]
def baseStart_493626 : Nat := 118140960795 + 493626 * 2 ^ 59
def prefixEnd_493626 : Nat := 4983230072969 + 3 ^ 40 * 493626 * 2
def baseEnd_493626 : Nat := 84489133852130306568287

theorem tailTrace_493626 : CollatzResearch.WordTrace tailWord_493626 prefixEnd_493626 84489133852130306568287 := by
  unfold tailWord_493626
  simp only [CollatzResearch.WordTrace]
  refine ⟨4501004827421195363519183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12002679539789854302717821 4501004827421195363519183)
  ·
    refine ⟨6751507241131793045278775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4501004827421195363519183 6751507241131793045278775)
    ·
      refine ⟨10127260861697689567918163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6751507241131793045278775 10127260861697689567918163)
      ·
        refine ⟨15190891292546534351877245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10127260861697689567918163 15190891292546534351877245)
        ·
          refine ⟨5696584234704950381953967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15190891292546534351877245 5696584234704950381953967)
          ·
            refine ⟨8544876352057425572930951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5696584234704950381953967 8544876352057425572930951)
            ·
              refine ⟨12817314528086138359396427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8544876352057425572930951 12817314528086138359396427)
              ·
                refine ⟨19225971792129207539094641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12817314528086138359396427 19225971792129207539094641)
                ·
                  refine ⟨14419478844096905654320981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19225971792129207539094641 14419478844096905654320981)
                  ·
                    refine ⟨84489133852130306568287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 14419478844096905654320981 84489133852130306568287)
                    ·
                      rfl

theorem cell23_493626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2, 9].length) (baseStart_493626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493626 prefixEnd_493626 := by exact prefixLift 493626
  have htrace : WordTrace (prefixWord ++ tailWord_493626) baseStart_493626 baseEnd_493626 := by
    simpa [prefixWord, tailWord_493626, baseEnd_493626] using wordTrace_append hprefix tailTrace_493626
  have hstable : (prefixWord ++ tailWord_493626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493626).length < 2 ^ (prefixWord ++ tailWord_493626).sum := by decide
  have hdescent : baseEnd_493626 < baseStart_493626 := by decide
  rcases family_descends (prefixWord ++ tailWord_493626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493657 : List Nat := [1, 2, 1, 2, 2, 1, 4, 5, 1, 1, 3]
def baseStart_493657 : Nat := 118140960795 + 493657 * 2 ^ 59
def prefixEnd_493657 : Nat := 4983230072969 + 3 ^ 40 * 493657 * 2
def baseEnd_493657 : Nat := 253483319456680298417219

theorem tailTrace_493657 : CollatzResearch.WordTrace tailWord_493657 prefixEnd_493657 253483319456680298417219 := by
  unfold tailWord_493657
  simp only [CollatzResearch.WordTrace]
  refine ⟨18005149972572473748455225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12003433315048315832303483 18005149972572473748455225)
  ·
    refine ⟨13503862479429355311341419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18005149972572473748455225 13503862479429355311341419)
    ·
      refine ⟨20255793719144032967012129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13503862479429355311341419 20255793719144032967012129)
      ·
        refine ⟨15191845289358024725259097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20255793719144032967012129 15191845289358024725259097)
        ·
          refine ⟨11393883967018518543944323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15191845289358024725259097 11393883967018518543944323)
          ·
            refine ⟨17090825950527777815916485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11393883967018518543944323 17090825950527777815916485)
            ·
              refine ⟨3204529865723958340484341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17090825950527777815916485 3204529865723958340484341)
              ·
                refine ⟨300424674911621094420407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3204529865723958340484341 300424674911621094420407)
                ·
                  refine ⟨450637012367431641630611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 300424674911621094420407 450637012367431641630611)
                  ·
                    refine ⟨675955518551147462445917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 450637012367431641630611 675955518551147462445917)
                    ·
                      refine ⟨253483319456680298417219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 675955518551147462445917 253483319456680298417219)
                      ·
                        rfl

theorem cell23_493657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 5, 1, 1, 3].length) (baseStart_493657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493657 prefixEnd_493657 := by exact prefixLift 493657
  have htrace : WordTrace (prefixWord ++ tailWord_493657) baseStart_493657 baseEnd_493657 := by
    simpa [prefixWord, tailWord_493657, baseEnd_493657] using wordTrace_append hprefix tailTrace_493657
  have hstable : (prefixWord ++ tailWord_493657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493657).length < 2 ^ (prefixWord ++ tailWord_493657).sum := by decide
  have hdescent : baseEnd_493657 < baseStart_493657 := by decide
  rcases family_descends (prefixWord ++ tailWord_493657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493700 : List Nat := [2, 3, 2, 1, 2, 1, 1, 3, 3, 2, 3]
def baseStart_493700 : Nat := 118140960795 + 493700 * 2 ^ 59
def prefixEnd_493700 : Nat := 4983230072969 + 3 ^ 40 * 493700 * 2
def baseEnd_493700 : Nat := 253505399124823630179521

theorem tailTrace_493700 : CollatzResearch.WordTrace tailWord_493700 prefixEnd_493700 253505399124823630179521 := by
  unfold tailWord_493700
  simp only [CollatzResearch.WordTrace]
  refine ⟨9003359155708346046135277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12004478874277794728180369 9003359155708346046135277)
  ·
    refine ⟨3376259683390629767300729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9003359155708346046135277 3376259683390629767300729)
    ·
      refine ⟨2532194762542972325475547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3376259683390629767300729 2532194762542972325475547)
      ·
        refine ⟨3798292143814458488213321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2532194762542972325475547 3798292143814458488213321)
        ·
          refine ⟨2848719107860843866159991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3798292143814458488213321 2848719107860843866159991)
          ·
            refine ⟨4273078661791265799239987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2848719107860843866159991 4273078661791265799239987)
            ·
              refine ⟨6409617992686898698859981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4273078661791265799239987 6409617992686898698859981)
              ·
                refine ⟨2403606747257587012072493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6409617992686898698859981 2403606747257587012072493)
                ·
                  refine ⟨901352530221595129527185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2403606747257587012072493 901352530221595129527185)
                  ·
                    refine ⟨676014397666196347145389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 901352530221595129527185 676014397666196347145389)
                    ·
                      refine ⟨253505399124823630179521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 676014397666196347145389 253505399124823630179521)
                      ·
                        rfl

theorem cell23_493700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_493700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493700 prefixEnd_493700 := by exact prefixLift 493700
  have htrace : WordTrace (prefixWord ++ tailWord_493700) baseStart_493700 baseEnd_493700 := by
    simpa [prefixWord, tailWord_493700, baseEnd_493700] using wordTrace_append hprefix tailTrace_493700
  have hstable : (prefixWord ++ tailWord_493700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493700).length < 2 ^ (prefixWord ++ tailWord_493700).sum := by decide
  have hdescent : baseEnd_493700 < baseStart_493700 := by decide
  rcases family_descends (prefixWord ++ tailWord_493700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493748 : List Nat := [2, 5, 3, 1, 1, 1, 2, 2, 1, 1, 4]
def baseStart_493748 : Nat := 118140960795 + 493748 * 2 ^ 59
def prefixEnd_493748 : Nat := 4983230072969 + 3 ^ 40 * 493748 * 2
def baseEnd_493748 : Nat := 253530046196239442379301

theorem tailTrace_493748 : CollatzResearch.WordTrace tailWord_493748 prefixEnd_493748 253530046196239442379301 := by
  unfold tailWord_493748
  simp only [CollatzResearch.WordTrace]
  refine ⟨9004234507621398145008949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12005646010161864193345265 9004234507621398145008949)
  ·
    refine ⟨844146985089506076094589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9004234507621398145008949 844146985089506076094589)
    ·
      refine ⟨316555119408564778535471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 844146985089506076094589 316555119408564778535471)
      ·
        refine ⟨474832679112847167803207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316555119408564778535471 474832679112847167803207)
        ·
          refine ⟨712249018669270751704811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474832679112847167803207 712249018669270751704811)
          ·
            refine ⟨1068373528003906127557217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712249018669270751704811 1068373528003906127557217)
            ·
              refine ⟨801280146002929595667913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1068373528003906127557217 801280146002929595667913)
              ·
                refine ⟨600960109502197196750935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 801280146002929595667913 600960109502197196750935)
                ·
                  refine ⟨901440164253295795126403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 600960109502197196750935 901440164253295795126403)
                  ·
                    refine ⟨1352160246379943692689605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 901440164253295795126403 1352160246379943692689605)
                    ·
                      refine ⟨253530046196239442379301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1352160246379943692689605 253530046196239442379301)
                      ·
                        rfl

theorem cell23_493748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_493748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493748 prefixEnd_493748 := by exact prefixLift 493748
  have htrace : WordTrace (prefixWord ++ tailWord_493748) baseStart_493748 baseEnd_493748 := by
    simpa [prefixWord, tailWord_493748, baseEnd_493748] using wordTrace_append hprefix tailTrace_493748
  have hstable : (prefixWord ++ tailWord_493748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493748).length < 2 ^ (prefixWord ++ tailWord_493748).sum := by decide
  have hdescent : baseEnd_493748 < baseStart_493748 := by decide
  rcases family_descends (prefixWord ++ tailWord_493748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493774 : List Nat := [4, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2]
def baseStart_493774 : Nat := 118140960795 + 493774 * 2 ^ 59
def prefixEnd_493774 : Nat := 4983230072969 + 3 ^ 40 * 493774 * 2
def baseEnd_493774 : Nat := 253543396693256340654181

theorem tailTrace_493774 : CollatzResearch.WordTrace tailWord_493774 prefixEnd_493774 253543396693256340654181 := by
  unfold tailWord_493774
  simp only [CollatzResearch.WordTrace]
  refine ⟨2251177164143575341308047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12006278208765735153642917 2251177164143575341308047)
  ·
    refine ⟨3376765746215363011962071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2251177164143575341308047 3376765746215363011962071)
    ·
      refine ⟨5065148619323044517943107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3376765746215363011962071 5065148619323044517943107)
      ·
        refine ⟨7597722928984566776914661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5065148619323044517943107 7597722928984566776914661)
        ·
          refine ⟨1424573049184606270671499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7597722928984566776914661 1424573049184606270671499)
          ·
            refine ⟨2136859573776909406007249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424573049184606270671499 2136859573776909406007249)
            ·
              refine ⟨1602644680332682054505437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2136859573776909406007249 1602644680332682054505437)
              ·
                refine ⟨600991755124755770439539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1602644680332682054505437 600991755124755770439539)
                ·
                  refine ⟨901487632687133655659309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 600991755124755770439539 901487632687133655659309)
                  ·
                    refine ⟨338057862257675120872241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 901487632687133655659309 338057862257675120872241)
                    ·
                      refine ⟨253543396693256340654181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 338057862257675120872241 253543396693256340654181)
                      ·
                        rfl

theorem cell23_493774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2].length) (baseStart_493774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493774 prefixEnd_493774 := by exact prefixLift 493774
  have htrace : WordTrace (prefixWord ++ tailWord_493774) baseStart_493774 baseEnd_493774 := by
    simpa [prefixWord, tailWord_493774, baseEnd_493774] using wordTrace_append hprefix tailTrace_493774
  have hstable : (prefixWord ++ tailWord_493774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493774).length < 2 ^ (prefixWord ++ tailWord_493774).sum := by decide
  have hdescent : baseEnd_493774 < baseStart_493774 := by decide
  rcases family_descends (prefixWord ++ tailWord_493774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493804 : List Nat := [2, 2, 1, 1, 2, 3, 3, 3, 2, 2, 2]
def baseStart_493804 : Nat := 118140960795 + 493804 * 2 ^ 59
def prefixEnd_493804 : Nat := 4983230072969 + 3 ^ 40 * 493804 * 2
def baseEnd_493804 : Nat := 253558801112891223279043

theorem tailTrace_493804 : CollatzResearch.WordTrace tailWord_493804 prefixEnd_493804 253558801112891223279043 := by
  unfold tailWord_493804
  simp only [CollatzResearch.WordTrace]
  refine ⟨9005255751519958927028233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12007007668693278569370977 9005255751519958927028233)
  ·
    refine ⟨6753941813639969195271175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9005255751519958927028233 6753941813639969195271175)
    ·
      refine ⟨10130912720459953792906763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6753941813639969195271175 10130912720459953792906763)
      ·
        refine ⟨15196369080689930689360145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10130912720459953792906763 15196369080689930689360145)
        ·
          refine ⟨11397276810517448017020109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15196369080689930689360145 11397276810517448017020109)
          ·
            refine ⟨4273978803944043006382541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11397276810517448017020109 4273978803944043006382541)
            ·
              refine ⟨1602742051479016127393453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4273978803944043006382541 1602742051479016127393453)
              ·
                refine ⟨601028269304631047772545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1602742051479016127393453 601028269304631047772545)
                ·
                  refine ⟨450771201978473285829409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 601028269304631047772545 450771201978473285829409)
                  ·
                    refine ⟨338078401483854964372057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 450771201978473285829409 338078401483854964372057)
                    ·
                      refine ⟨253558801112891223279043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 338078401483854964372057 253558801112891223279043)
                      ·
                        rfl

theorem cell23_493804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 2, 2].length) (baseStart_493804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493804 prefixEnd_493804 := by exact prefixLift 493804
  have htrace : WordTrace (prefixWord ++ tailWord_493804) baseStart_493804 baseEnd_493804 := by
    simpa [prefixWord, tailWord_493804, baseEnd_493804] using wordTrace_append hprefix tailTrace_493804
  have hstable : (prefixWord ++ tailWord_493804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493804).length < 2 ^ (prefixWord ++ tailWord_493804).sum := by decide
  have hdescent : baseEnd_493804 < baseStart_493804 := by decide
  rcases family_descends (prefixWord ++ tailWord_493804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493847 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 2, 5, 2]
def baseStart_493847 : Nat := 118140960795 + 493847 * 2 ^ 59
def prefixEnd_493847 : Nat := 4983230072969 + 3 ^ 40 * 493847 * 2
def baseEnd_493847 : Nat := 253580880781034555041345

theorem tailTrace_493847 : CollatzResearch.WordTrace tailWord_493847 prefixEnd_493847 253580880781034555041345 := by
  unfold tailWord_493847
  simp only [CollatzResearch.WordTrace]
  refine ⟨18012079841884136197871795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12008053227922757465247863 18012079841884136197871795)
  ·
    refine ⟨27018119762826204296807693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18012079841884136197871795 27018119762826204296807693)
    ·
      refine ⟨10131794911059826611302885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27018119762826204296807693 10131794911059826611302885)
      ·
        refine ⟨1899711545823717489619291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10131794911059826611302885 1899711545823717489619291)
        ·
          refine ⟨2849567318735576234428937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1899711545823717489619291 2849567318735576234428937)
          ·
            refine ⟨2137175489051682175821703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2849567318735576234428937 2137175489051682175821703)
            ·
              refine ⟨3205763233577523263732555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2137175489051682175821703 3205763233577523263732555)
              ·
                refine ⟨4808644850366284895598833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3205763233577523263732555 4808644850366284895598833)
                ·
                  refine ⟨3606483637774713671699125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4808644850366284895598833 3606483637774713671699125)
                  ·
                    refine ⟨338107841041379406721793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3606483637774713671699125 338107841041379406721793)
                    ·
                      refine ⟨253580880781034555041345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 338107841041379406721793 253580880781034555041345)
                      ·
                        rfl

theorem cell23_493847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_493847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493847 prefixEnd_493847 := by exact prefixLift 493847
  have htrace : WordTrace (prefixWord ++ tailWord_493847) baseStart_493847 baseEnd_493847 := by
    simpa [prefixWord, tailWord_493847, baseEnd_493847] using wordTrace_append hprefix tailTrace_493847
  have hstable : (prefixWord ++ tailWord_493847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493847).length < 2 ^ (prefixWord ++ tailWord_493847).sum := by decide
  have hdescent : baseEnd_493847 < baseStart_493847 := by decide
  rcases family_descends (prefixWord ++ tailWord_493847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493854 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_493854 : Nat := 118140960795 + 493854 * 2 ^ 59
def prefixEnd_493854 : Nat := 4983230072969 + 3 ^ 40 * 493854 * 2
def baseEnd_493854 : Nat := 253584475145616027653813

theorem tailTrace_493854 : CollatzResearch.WordTrace tailWord_493854 prefixEnd_493854 253584475145616027653813 := by
  unfold tailWord_493854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2251541894107347049172077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12008223435239184262251077 2251541894107347049172077)
  ·
    refine ⟨844328210290255143439529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2251541894107347049172077 844328210290255143439529)
    ·
      refine ⟨633246157717691357579647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 844328210290255143439529 633246157717691357579647)
      ·
        refine ⟨949869236576537036369471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 633246157717691357579647 949869236576537036369471)
        ·
          refine ⟨1424803854864805554554207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 949869236576537036369471 1424803854864805554554207)
          ·
            refine ⟨2137205782297208331831311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424803854864805554554207 2137205782297208331831311)
            ·
              refine ⟨3205808673445812497746967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2137205782297208331831311 3205808673445812497746967)
              ·
                refine ⟨4808713010168718746620451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3205808673445812497746967 4808713010168718746620451)
                ·
                  refine ⟨7213069515253078119930677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4808713010168718746620451 7213069515253078119930677)
                  ·
                    refine ⟨676225267054976073743501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7213069515253078119930677 676225267054976073743501)
                    ·
                      refine ⟨253584475145616027653813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 676225267054976073743501 253584475145616027653813)
                      ·
                        rfl

theorem cell23_493854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_493854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493854 prefixEnd_493854 := by exact prefixLift 493854
  have htrace : WordTrace (prefixWord ++ tailWord_493854) baseStart_493854 baseEnd_493854 := by
    simpa [prefixWord, tailWord_493854, baseEnd_493854] using wordTrace_append hprefix tailTrace_493854
  have hstable : (prefixWord ++ tailWord_493854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493854).length < 2 ^ (prefixWord ++ tailWord_493854).sum := by decide
  have hdescent : baseEnd_493854 < baseStart_493854 := by decide
  rcases family_descends (prefixWord ++ tailWord_493854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493874 : List Nat := [3, 2, 1, 1, 5, 2, 1, 1, 2, 5]
def baseStart_493874 : Nat := 118140960795 + 493874 * 2 ^ 59
def prefixEnd_493874 : Nat := 4983230072969 + 3 ^ 40 * 493874 * 2
def baseEnd_493874 : Nat := 84531581586235316467907

theorem tailTrace_493874 : CollatzResearch.WordTrace tailWord_493874 prefixEnd_493874 84531581586235316467907 := by
  unfold tailWord_493874
  simp only [CollatzResearch.WordTrace]
  refine ⟨4503266153196579952276169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12008709741857546539403117 4503266153196579952276169)
  ·
    refine ⟨3377449614897434964207127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4503266153196579952276169 3377449614897434964207127)
    ·
      refine ⟨5066174422346152446310691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3377449614897434964207127 5066174422346152446310691)
      ·
        refine ⟨7599261633519228669466037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5066174422346152446310691 7599261633519228669466037)
        ·
          refine ⟨712430778142427687762441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7599261633519228669466037 712430778142427687762441)
          ·
            refine ⟨534323083606820765821831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 712430778142427687762441 534323083606820765821831)
            ·
              refine ⟨801484625410231148732747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534323083606820765821831 801484625410231148732747)
              ·
                refine ⟨1202226938115346723099121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 801484625410231148732747 1202226938115346723099121)
                ·
                  refine ⟨901670203586510042324341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1202226938115346723099121 901670203586510042324341)
                  ·
                    refine ⟨84531581586235316467907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 901670203586510042324341 84531581586235316467907)
                    ·
                      rfl

theorem cell23_493874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_493874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493874 prefixEnd_493874 := by exact prefixLift 493874
  have htrace : WordTrace (prefixWord ++ tailWord_493874) baseStart_493874 baseEnd_493874 := by
    simpa [prefixWord, tailWord_493874, baseEnd_493874] using wordTrace_append hprefix tailTrace_493874
  have hstable : (prefixWord ++ tailWord_493874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493874).length < 2 ^ (prefixWord ++ tailWord_493874).sum := by decide
  have hdescent : baseEnd_493874 < baseStart_493874 := by decide
  rcases family_descends (prefixWord ++ tailWord_493874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493877 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 1, 6, 2]
def baseStart_493877 : Nat := 118140960795 + 493877 * 2 ^ 59
def prefixEnd_493877 : Nat := 4983230072969 + 3 ^ 40 * 493877 * 2
def baseEnd_493877 : Nat := 253596285200669437666207

theorem tailTrace_493877 : CollatzResearch.WordTrace tailWord_493877 prefixEnd_493877 253596285200669437666207 := by
  unfold tailWord_493877
  simp only [CollatzResearch.WordTrace]
  refine ⟨18013174031775451321463885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12008782687850300880975923 18013174031775451321463885)
  ·
    refine ⟨6754940261915794245548957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18013174031775451321463885 6754940261915794245548957)
    ·
      refine ⟨2533102598218422842080859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6754940261915794245548957 2533102598218422842080859)
      ·
        refine ⟨3799653897327634263121289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2533102598218422842080859 3799653897327634263121289)
        ·
          refine ⟨2849740422995725697340967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3799653897327634263121289 2849740422995725697340967)
          ·
            refine ⟨4274610634493588546011451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2849740422995725697340967 4274610634493588546011451)
            ·
              refine ⟨6411915951740382819017177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4274610634493588546011451 6411915951740382819017177)
              ·
                refine ⟨4808936963805287114262883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6411915951740382819017177 4808936963805287114262883)
                ·
                  refine ⟨7213405445707930671394325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4808936963805287114262883 7213405445707930671394325)
                  ·
                    refine ⟨338128380267559250221609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7213405445707930671394325 338128380267559250221609)
                    ·
                      refine ⟨253596285200669437666207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 338128380267559250221609 253596285200669437666207)
                      ·
                        rfl

theorem cell23_493877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_493877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493877 prefixEnd_493877 := by exact prefixLift 493877
  have htrace : WordTrace (prefixWord ++ tailWord_493877) baseStart_493877 baseEnd_493877 := by
    simpa [prefixWord, tailWord_493877, baseEnd_493877] using wordTrace_append hprefix tailTrace_493877
  have hstable : (prefixWord ++ tailWord_493877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493877).length < 2 ^ (prefixWord ++ tailWord_493877).sum := by decide
  have hdescent : baseEnd_493877 < baseStart_493877 := by decide
  rcases family_descends (prefixWord ++ tailWord_493877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493900 : List Nat := [2, 2, 1, 3, 2, 1, 3, 1, 8]
def baseStart_493900 : Nat := 118140960795 + 493900 * 2 ^ 59
def prefixEnd_493900 : Nat := 4983230072969 + 3 ^ 40 * 493900 * 2
def baseEnd_493900 : Nat := 28178677250635871964289

theorem tailTrace_493900 : CollatzResearch.WordTrace tailWord_493900 prefixEnd_493900 28178677250635871964289 := by
  unfold tailWord_493900
  simp only [CollatzResearch.WordTrace]
  refine ⟨9007006455346063124775577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12009341940461417499700769 9007006455346063124775577)
  ·
    refine ⟨6755254841509547343581683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9007006455346063124775577 6755254841509547343581683)
    ·
      refine ⟨10132882262264321015372525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6755254841509547343581683 10132882262264321015372525)
      ·
        refine ⟨3799830848349120380764697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10132882262264321015372525 3799830848349120380764697)
        ·
          refine ⟨2849873136261840285573523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3799830848349120380764697 2849873136261840285573523)
          ·
            refine ⟨4274809704392760428360285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2849873136261840285573523 4274809704392760428360285)
            ·
              refine ⟨1603053639147285160635107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4274809704392760428360285 1603053639147285160635107)
              ·
                refine ⟨2404580458720927740952661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1603053639147285160635107 2404580458720927740952661)
                ·
                  refine ⟨28178677250635871964289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2404580458720927740952661 28178677250635871964289)
                  ·
                    rfl

theorem cell23_493900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 8].length) (baseStart_493900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493900 prefixEnd_493900 := by exact prefixLift 493900
  have htrace : WordTrace (prefixWord ++ tailWord_493900) baseStart_493900 baseEnd_493900 := by
    simpa [prefixWord, tailWord_493900, baseEnd_493900] using wordTrace_append hprefix tailTrace_493900
  have hstable : (prefixWord ++ tailWord_493900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493900).length < 2 ^ (prefixWord ++ tailWord_493900).sum := by decide
  have hdescent : baseEnd_493900 < baseStart_493900 := by decide
  rcases family_descends (prefixWord ++ tailWord_493900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493904 : List Nat := [2, 1, 1, 1, 1, 6, 2, 4, 1, 4]
def baseStart_493904 : Nat := 118140960795 + 493904 * 2 ^ 59
def prefixEnd_493904 : Nat := 4983230072969 + 3 ^ 40 * 493904 * 2
def baseEnd_493904 : Nat := 84536716392780277342861

theorem tailTrace_493904 : CollatzResearch.WordTrace tailWord_493904 prefixEnd_493904 84536716392780277342861 := by
  unfold tailWord_493904
  simp only [CollatzResearch.WordTrace]
  refine ⟨9007079401338817466348383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12009439201785089955131177 9007079401338817466348383)
  ·
    refine ⟨13510619102008226199522575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9007079401338817466348383 13510619102008226199522575)
    ·
      refine ⟨20265928653012339299283863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13510619102008226199522575 20265928653012339299283863)
      ·
        refine ⟨30398892979518508948925795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20265928653012339299283863 30398892979518508948925795)
        ·
          refine ⟨45598339469277763423388693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30398892979518508948925795 45598339469277763423388693)
          ·
            refine ⟨2137422162622395160471345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45598339469277763423388693 2137422162622395160471345)
            ·
              refine ⟨1603066621966796370353509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2137422162622395160471345 1603066621966796370353509)
              ·
                refine ⟨300574991618774319441283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1603066621966796370353509 300574991618774319441283)
                ·
                  refine ⟨450862487428161479161925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 300574991618774319441283 450862487428161479161925)
                  ·
                    refine ⟨84536716392780277342861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 450862487428161479161925 84536716392780277342861)
                    ·
                      rfl

theorem cell23_493904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 4, 1, 4].length) (baseStart_493904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493904 prefixEnd_493904 := by exact prefixLift 493904
  have htrace : WordTrace (prefixWord ++ tailWord_493904) baseStart_493904 baseEnd_493904 := by
    simpa [prefixWord, tailWord_493904, baseEnd_493904] using wordTrace_append hprefix tailTrace_493904
  have hstable : (prefixWord ++ tailWord_493904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493904).length < 2 ^ (prefixWord ++ tailWord_493904).sum := by decide
  have hdescent : baseEnd_493904 < baseStart_493904 := by decide
  rcases family_descends (prefixWord ++ tailWord_493904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493947 : List Nat := [1, 1, 1, 1, 1, 7, 2, 3, 1, 5]
def baseStart_493947 : Nat := 118140960795 + 493947 * 2 ^ 59
def prefixEnd_493947 : Nat := 4983230072969 + 3 ^ 40 * 493947 * 2
def baseEnd_493947 : Nat := 84544076282161387930295

theorem tailTrace_493947 : CollatzResearch.WordTrace tailWord_493947 prefixEnd_493947 84544076282161387930295 := by
  unfold tailWord_493947
  simp only [CollatzResearch.WordTrace]
  refine ⟨18015727141521853276512095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12010484761014568851008063 18015727141521853276512095)
  ·
    refine ⟨27023590712282779914768143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18015727141521853276512095 27023590712282779914768143)
    ·
      refine ⟨40535386068424169872152215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27023590712282779914768143 40535386068424169872152215)
      ·
        refine ⟨60803079102636254808228323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40535386068424169872152215 60803079102636254808228323)
        ·
          refine ⟨91204618653954382212342485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60803079102636254808228323 91204618653954382212342485)
          ·
            refine ⟨2137608249702055833101777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 91204618653954382212342485 2137608249702055833101777)
            ·
              refine ⟨1603206187276541874826333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2137608249702055833101777 1603206187276541874826333)
              ·
                refine ⟨601202320228703203059875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1603206187276541874826333 601202320228703203059875)
                ·
                  refine ⟨901803480343054804589813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 601202320228703203059875 901803480343054804589813)
                  ·
                    refine ⟨84544076282161387930295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 901803480343054804589813 84544076282161387930295)
                    ·
                      rfl

theorem cell23_493947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 5].length) (baseStart_493947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493947 prefixEnd_493947 := by exact prefixLift 493947
  have htrace : WordTrace (prefixWord ++ tailWord_493947) baseStart_493947 baseEnd_493947 := by
    simpa [prefixWord, tailWord_493947, baseEnd_493947] using wordTrace_append hprefix tailTrace_493947
  have hstable : (prefixWord ++ tailWord_493947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493947).length < 2 ^ (prefixWord ++ tailWord_493947).sum := by decide
  have hdescent : baseEnd_493947 < baseStart_493947 := by decide
  rcases family_descends (prefixWord ++ tailWord_493947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493961 : List Nat := [1, 2, 1, 1, 6, 3, 1, 1, 3, 1, 3]
def baseStart_493961 : Nat := 118140960795 + 493961 * 2 ^ 59
def prefixEnd_493961 : Nat := 4983230072969 + 3 ^ 40 * 493961 * 2
def baseEnd_493961 : Nat := 253639417575647109015821

theorem tailTrace_493961 : CollatzResearch.WordTrace tailWord_493961 prefixEnd_493961 253639417575647109015821 := by
  unfold tailWord_493961
  simp only [CollatzResearch.WordTrace]
  refine ⟨18016237763471133667521737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12010825175647422445014491 18016237763471133667521737)
  ·
    refine ⟨13512178322603350250641303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18016237763471133667521737 13512178322603350250641303)
    ·
      refine ⟨20268267483905025375961955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13512178322603350250641303 20268267483905025375961955)
      ·
        refine ⟨30402401225857538063942933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20268267483905025375961955 30402401225857538063942933)
        ·
          refine ⟨1425112557462072096747325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30402401225857538063942933 1425112557462072096747325)
          ·
            refine ⟨534417209048277036280247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1425112557462072096747325 534417209048277036280247)
            ·
              refine ⟨801625813572415554420371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534417209048277036280247 801625813572415554420371)
              ·
                refine ⟨1202438720358623331630557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 801625813572415554420371 1202438720358623331630557)
                ·
                  refine ⟨450914520134483749361459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1202438720358623331630557 450914520134483749361459)
                  ·
                    refine ⟨676371780201725624042189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 450914520134483749361459 676371780201725624042189)
                    ·
                      refine ⟨253639417575647109015821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 676371780201725624042189 253639417575647109015821)
                      ·
                        rfl

theorem cell23_493961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 3, 1, 3].length) (baseStart_493961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493961 prefixEnd_493961 := by exact prefixLift 493961
  have htrace : WordTrace (prefixWord ++ tailWord_493961) baseStart_493961 baseEnd_493961 := by
    simpa [prefixWord, tailWord_493961, baseEnd_493961] using wordTrace_append hprefix tailTrace_493961
  have hstable : (prefixWord ++ tailWord_493961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493961).length < 2 ^ (prefixWord ++ tailWord_493961).sum := by decide
  have hdescent : baseEnd_493961 < baseStart_493961 := by decide
  rcases family_descends (prefixWord ++ tailWord_493961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493981 : List Nat := [1, 4, 2, 1, 4, 2, 1, 2, 1, 5]
def baseStart_493981 : Nat := 118140960795 + 493981 * 2 ^ 59
def prefixEnd_493981 : Nat := 4983230072969 + 3 ^ 40 * 493981 * 2
def baseEnd_493981 : Nat := 84549895729579010255243

theorem tailTrace_493981 : CollatzResearch.WordTrace tailWord_493981 prefixEnd_493981 84549895729579010255243 := by
  unfold tailWord_493981
  simp only [CollatzResearch.WordTrace]
  refine ⟨18016967223398677083249797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12011311482265784722166531 18016967223398677083249797)
  ·
    refine ⟨3378181354387251953109337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18016967223398677083249797 3378181354387251953109337)
    ·
      refine ⟨2533636015790438964832003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3378181354387251953109337 2533636015790438964832003)
      ·
        refine ⟨3800454023685658447248005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2533636015790438964832003 3800454023685658447248005)
        ·
          refine ⟨712585129441060958859001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3800454023685658447248005 712585129441060958859001)
          ·
            refine ⟨534438847080795719144251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 712585129441060958859001 534438847080795719144251)
            ·
              refine ⟨801658270621193578716377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534438847080795719144251 801658270621193578716377)
              ·
                refine ⟨601243702965895184037283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 801658270621193578716377 601243702965895184037283)
                ·
                  refine ⟨901865554448842776055925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 601243702965895184037283 901865554448842776055925)
                  ·
                    refine ⟨84549895729579010255243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 901865554448842776055925 84549895729579010255243)
                    ·
                      rfl

theorem cell23_493981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_493981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493981 prefixEnd_493981 := by exact prefixLift 493981
  have htrace : WordTrace (prefixWord ++ tailWord_493981) baseStart_493981 baseEnd_493981 := by
    simpa [prefixWord, tailWord_493981, baseEnd_493981] using wordTrace_append hprefix tailTrace_493981
  have hstable : (prefixWord ++ tailWord_493981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493981).length < 2 ^ (prefixWord ++ tailWord_493981).sum := by decide
  have hdescent : baseEnd_493981 < baseStart_493981 := by decide
  rcases family_descends (prefixWord ++ tailWord_493981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493984 : List Nat := [2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 4]
def baseStart_493984 : Nat := 118140960795 + 493984 * 2 ^ 59
def prefixEnd_493984 : Nat := 4983230072969 + 3 ^ 40 * 493984 * 2
def baseEnd_493984 : Nat := 253651227630700519028215

theorem tailTrace_493984 : CollatzResearch.WordTrace tailWord_493984 prefixEnd_493984 253651227630700519028215 := by
  unfold tailWord_493984
  simp only [CollatzResearch.WordTrace]
  refine ⟨9008538321193904297804503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12011384428258539063739337 9008538321193904297804503)
  ·
    refine ⟨13512807481790856446706755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9008538321193904297804503 13512807481790856446706755)
    ·
      refine ⟨20269211222686284670060133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13512807481790856446706755 20269211222686284670060133)
      ·
        refine ⟨3800477104253678375636275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20269211222686284670060133 3800477104253678375636275)
        ·
          refine ⟨5700715656380517563454413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3800477104253678375636275 5700715656380517563454413)
          ·
            refine ⟨2137768371142694086295405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5700715656380517563454413 2137768371142694086295405)
            ·
              refine ⟨801663139178510282360777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2137768371142694086295405 801663139178510282360777)
              ·
                refine ⟨601247354383882711770583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 801663139178510282360777 601247354383882711770583)
                ·
                  refine ⟨901871031575824067655875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 601247354383882711770583 901871031575824067655875)
                  ·
                    refine ⟨1352806547363736101483813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 901871031575824067655875 1352806547363736101483813)
                    ·
                      refine ⟨253651227630700519028215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1352806547363736101483813 253651227630700519028215)
                      ·
                        rfl

theorem cell23_493984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_493984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_493984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_493984 prefixEnd_493984 := by exact prefixLift 493984
  have htrace : WordTrace (prefixWord ++ tailWord_493984) baseStart_493984 baseEnd_493984 := by
    simpa [prefixWord, tailWord_493984, baseEnd_493984] using wordTrace_append hprefix tailTrace_493984
  have hstable : (prefixWord ++ tailWord_493984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493984).length < 2 ^ (prefixWord ++ tailWord_493984).sum := by decide
  have hdescent : baseEnd_493984 < baseStart_493984 := by decide
  rcases family_descends (prefixWord ++ tailWord_493984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494001 : List Nat := [1, 2, 2, 4, 1, 3, 3, 1, 1, 1, 4]
def baseStart_494001 : Nat := 118140960795 + 494001 * 2 ^ 59
def prefixEnd_494001 : Nat := 4983230072969 + 3 ^ 40 * 494001 * 2
def baseEnd_494001 : Nat := 253659956801826952515637

theorem tailTrace_494001 : CollatzResearch.WordTrace tailWord_494001 prefixEnd_494001 253659956801826952515637 := by
  unfold tailWord_494001
  simp only [CollatzResearch.WordTrace]
  refine ⟨18017696683326220498977857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12011797788884146999318571 18017696683326220498977857)
  ·
    refine ⟨13513272512494665374233393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18017696683326220498977857 13513272512494665374233393)
    ·
      refine ⟨10134954384370999030675045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13513272512494665374233393 10134954384370999030675045)
      ·
        refine ⟨1900303947069562318251571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10134954384370999030675045 1900303947069562318251571)
        ·
          refine ⟨2850455920604343477377357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1900303947069562318251571 2850455920604343477377357)
          ·
            refine ⟨1068920970226628804016509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2850455920604343477377357 1068920970226628804016509)
            ·
              refine ⟨400845363834985801506191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1068920970226628804016509 400845363834985801506191)
              ·
                refine ⟨601268045752478702259287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400845363834985801506191 601268045752478702259287)
                ·
                  refine ⟨901902068628718053388931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 601268045752478702259287 901902068628718053388931)
                  ·
                    refine ⟨1352853102943077080083397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 901902068628718053388931 1352853102943077080083397)
                    ·
                      refine ⟨253659956801826952515637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1352853102943077080083397 253659956801826952515637)
                      ·
                        rfl

theorem cell23_494001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_494001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494001 prefixEnd_494001 := by exact prefixLift 494001
  have htrace : WordTrace (prefixWord ++ tailWord_494001) baseStart_494001 baseEnd_494001 := by
    simpa [prefixWord, tailWord_494001, baseEnd_494001] using wordTrace_append hprefix tailTrace_494001
  have hstable : (prefixWord ++ tailWord_494001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494001).length < 2 ^ (prefixWord ++ tailWord_494001).sum := by decide
  have hdescent : baseEnd_494001 < baseStart_494001 := by decide
  rcases family_descends (prefixWord ++ tailWord_494001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494084 : List Nat := [2, 3, 2, 3, 1, 1, 2, 1, 2, 6]
def baseStart_494084 : Nat := 118140960795 + 494084 * 2 ^ 59
def prefixEnd_494084 : Nat := 4983230072969 + 3 ^ 40 * 494084 * 2
def baseEnd_494084 : Nat := 84567525232050042592585

theorem tailTrace_494084 : CollatzResearch.WordTrace tailWord_494084 prefixEnd_494084 84567525232050042592585 := by
  unfold tailWord_494084
  simp only [CollatzResearch.WordTrace]
  refine ⟨9010361971012762837124653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12013815961350350449499537 9010361971012762837124653)
  ·
    refine ⟨3378885739129786063921745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9010361971012762837124653 3378885739129786063921745)
    ·
      refine ⟨2534164304347339547941309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3378885739129786063921745 2534164304347339547941309)
      ·
        refine ⟨950311614130252330477991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2534164304347339547941309 950311614130252330477991)
        ·
          refine ⟨1425467421195378495716987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 950311614130252330477991 1425467421195378495716987)
          ·
            refine ⟨2138201131793067743575481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1425467421195378495716987 2138201131793067743575481)
            ·
              refine ⟨1603650848844800807681611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2138201131793067743575481 1603650848844800807681611)
              ·
                refine ⟨2405476273267201211522417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1603650848844800807681611 2405476273267201211522417)
                ·
                  refine ⟨1804107204950400908641813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2405476273267201211522417 1804107204950400908641813)
                  ·
                    refine ⟨84567525232050042592585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1804107204950400908641813 84567525232050042592585)
                    ·
                      rfl

theorem cell23_494084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_494084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494084 prefixEnd_494084 := by exact prefixLift 494084
  have htrace : WordTrace (prefixWord ++ tailWord_494084) baseStart_494084 baseEnd_494084 := by
    simpa [prefixWord, tailWord_494084, baseEnd_494084] using wordTrace_append hprefix tailTrace_494084
  have hstable : (prefixWord ++ tailWord_494084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494084).length < 2 ^ (prefixWord ++ tailWord_494084).sum := by decide
  have hdescent : baseEnd_494084 < baseStart_494084 := by decide
  rcases family_descends (prefixWord ++ tailWord_494084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494091 : List Nat := [1, 1, 1, 1, 7, 1, 3, 1, 1, 4, 2]
def baseStart_494091 : Nat := 118140960795 + 494091 * 2 ^ 59
def prefixEnd_494091 : Nat := 4983230072969 + 3 ^ 40 * 494091 * 2
def baseEnd_494091 : Nat := 253706170060731600390223

theorem tailTrace_494091 : CollatzResearch.WordTrace tailWord_494091 prefixEnd_494091 253706170060731600390223 := by
  unfold tailWord_494091
  simp only [CollatzResearch.WordTrace]
  refine ⟨18020979253000165869754127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12013986168666777246502751 18020979253000165869754127)
  ·
    refine ⟨27031468879500248804631191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18020979253000165869754127 27031468879500248804631191)
    ·
      refine ⟨40547203319250373206946787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27031468879500248804631191 40547203319250373206946787)
      ·
        refine ⟨60820804978875559810420181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40547203319250373206946787 60820804978875559810420181)
        ·
          refine ⟨1425487616692395933056723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 60820804978875559810420181 1425487616692395933056723)
          ·
            refine ⟨2138231425038593899585085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1425487616692395933056723 2138231425038593899585085)
            ·
              refine ⟨801836784389472712344407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2138231425038593899585085 801836784389472712344407)
              ·
                refine ⟨1202755176584209068516611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 801836784389472712344407 1202755176584209068516611)
                ·
                  refine ⟨1804132764876313602774917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1202755176584209068516611 1804132764876313602774917)
                  ·
                    refine ⟨338274893414308800520297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1804132764876313602774917 338274893414308800520297)
                    ·
                      refine ⟨253706170060731600390223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 338274893414308800520297 253706170060731600390223)
                      ·
                        rfl

theorem cell23_494091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 4, 2].length) (baseStart_494091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494091 prefixEnd_494091 := by exact prefixLift 494091
  have htrace : WordTrace (prefixWord ++ tailWord_494091) baseStart_494091 baseEnd_494091 := by
    simpa [prefixWord, tailWord_494091, baseEnd_494091] using wordTrace_append hprefix tailTrace_494091
  have hstable : (prefixWord ++ tailWord_494091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494091).length < 2 ^ (prefixWord ++ tailWord_494091).sum := by decide
  have hdescent : baseEnd_494091 < baseStart_494091 := by decide
  rcases family_descends (prefixWord ++ tailWord_494091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494131 : List Nat := [1, 1, 1, 2, 4, 2, 5, 2, 5]
def baseStart_494131 : Nat := 118140960795 + 494131 * 2 ^ 59
def prefixEnd_494131 : Nat := 4983230072969 + 3 ^ 40 * 494131 * 2
def baseEnd_494131 : Nat := 28191856587434604876671

theorem tailTrace_494131 : CollatzResearch.WordTrace tailWord_494131 prefixEnd_494131 28191856587434604876671 := by
  unfold tailWord_494131
  simp only [CollatzResearch.WordTrace]
  refine ⟨18022438172855252701210247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12014958781903501800806831 18022438172855252701210247)
  ·
    refine ⟨27033657259282879051815371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18022438172855252701210247 27033657259282879051815371)
    ·
      refine ⟨40550485888924318577723057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27033657259282879051815371 40550485888924318577723057)
      ·
        refine ⟨30412864416693238933292293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40550485888924318577723057 30412864416693238933292293)
        ·
          refine ⟨5702412078129982299992305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30412864416693238933292293 5702412078129982299992305)
          ·
            refine ⟨4276809058597486724994229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5702412078129982299992305 4276809058597486724994229)
            ·
              refine ⟨400950849243514380468209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4276809058597486724994229 400950849243514380468209)
              ·
                refine ⟨300713136932635785351157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 400950849243514380468209 300713136932635785351157)
                ·
                  refine ⟨28191856587434604876671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 300713136932635785351157 28191856587434604876671)
                  ·
                    rfl

theorem cell23_494131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 2, 5].length) (baseStart_494131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494131 prefixEnd_494131 := by exact prefixLift 494131
  have htrace : WordTrace (prefixWord ++ tailWord_494131) baseStart_494131 baseEnd_494131 := by
    simpa [prefixWord, tailWord_494131, baseEnd_494131] using wordTrace_append hprefix tailTrace_494131
  have hstable : (prefixWord ++ tailWord_494131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494131).length < 2 ^ (prefixWord ++ tailWord_494131).sum := by decide
  have hdescent : baseEnd_494131 < baseStart_494131 := by decide
  rcases family_descends (prefixWord ++ tailWord_494131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494142 : List Nat := [4, 2, 1, 4, 1, 1, 1, 3, 2, 2, 2]
def baseStart_494142 : Nat := 118140960795 + 494142 * 2 ^ 59
def prefixEnd_494142 : Nat := 4983230072969 + 3 ^ 40 * 494142 * 2
def baseEnd_494142 : Nat := 253732357574110900852489

theorem tailTrace_494142 : CollatzResearch.WordTrace tailWord_494142 prefixEnd_494142 253732357574110900852489 := by
  unfold tailWord_494142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2252854921976925197482585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12015226250543601053240453 2252854921976925197482585)
  ·
    refine ⟨1689641191482693898111939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2252854921976925197482585 1689641191482693898111939)
    ·
      refine ⟨2534461787224040847167909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1689641191482693898111939 2534461787224040847167909)
      ·
        refine ⟨475211585104507658843983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2534461787224040847167909 475211585104507658843983)
        ·
          refine ⟨712817377656761488265975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475211585104507658843983 712817377656761488265975)
          ·
            refine ⟨1069226066485142232398963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712817377656761488265975 1069226066485142232398963)
            ·
              refine ⟨1603839099727713348598445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1069226066485142232398963 1603839099727713348598445)
              ·
                refine ⟨601439662397892505724417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1603839099727713348598445 601439662397892505724417)
                ·
                  refine ⟨451079746798419379293313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 601439662397892505724417 451079746798419379293313)
                  ·
                    refine ⟨338309810098814534469985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 451079746798419379293313 338309810098814534469985)
                    ·
                      refine ⟨253732357574110900852489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 338309810098814534469985 253732357574110900852489)
                      ·
                        rfl

theorem cell23_494142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_494142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494142 prefixEnd_494142 := by exact prefixLift 494142
  have htrace : WordTrace (prefixWord ++ tailWord_494142) baseStart_494142 baseEnd_494142 := by
    simpa [prefixWord, tailWord_494142, baseEnd_494142] using wordTrace_append hprefix tailTrace_494142
  have hstable : (prefixWord ++ tailWord_494142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494142).length < 2 ^ (prefixWord ++ tailWord_494142).sum := by decide
  have hdescent : baseEnd_494142 < baseStart_494142 := by decide
  rcases family_descends (prefixWord ++ tailWord_494142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494147 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 4]
def baseStart_494147 : Nat := 118140960795 + 494147 * 2 ^ 59
def prefixEnd_494147 : Nat := 4983230072969 + 3 ^ 40 * 494147 * 2
def baseEnd_494147 : Nat := 253734924977383381289965

theorem tailTrace_494147 : CollatzResearch.WordTrace tailWord_494147 prefixEnd_494147 253734924977383381289965 := by
  unfold tailWord_494147
  simp only [CollatzResearch.WordTrace]
  refine ⟨18023021740797287433792695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12015347827198191622528463 18023021740797287433792695)
  ·
    refine ⟨27034532611195931150689043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18023021740797287433792695 27034532611195931150689043)
    ·
      refine ⟨40551798916793896726033565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27034532611195931150689043 40551798916793896726033565)
      ·
        refine ⟨15206924593797711272262587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40551798916793896726033565 15206924593797711272262587)
        ·
          refine ⟨22810386890696566908393881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15206924593797711272262587 22810386890696566908393881)
          ·
            refine ⟨17107790168022425181295411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22810386890696566908393881 17107790168022425181295411)
            ·
              refine ⟨25661685252033637771943117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17107790168022425181295411 25661685252033637771943117)
              ·
                refine ⟨9623131969512614164478669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25661685252033637771943117 9623131969512614164478669)
                ·
                  refine ⟨3608674488567230311679501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9623131969512614164478669 3608674488567230311679501)
                  ·
                    refine ⟨1353252933212711366879813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3608674488567230311679501 1353252933212711366879813)
                    ·
                      refine ⟨253734924977383381289965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1353252933212711366879813 253734924977383381289965)
                      ·
                        rfl

theorem cell23_494147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_494147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494147 prefixEnd_494147 := by exact prefixLift 494147
  have htrace : WordTrace (prefixWord ++ tailWord_494147) baseStart_494147 baseEnd_494147 := by
    simpa [prefixWord, tailWord_494147, baseEnd_494147] using wordTrace_append hprefix tailTrace_494147
  have hstable : (prefixWord ++ tailWord_494147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494147).length < 2 ^ (prefixWord ++ tailWord_494147).sum := by decide
  have hdescent : baseEnd_494147 < baseStart_494147 := by decide
  rcases family_descends (prefixWord ++ tailWord_494147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494204 : List Nat := [2, 2, 2, 1, 1, 2, 4, 3, 6]
def baseStart_494204 : Nat := 118140960795 + 494204 * 2 ^ 59
def prefixEnd_494204 : Nat := 4983230072969 + 3 ^ 40 * 494204 * 2
def baseEnd_494204 : Nat := 28196021486076628697467

theorem tailTrace_494204 : CollatzResearch.WordTrace tailWord_494204 prefixEnd_494204 28196021486076628697467 := by
  unfold tailWord_494204
  simp only [CollatzResearch.WordTrace]
  refine ⟨9012550350795393084308833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12016733801060524112411777 9012550350795393084308833)
  ·
    refine ⟨6759412763096544813231625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9012550350795393084308833 6759412763096544813231625)
    ·
      refine ⟨5069559572322408609923719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6759412763096544813231625 5069559572322408609923719)
      ·
        refine ⟨7604339358483612914885579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5069559572322408609923719 7604339358483612914885579)
        ·
          refine ⟨11406509037725419372328369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7604339358483612914885579 11406509037725419372328369)
          ·
            refine ⟨8554881778294064529246277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11406509037725419372328369 8554881778294064529246277)
            ·
              refine ⟨1604040333430137099233677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8554881778294064529246277 1604040333430137099233677)
              ·
                refine ⟨601515125036301412212629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1604040333430137099233677 601515125036301412212629)
                ·
                  refine ⟨28196021486076628697467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 601515125036301412212629 28196021486076628697467)
                  ·
                    rfl

theorem cell23_494204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 6].length) (baseStart_494204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494204 prefixEnd_494204 := by exact prefixLift 494204
  have htrace : WordTrace (prefixWord ++ tailWord_494204) baseStart_494204 baseEnd_494204 := by
    simpa [prefixWord, tailWord_494204, baseEnd_494204] using wordTrace_append hprefix tailTrace_494204
  have hstable : (prefixWord ++ tailWord_494204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494204).length < 2 ^ (prefixWord ++ tailWord_494204).sum := by decide
  have hdescent : baseEnd_494204 < baseStart_494204 := by decide
  rcases family_descends (prefixWord ++ tailWord_494204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494207 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 6]
def baseStart_494207 : Nat := 118140960795 + 494207 * 2 ^ 59
def prefixEnd_494207 : Nat := 4983230072969 + 3 ^ 40 * 494207 * 2
def baseEnd_494207 : Nat := 253765733816653146539689

theorem tailTrace_494207 : CollatzResearch.WordTrace tailWord_494207 prefixEnd_494207 253765733816653146539689 := by
  unfold tailWord_494207
  simp only [CollatzResearch.WordTrace]
  refine ⟨18025210120579917680976875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12016806747053278453984583 18025210120579917680976875)
  ·
    refine ⟨27037815180869876521465313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18025210120579917680976875 27037815180869876521465313)
    ·
      refine ⟨20278361385652407391098985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27037815180869876521465313 20278361385652407391098985)
      ·
        refine ⟨15208771039239305543324239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20278361385652407391098985 15208771039239305543324239)
        ·
          refine ⟨22813156558858958314986359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15208771039239305543324239 22813156558858958314986359)
          ·
            refine ⟨34219734838288437472479539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22813156558858958314986359 34219734838288437472479539)
            ·
              refine ⟨51329602257432656208719309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34219734838288437472479539 51329602257432656208719309)
              ·
                refine ⟨19248600846537246078269741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51329602257432656208719309 19248600846537246078269741)
                ·
                  refine ⟨7218225317451467279351153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19248600846537246078269741 7218225317451467279351153)
                  ·
                    refine ⟨5413668988088600459513365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7218225317451467279351153 5413668988088600459513365)
                    ·
                      refine ⟨253765733816653146539689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5413668988088600459513365 253765733816653146539689)
                      ·
                        rfl

theorem cell23_494207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_494207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494207 prefixEnd_494207 := by exact prefixLift 494207
  have htrace : WordTrace (prefixWord ++ tailWord_494207) baseStart_494207 baseEnd_494207 := by
    simpa [prefixWord, tailWord_494207, baseEnd_494207] using wordTrace_append hprefix tailTrace_494207
  have hstable : (prefixWord ++ tailWord_494207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494207).length < 2 ^ (prefixWord ++ tailWord_494207).sum := by decide
  have hdescent : baseEnd_494207 < baseStart_494207 := by decide
  rcases family_descends (prefixWord ++ tailWord_494207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494227 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 7]
def baseStart_494227 : Nat := 118140960795 + 494227 * 2 ^ 59
def prefixEnd_494227 : Nat := 4983230072969 + 3 ^ 40 * 494227 * 2
def baseEnd_494227 : Nat := 253776003429743068289597

theorem tailTrace_494227 : CollatzResearch.WordTrace tailWord_494227 prefixEnd_494227 253776003429743068289597 := by
  unfold tailWord_494227
  simp only [CollatzResearch.WordTrace]
  refine ⟨18025939580507461096704935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12017293053671640731136623 18025939580507461096704935)
  ·
    refine ⟨27038909370761191645057403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18025939580507461096704935 27038909370761191645057403)
    ·
      refine ⟨40558364056141787467586105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27038909370761191645057403 40558364056141787467586105)
      ·
        refine ⟨30418773042106340600689579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40558364056141787467586105 30418773042106340600689579)
        ·
          refine ⟨45628159563159510901034369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30418773042106340600689579 45628159563159510901034369)
          ·
            refine ⟨34221119672369633175775777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45628159563159510901034369 34221119672369633175775777)
            ·
              refine ⟨25665839754277224881831833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34221119672369633175775777 25665839754277224881831833)
              ·
                refine ⟨19249379815707918661373875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25665839754277224881831833 19249379815707918661373875)
                ·
                  refine ⟨28874069723561877992060813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19249379815707918661373875 28874069723561877992060813)
                  ·
                    refine ⟨10827776146335704247022805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28874069723561877992060813 10827776146335704247022805)
                    ·
                      refine ⟨253776003429743068289597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 10827776146335704247022805 253776003429743068289597)
                      ·
                        rfl

theorem cell23_494227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 7].length) (baseStart_494227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494227 prefixEnd_494227 := by exact prefixLift 494227
  have htrace : WordTrace (prefixWord ++ tailWord_494227) baseStart_494227 baseEnd_494227 := by
    simpa [prefixWord, tailWord_494227, baseEnd_494227] using wordTrace_append hprefix tailTrace_494227
  have hstable : (prefixWord ++ tailWord_494227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494227).length < 2 ^ (prefixWord ++ tailWord_494227).sum := by decide
  have hdescent : baseEnd_494227 < baseStart_494227 := by decide
  rcases family_descends (prefixWord ++ tailWord_494227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494231 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 5, 1, 3]
def baseStart_494231 : Nat := 118140960795 + 494231 * 2 ^ 59
def prefixEnd_494231 : Nat := 4983230072969 + 3 ^ 40 * 494231 * 2
def baseEnd_494231 : Nat := 253778057352361052639579

theorem tailTrace_494231 : CollatzResearch.WordTrace tailWord_494231 prefixEnd_494231 253778057352361052639579 := by
  unfold tailWord_494231
  simp only [CollatzResearch.WordTrace]
  refine ⟨18026085472492969779850547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12017390314995313186567031 18026085472492969779850547)
  ·
    refine ⟨27039128208739454669775821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18026085472492969779850547 27039128208739454669775821)
    ·
      refine ⟨10139673078277295501165933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27039128208739454669775821 10139673078277295501165933)
      ·
        refine ⟨3802377404353985812937225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10139673078277295501165933 3802377404353985812937225)
        ·
          refine ⟨2851783053265489359702919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3802377404353985812937225 2851783053265489359702919)
          ·
            refine ⟨4277674579898234039554379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2851783053265489359702919 4277674579898234039554379)
            ·
              refine ⟨6416511869847351059331569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4277674579898234039554379 6416511869847351059331569)
              ·
                refine ⟨4812383902385513294498677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6416511869847351059331569 4812383902385513294498677)
                ·
                  refine ⟨451160990848641871359251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4812383902385513294498677 451160990848641871359251)
                  ·
                    refine ⟨676741486272962807038877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 451160990848641871359251 676741486272962807038877)
                    ·
                      refine ⟨253778057352361052639579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 676741486272962807038877 253778057352361052639579)
                      ·
                        rfl

theorem cell23_494231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_494231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494231 prefixEnd_494231 := by exact prefixLift 494231
  have htrace : WordTrace (prefixWord ++ tailWord_494231) baseStart_494231 baseEnd_494231 := by
    simpa [prefixWord, tailWord_494231, baseEnd_494231] using wordTrace_append hprefix tailTrace_494231
  have hstable : (prefixWord ++ tailWord_494231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494231).length < 2 ^ (prefixWord ++ tailWord_494231).sum := by decide
  have hdescent : baseEnd_494231 < baseStart_494231 := by decide
  rcases family_descends (prefixWord ++ tailWord_494231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494271 : List Nat := [1, 1, 2, 2, 2, 4, 1, 4, 1, 1, 4]
def baseStart_494271 : Nat := 118140960795 + 494271 * 2 ^ 59
def prefixEnd_494271 : Nat := 4983230072969 + 3 ^ 40 * 494271 * 2
def baseEnd_494271 : Nat := 253798596578540896139395

theorem tailTrace_494271 : CollatzResearch.WordTrace tailWord_494271 prefixEnd_494271 253798596578540896139395 := by
  unfold tailWord_494271
  simp only [CollatzResearch.WordTrace]
  refine ⟨18027544392348056611306667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12018362928232037740871111 18027544392348056611306667)
  ·
    refine ⟨27041316588522084916960001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18027544392348056611306667 27041316588522084916960001)
    ·
      refine ⟨20280987441391563687720001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27041316588522084916960001 20280987441391563687720001)
      ·
        refine ⟨15210740581043672765790001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20280987441391563687720001 15210740581043672765790001)
        ·
          refine ⟨11408055435782754574342501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15210740581043672765790001 11408055435782754574342501)
          ·
            refine ⟨2139010394209266482689219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11408055435782754574342501 2139010394209266482689219)
            ·
              refine ⟨3208515591313899724033829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2139010394209266482689219 3208515591313899724033829)
              ·
                refine ⟨601596673371356198256343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3208515591313899724033829 601596673371356198256343)
                ·
                  refine ⟨902395010057034297384515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 601596673371356198256343 902395010057034297384515)
                  ·
                    refine ⟨1353592515085551446076773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 902395010057034297384515 1353592515085551446076773)
                    ·
                      refine ⟨253798596578540896139395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1353592515085551446076773 253798596578540896139395)
                      ·
                        rfl

theorem cell23_494271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 1, 4].length) (baseStart_494271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494271 prefixEnd_494271 := by exact prefixLift 494271
  have htrace : WordTrace (prefixWord ++ tailWord_494271) baseStart_494271 baseEnd_494271 := by
    simpa [prefixWord, tailWord_494271, baseEnd_494271] using wordTrace_append hprefix tailTrace_494271
  have hstable : (prefixWord ++ tailWord_494271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494271).length < 2 ^ (prefixWord ++ tailWord_494271).sum := by decide
  have hdescent : baseEnd_494271 < baseStart_494271 := by decide
  rcases family_descends (prefixWord ++ tailWord_494271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494282 : List Nat := [3, 1, 2, 1, 4, 3, 1, 3, 1, 1, 3]
def baseStart_494282 : Nat := 118140960795 + 494282 * 2 ^ 59
def prefixEnd_494282 : Nat := 4983230072969 + 3 ^ 40 * 494282 * 2
def baseEnd_494282 : Nat := 253804244865740353101845

theorem tailTrace_494282 : CollatzResearch.WordTrace tailWord_494282 prefixEnd_494282 253804244865740353101845 := by
  unfold tailWord_494282
  simp only [CollatzResearch.WordTrace]
  refine ⟨4506986398827051372489275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12018630396872136993304733 4506986398827051372489275)
  ·
    refine ⟨6760479598240577058733913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4506986398827051372489275 6760479598240577058733913)
    ·
      refine ⟨5070359698680432794050435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6760479598240577058733913 5070359698680432794050435)
      ·
        refine ⟨7605539548020649191075653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5070359698680432794050435 7605539548020649191075653)
        ·
          refine ⟨1426038665253871723326685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7605539548020649191075653 1426038665253871723326685)
          ·
            refine ⟨534764499470201896247507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1426038665253871723326685 534764499470201896247507)
            ·
              refine ⟨802146749205302844371261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534764499470201896247507 802146749205302844371261)
              ·
                refine ⟨300805030951988566639223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 802146749205302844371261 300805030951988566639223)
                ·
                  refine ⟨451207546427982849958835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 300805030951988566639223 451207546427982849958835)
                  ·
                    refine ⟨676811319641974274938253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 451207546427982849958835 676811319641974274938253)
                    ·
                      refine ⟨253804244865740353101845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 676811319641974274938253 253804244865740353101845)
                      ·
                        rfl

theorem cell23_494282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 3, 1, 1, 3].length) (baseStart_494282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494282 prefixEnd_494282 := by exact prefixLift 494282
  have htrace : WordTrace (prefixWord ++ tailWord_494282) baseStart_494282 baseEnd_494282 := by
    simpa [prefixWord, tailWord_494282, baseEnd_494282] using wordTrace_append hprefix tailTrace_494282
  have hstable : (prefixWord ++ tailWord_494282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494282).length < 2 ^ (prefixWord ++ tailWord_494282).sum := by decide
  have hdescent : baseEnd_494282 < baseStart_494282 := by decide
  rcases family_descends (prefixWord ++ tailWord_494282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494305 : List Nat := [1, 2, 3, 1, 4, 1, 3, 1, 3, 2, 2]
def baseStart_494305 : Nat := 118140960795 + 494305 * 2 ^ 59
def prefixEnd_494305 : Nat := 4983230072969 + 3 ^ 40 * 494305 * 2
def baseEnd_494305 : Nat := 253816054920793763114239

theorem tailTrace_494305 : CollatzResearch.WordTrace tailWord_494305 prefixEnd_494305 253816054920793763114239 := by
  unfold tailWord_494305
  simp only [CollatzResearch.WordTrace]
  refine ⟨18028784474224880418044369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12019189649483253612029579 18028784474224880418044369)
  ·
    refine ⟨13521588355668660313533277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18028784474224880418044369 13521588355668660313533277)
    ·
      refine ⟨5070595633375747617574979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13521588355668660313533277 5070595633375747617574979)
      ·
        refine ⟨7605893450063621426362469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5070595633375747617574979 7605893450063621426362469)
        ·
          refine ⟨1426105021886929017442963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7605893450063621426362469 1426105021886929017442963)
          ·
            refine ⟨2139157532830393526164445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1426105021886929017442963 2139157532830393526164445)
            ·
              refine ⟨802184074811397572311667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2139157532830393526164445 802184074811397572311667)
              ·
                refine ⟨1203276112217096358467501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 802184074811397572311667 1203276112217096358467501)
                ·
                  refine ⟨451228542081411134425313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1203276112217096358467501 451228542081411134425313)
                  ·
                    refine ⟨338421406561058350818985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 451228542081411134425313 338421406561058350818985)
                    ·
                      refine ⟨253816054920793763114239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 338421406561058350818985 253816054920793763114239)
                      ·
                        rfl

theorem cell23_494305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 3, 2, 2].length) (baseStart_494305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494305 prefixEnd_494305 := by exact prefixLift 494305
  have htrace : WordTrace (prefixWord ++ tailWord_494305) baseStart_494305 baseEnd_494305 := by
    simpa [prefixWord, tailWord_494305, baseEnd_494305] using wordTrace_append hprefix tailTrace_494305
  have hstable : (prefixWord ++ tailWord_494305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494305).length < 2 ^ (prefixWord ++ tailWord_494305).sum := by decide
  have hdescent : baseEnd_494305 < baseStart_494305 := by decide
  rcases family_descends (prefixWord ++ tailWord_494305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494314 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 1, 4, 6]
def baseStart_494314 : Nat := 118140960795 + 494314 * 2 ^ 59
def prefixEnd_494314 : Nat := 4983230072969 + 3 ^ 40 * 494314 * 2
def baseEnd_494314 : Nat := 253820676246684227901697

theorem tailTrace_494314 : CollatzResearch.WordTrace tailWord_494314 prefixEnd_494314 253820676246684227901697 := by
  unfold tailWord_494314
  simp only [CollatzResearch.WordTrace]
  refine ⟨4507278182798068738780499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12019408487461516636747997 4507278182798068738780499)
  ·
    refine ⟨6760917274197103108170749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4507278182798068738780499 6760917274197103108170749)
    ·
      refine ⟨2535343977823913665564031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6760917274197103108170749 2535343977823913665564031)
      ·
        refine ⟨3803015966735870498346047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2535343977823913665564031 3803015966735870498346047)
        ·
          refine ⟨5704523950103805747519071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3803015966735870498346047 5704523950103805747519071)
          ·
            refine ⟨8556785925155708621278607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5704523950103805747519071 8556785925155708621278607)
            ·
              refine ⟨12835178887733562931917911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8556785925155708621278607 12835178887733562931917911)
              ·
                refine ⟨19252768331600344397876867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12835178887733562931917911 19252768331600344397876867)
                ·
                  refine ⟨28879152497400516596815301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19252768331600344397876867 28879152497400516596815301)
                  ·
                    refine ⟨5414841093262596861902869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28879152497400516596815301 5414841093262596861902869)
                    ·
                      refine ⟨253820676246684227901697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5414841093262596861902869 253820676246684227901697)
                      ·
                        rfl

theorem cell23_494314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_494314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494314 prefixEnd_494314 := by exact prefixLift 494314
  have htrace : WordTrace (prefixWord ++ tailWord_494314) baseStart_494314 baseEnd_494314 := by
    simpa [prefixWord, tailWord_494314, baseEnd_494314] using wordTrace_append hprefix tailTrace_494314
  have hstable : (prefixWord ++ tailWord_494314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494314).length < 2 ^ (prefixWord ++ tailWord_494314).sum := by decide
  have hdescent : baseEnd_494314 < baseStart_494314 := by decide
  rcases family_descends (prefixWord ++ tailWord_494314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494321 : List Nat := [1, 2, 2, 2, 2, 2, 2, 3, 1, 3, 3]
def baseStart_494321 : Nat := 118140960795 + 494321 * 2 ^ 59
def prefixEnd_494321 : Nat := 4983230072969 + 3 ^ 40 * 494321 * 2
def baseEnd_494321 : Nat := 253824270611265700514165

theorem tailTrace_494321 : CollatzResearch.WordTrace tailWord_494321 prefixEnd_494321 253824270611265700514165 := by
  unfold tailWord_494321
  simp only [CollatzResearch.WordTrace]
  refine ⟨18029368042166915150626817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12019578694777943433751211 18029368042166915150626817)
  ·
    refine ⟨13522026031625186362970113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18029368042166915150626817 13522026031625186362970113)
    ·
      refine ⟨10141519523718889772227585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13522026031625186362970113 10141519523718889772227585)
      ·
        refine ⟨7606139642789167329170689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10141519523718889772227585 7606139642789167329170689)
        ·
          refine ⟨5704604732091875496878017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7606139642789167329170689 5704604732091875496878017)
          ·
            refine ⟨4278453549068906622658513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5704604732091875496878017 4278453549068906622658513)
            ·
              refine ⟨3208840161801679966993885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4278453549068906622658513 3208840161801679966993885)
              ·
                refine ⟨1203315060675629987622707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3208840161801679966993885 1203315060675629987622707)
                ·
                  refine ⟨1804972591013444981434061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1203315060675629987622707 1804972591013444981434061)
                  ·
                    refine ⟨676864721630041868037773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1804972591013444981434061 676864721630041868037773)
                    ·
                      refine ⟨253824270611265700514165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 676864721630041868037773 253824270611265700514165)
                      ·
                        rfl

theorem cell23_494321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_494321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494321 prefixEnd_494321 := by exact prefixLift 494321
  have htrace : WordTrace (prefixWord ++ tailWord_494321) baseStart_494321 baseEnd_494321 := by
    simpa [prefixWord, tailWord_494321, baseEnd_494321] using wordTrace_append hprefix tailTrace_494321
  have hstable : (prefixWord ++ tailWord_494321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494321).length < 2 ^ (prefixWord ++ tailWord_494321).sum := by decide
  have hdescent : baseEnd_494321 < baseStart_494321 := by decide
  rcases family_descends (prefixWord ++ tailWord_494321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494338 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 3, 3, 3]
def baseStart_494338 : Nat := 118140960795 + 494338 * 2 ^ 59
def prefixEnd_494338 : Nat := 4983230072969 + 3 ^ 40 * 494338 * 2
def baseEnd_494338 : Nat := 253832999782392134001587

theorem tailTrace_494338 : CollatzResearch.WordTrace tailWord_494338 prefixEnd_494338 253832999782392134001587 := by
  unfold tailWord_494338
  simp only [CollatzResearch.WordTrace]
  refine ⟨4507497020776331763498917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12019992055403551369330445 4507497020776331763498917)
  ·
    refine ⟨845155691395562205656047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4507497020776331763498917 845155691395562205656047)
    ·
      refine ⟨1267733537093343308484071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 845155691395562205656047 1267733537093343308484071)
      ·
        refine ⟨1901600305640014962726107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1267733537093343308484071 1901600305640014962726107)
        ·
          refine ⟨2852400458460022444089161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1901600305640014962726107 2852400458460022444089161)
          ·
            refine ⟨2139300343845016833066871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2852400458460022444089161 2139300343845016833066871)
            ·
              refine ⟨3208950515767525249600307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2139300343845016833066871 3208950515767525249600307)
              ·
                refine ⟨4813425773651287874400461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3208950515767525249600307 4813425773651287874400461)
                ·
                  refine ⟨1805034665119232952900173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4813425773651287874400461 1805034665119232952900173)
                  ·
                    refine ⟨676887999419712357337565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1805034665119232952900173 676887999419712357337565)
                    ·
                      refine ⟨253832999782392134001587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 676887999419712357337565 253832999782392134001587)
                      ·
                        rfl

theorem cell23_494338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_494338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494338 prefixEnd_494338 := by exact prefixLift 494338
  have htrace : WordTrace (prefixWord ++ tailWord_494338) baseStart_494338 baseEnd_494338 := by
    simpa [prefixWord, tailWord_494338, baseEnd_494338] using wordTrace_append hprefix tailTrace_494338
  have hstable : (prefixWord ++ tailWord_494338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494338).length < 2 ^ (prefixWord ++ tailWord_494338).sum := by decide
  have hdescent : baseEnd_494338 < baseStart_494338 := by decide
  rcases family_descends (prefixWord ++ tailWord_494338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494406 : List Nat := [6, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3]
def baseStart_494406 : Nat := 118140960795 + 494406 * 2 ^ 59
def prefixEnd_494406 : Nat := 4983230072969 + 3 ^ 40 * 494406 * 2
def baseEnd_494406 : Nat := 253867916466897867951275

theorem tailTrace_494406 : CollatzResearch.WordTrace tailWord_494406 prefixEnd_494406 253867916466897867951275 := by
  unfold tailWord_494406
  simp only [CollatzResearch.WordTrace]
  refine ⟨563514632714342958358471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12021645497905983111647381 563514632714342958358471)
  ·
    refine ⟨845271949071514437537707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 563514632714342958358471 845271949071514437537707)
    ·
      refine ⟨1267907923607271656306561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 845271949071514437537707 1267907923607271656306561)
      ·
        refine ⟨950930942705453742229921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1267907923607271656306561 950930942705453742229921)
        ·
          refine ⟨713198207029090306672441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 950930942705453742229921 713198207029090306672441)
          ·
            refine ⟨534898655271817730004331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 713198207029090306672441 534898655271817730004331)
            ·
              refine ⟨802347982907726595006497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534898655271817730004331 802347982907726595006497)
              ·
                refine ⟨601760987180794946254873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 802347982907726595006497 601760987180794946254873)
                ·
                  refine ⟨451320740385596209691155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 601760987180794946254873 451320740385596209691155)
                  ·
                    refine ⟨676981110578394314536733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 451320740385596209691155 676981110578394314536733)
                    ·
                      refine ⟨253867916466897867951275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 676981110578394314536733 253867916466897867951275)
                      ·
                        rfl

theorem cell23_494406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_494406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494406 prefixEnd_494406 := by exact prefixLift 494406
  have htrace : WordTrace (prefixWord ++ tailWord_494406) baseStart_494406 baseEnd_494406 := by
    simpa [prefixWord, tailWord_494406, baseEnd_494406] using wordTrace_append hprefix tailTrace_494406
  have hstable : (prefixWord ++ tailWord_494406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494406).length < 2 ^ (prefixWord ++ tailWord_494406).sum := by decide
  have hdescent : baseEnd_494406 < baseStart_494406 := by decide
  rcases family_descends (prefixWord ++ tailWord_494406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494412 : List Nat := [2, 2, 1, 3, 3, 1, 3, 2, 2, 2, 2]
def baseStart_494412 : Nat := 118140960795 + 494412 * 2 ^ 59
def prefixEnd_494412 : Nat := 4983230072969 + 3 ^ 40 * 494412 * 2
def baseEnd_494412 : Nat := 253870997350824844476247

theorem tailTrace_494412 : CollatzResearch.WordTrace tailWord_494412 prefixEnd_494412 253870997350824844476247 := by
  unfold tailWord_494412
  simp only [CollatzResearch.WordTrace]
  refine ⟨9016343542418618846094745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12021791389891491794792993 9016343542418618846094745)
  ·
    refine ⟨6762257656813964134571059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9016343542418618846094745 6762257656813964134571059)
    ·
      refine ⟨10143386485220946201856589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6762257656813964134571059 10143386485220946201856589)
      ·
        refine ⟨3803769931957854825696221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10143386485220946201856589 3803769931957854825696221)
        ·
          refine ⟨1426413724484195559636083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3803769931957854825696221 1426413724484195559636083)
          ·
            refine ⟨2139620586726293339454125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1426413724484195559636083 2139620586726293339454125)
            ·
              refine ⟨802357720022360002295297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2139620586726293339454125 802357720022360002295297)
              ·
                refine ⟨601768290016770001721473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 802357720022360002295297 601768290016770001721473)
                ·
                  refine ⟨451326217512577501291105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 601768290016770001721473 451326217512577501291105)
                  ·
                    refine ⟨338494663134433125968329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 451326217512577501291105 338494663134433125968329)
                    ·
                      refine ⟨253870997350824844476247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 338494663134433125968329 253870997350824844476247)
                      ·
                        rfl

theorem cell23_494412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_494412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494412 prefixEnd_494412 := by exact prefixLift 494412
  have htrace : WordTrace (prefixWord ++ tailWord_494412) baseStart_494412 baseEnd_494412 := by
    simpa [prefixWord, tailWord_494412, baseEnd_494412] using wordTrace_append hprefix tailTrace_494412
  have hstable : (prefixWord ++ tailWord_494412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494412).length < 2 ^ (prefixWord ++ tailWord_494412).sum := by decide
  have hdescent : baseEnd_494412 < baseStart_494412 := by decide
  rcases family_descends (prefixWord ++ tailWord_494412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494418 : List Nat := [3, 2, 2, 1, 1, 2, 1, 6, 5]
def baseStart_494418 : Nat := 118140960795 + 494418 * 2 ^ 59
def prefixEnd_494418 : Nat := 4983230072969 + 3 ^ 40 * 494418 * 2
def baseEnd_494418 : Nat := 28208230914972424555691

theorem tailTrace_494418 : CollatzResearch.WordTrace tailWord_494418 prefixEnd_494418 28208230914972424555691 := by
  unfold tailWord_494418
  simp only [CollatzResearch.WordTrace]
  refine ⟨4508226480703875179226977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12021937281877000477938605 4508226480703875179226977)
  ·
    refine ⟨3381169860527906384420233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4508226480703875179226977 3381169860527906384420233)
    ·
      refine ⟨2535877395395929788315175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3381169860527906384420233 2535877395395929788315175)
      ·
        refine ⟨3803816093093894682472763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2535877395395929788315175 3803816093093894682472763)
        ·
          refine ⟨5705724139640842023709145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3803816093093894682472763 5705724139640842023709145)
          ·
            refine ⟨4279293104730631517781859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5705724139640842023709145 4279293104730631517781859)
            ·
              refine ⟨6418939657095947276672789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4279293104730631517781859 6418939657095947276672789)
              ·
                refine ⟨300887796426372528594037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6418939657095947276672789 300887796426372528594037)
                ·
                  refine ⟨28208230914972424555691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 300887796426372528594037 28208230914972424555691)
                  ·
                    rfl

theorem cell23_494418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 6, 5].length) (baseStart_494418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494418 prefixEnd_494418 := by exact prefixLift 494418
  have htrace : WordTrace (prefixWord ++ tailWord_494418) baseStart_494418 baseEnd_494418 := by
    simpa [prefixWord, tailWord_494418, baseEnd_494418] using wordTrace_append hprefix tailTrace_494418
  have hstable : (prefixWord ++ tailWord_494418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494418).length < 2 ^ (prefixWord ++ tailWord_494418).sum := by decide
  have hdescent : baseEnd_494418 < baseStart_494418 := by decide
  rcases family_descends (prefixWord ++ tailWord_494418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494451 : List Nat := [1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 4]
def baseStart_494451 : Nat := 118140960795 + 494451 * 2 ^ 59
def prefixEnd_494451 : Nat := 4983230072969 + 3 ^ 40 * 494451 * 2
def baseEnd_494451 : Nat := 253891023096350191888567

theorem tailTrace_494451 : CollatzResearch.WordTrace tailWord_494451 prefixEnd_494451 253891023096350191888567 := by
  unfold tailWord_494451
  simp only [CollatzResearch.WordTrace]
  refine ⟨18034109531695947352859207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12022739687797298235239471 18034109531695947352859207)
  ·
    refine ⟨27051164297543921029288811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18034109531695947352859207 27051164297543921029288811)
    ·
      refine ⟨40576746446315881543933217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27051164297543921029288811 40576746446315881543933217)
      ·
        refine ⟨30432559834736911157949913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40576746446315881543933217 30432559834736911157949913)
        ·
          refine ⟨22824419876052683368462435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30432559834736911157949913 22824419876052683368462435)
          ·
            refine ⟨34236629814079025052693653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22824419876052683368462435 34236629814079025052693653)
            ·
              refine ⟨1604842022534954299345015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34236629814079025052693653 1604842022534954299345015)
              ·
                refine ⟨2407263033802431449017523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1604842022534954299345015 2407263033802431449017523)
                ·
                  refine ⟨3610894550703647173526285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2407263033802431449017523 3610894550703647173526285)
                  ·
                    refine ⟨1354085456513867690072357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3610894550703647173526285 1354085456513867690072357)
                    ·
                      refine ⟨253891023096350191888567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1354085456513867690072357 253891023096350191888567)
                      ·
                        rfl

theorem cell23_494451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 4].length) (baseStart_494451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494451 prefixEnd_494451 := by exact prefixLift 494451
  have htrace : WordTrace (prefixWord ++ tailWord_494451) baseStart_494451 baseEnd_494451 := by
    simpa [prefixWord, tailWord_494451, baseEnd_494451] using wordTrace_append hprefix tailTrace_494451
  have hstable : (prefixWord ++ tailWord_494451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494451).length < 2 ^ (prefixWord ++ tailWord_494451).sum := by decide
  have hdescent : baseEnd_494451 < baseStart_494451 := by decide
  rcases family_descends (prefixWord ++ tailWord_494451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494525 : List Nat := [1, 4, 1, 2, 4, 1, 2, 2, 6]
def baseStart_494525 : Nat := 118140960795 + 494525 * 2 ^ 59
def prefixEnd_494525 : Nat := 4983230072969 + 3 ^ 40 * 494525 * 2
def baseEnd_494525 : Nat := 28214335629420322484803

theorem tailTrace_494525 : CollatzResearch.WordTrace tailWord_494525 prefixEnd_494525 28214335629420322484803 := by
  unfold tailWord_494525
  simp only [CollatzResearch.WordTrace]
  refine ⟨18036808533427857991053029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12024539022285238660702019 18036808533427857991053029)
  ·
    refine ⟨3381901600017723373322443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18036808533427857991053029 3381901600017723373322443)
    ·
      refine ⟨5072852400026585059983665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3381901600017723373322443 5072852400026585059983665)
      ·
        refine ⟨3804639300019938794987749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5072852400026585059983665 3804639300019938794987749)
        ·
          refine ⟨713369868753738524060203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3804639300019938794987749 713369868753738524060203)
          ·
            refine ⟨1070054803130607786090305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713369868753738524060203 1070054803130607786090305)
            ·
              refine ⟨802541102347955839567729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1070054803130607786090305 802541102347955839567729)
              ·
                refine ⟨601905826760966879675797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 802541102347955839567729 601905826760966879675797)
                ·
                  refine ⟨28214335629420322484803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 601905826760966879675797 28214335629420322484803)
                  ·
                    rfl

theorem cell23_494525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 6].length) (baseStart_494525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494525 prefixEnd_494525 := by exact prefixLift 494525
  have htrace : WordTrace (prefixWord ++ tailWord_494525) baseStart_494525 baseEnd_494525 := by
    simpa [prefixWord, tailWord_494525, baseEnd_494525] using wordTrace_append hprefix tailTrace_494525
  have hstable : (prefixWord ++ tailWord_494525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494525).length < 2 ^ (prefixWord ++ tailWord_494525).sum := by decide
  have hdescent : baseEnd_494525 < baseStart_494525 := by decide
  rcases family_descends (prefixWord ++ tailWord_494525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494568 : List Nat := [2, 1, 4, 1, 1, 1, 4, 2, 1, 6]
def baseStart_494568 : Nat := 118140960795 + 494568 * 2 ^ 59
def prefixEnd_494568 : Nat := 4983230072969 + 3 ^ 40 * 494568 * 2
def baseEnd_494568 : Nat := 84650366777642078041843

theorem tailTrace_494568 : CollatzResearch.WordTrace tailWord_494568 prefixEnd_494568 84650366777642078041843 := by
  unfold tailWord_494568
  simp only [CollatzResearch.WordTrace]
  refine ⟨9019188436136038167434179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12025584581514717556578905 9019188436136038167434179)
  ·
    refine ⟨13528782654204057251151269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9019188436136038167434179 13528782654204057251151269)
    ·
      refine ⟨2536646747663260734590863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13528782654204057251151269 2536646747663260734590863)
      ·
        refine ⟨3804970121494891101886295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2536646747663260734590863 3804970121494891101886295)
        ·
          refine ⟨5707455182242336652829443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3804970121494891101886295 5707455182242336652829443)
          ·
            refine ⟨8561182773363504979244165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5707455182242336652829443 8561182773363504979244165)
            ·
              refine ⟨1605221770005657183608281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8561182773363504979244165 1605221770005657183608281)
              ·
                refine ⟨1203916327504242887706211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1605221770005657183608281 1203916327504242887706211)
                ·
                  refine ⟨1805874491256364331559317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1203916327504242887706211 1805874491256364331559317)
                  ·
                    refine ⟨84650366777642078041843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1805874491256364331559317 84650366777642078041843)
                    ·
                      rfl

theorem cell23_494568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_494568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494568 prefixEnd_494568 := by exact prefixLift 494568
  have htrace : WordTrace (prefixWord ++ tailWord_494568) baseStart_494568 baseEnd_494568 := by
    simpa [prefixWord, tailWord_494568, baseEnd_494568] using wordTrace_append hprefix tailTrace_494568
  have hstable : (prefixWord ++ tailWord_494568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494568).length < 2 ^ (prefixWord ++ tailWord_494568).sum := by decide
  have hdescent : baseEnd_494568 < baseStart_494568 := by decide
  rcases family_descends (prefixWord ++ tailWord_494568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494571 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 6]
def baseStart_494571 : Nat := 118140960795 + 494571 * 2 ^ 59
def prefixEnd_494571 : Nat := 4983230072969 + 3 ^ 40 * 494571 * 2
def baseEnd_494571 : Nat := 253952640774889722388015

theorem tailTrace_494571 : CollatzResearch.WordTrace tailWord_494571 prefixEnd_494571 253952640774889722388015 := by
  unfold tailWord_494571
  simp only [CollatzResearch.WordTrace]
  refine ⟨18038486291261207847227567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12025657527507471898151711 18038486291261207847227567)
  ·
    refine ⟨27057729436891811770841351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18038486291261207847227567 27057729436891811770841351)
    ·
      refine ⟨40586594155337717656262027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27057729436891811770841351 40586594155337717656262027)
      ·
        refine ⟨60879891233006576484393041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40586594155337717656262027 60879891233006576484393041)
        ·
          refine ⟨45659918424754932363294781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60879891233006576484393041 45659918424754932363294781)
          ·
            refine ⟨17122469409283099636235543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45659918424754932363294781 17122469409283099636235543)
            ·
              refine ⟨25683704113924649454353315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17122469409283099636235543 25683704113924649454353315)
              ·
                refine ⟨38525556170886974181529973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25683704113924649454353315 38525556170886974181529973)
                ·
                  refine ⟨3611770891020653829518435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38525556170886974181529973 3611770891020653829518435)
                  ·
                    refine ⟨5417656336530980744277653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3611770891020653829518435 5417656336530980744277653)
                    ·
                      refine ⟨253952640774889722388015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5417656336530980744277653 253952640774889722388015)
                      ·
                        rfl

theorem cell23_494571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 6].length) (baseStart_494571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494571 prefixEnd_494571 := by exact prefixLift 494571
  have htrace : WordTrace (prefixWord ++ tailWord_494571) baseStart_494571 baseEnd_494571 := by
    simpa [prefixWord, tailWord_494571, baseEnd_494571] using wordTrace_append hprefix tailTrace_494571
  have hstable : (prefixWord ++ tailWord_494571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494571).length < 2 ^ (prefixWord ++ tailWord_494571).sum := by decide
  have hdescent : baseEnd_494571 < baseStart_494571 := by decide
  rcases family_descends (prefixWord ++ tailWord_494571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494575 : List Nat := [1, 1, 2, 1, 4, 4, 1, 3, 1, 1, 4]
def baseStart_494575 : Nat := 118140960795 + 494575 * 2 ^ 59
def prefixEnd_494575 : Nat := 4983230072969 + 3 ^ 40 * 494575 * 2
def baseEnd_494575 : Nat := 253954694697507706737997

theorem tailTrace_494575 : CollatzResearch.WordTrace tailWord_494575 prefixEnd_494575 253954694697507706737997 := by
  unfold tailWord_494575
  simp only [CollatzResearch.WordTrace]
  refine ⟨18038632183246716530373179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12025754788831144353582119 18038632183246716530373179)
  ·
    refine ⟨27057948274870074795559769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18038632183246716530373179 27057948274870074795559769)
    ·
      refine ⟨20293461206152556096669827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27057948274870074795559769 20293461206152556096669827)
      ·
        refine ⟨30440191809228834145004741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20293461206152556096669827 30440191809228834145004741)
        ·
          refine ⟨5707535964230406402188389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30440191809228834145004741 5707535964230406402188389)
          ·
            refine ⟨1070162993293201200410323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5707535964230406402188389 1070162993293201200410323)
            ·
              refine ⟨1605244489939801800615485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1070162993293201200410323 1605244489939801800615485)
              ·
                refine ⟨601966683727425675230807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1605244489939801800615485 601966683727425675230807)
                ·
                  refine ⟨902950025591138512846211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 601966683727425675230807 902950025591138512846211)
                  ·
                    refine ⟨1354425038386707769269317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 902950025591138512846211 1354425038386707769269317)
                    ·
                      refine ⟨253954694697507706737997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1354425038386707769269317 253954694697507706737997)
                      ·
                        rfl

theorem cell23_494575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 1, 4].length) (baseStart_494575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494575 prefixEnd_494575 := by exact prefixLift 494575
  have htrace : WordTrace (prefixWord ++ tailWord_494575) baseStart_494575 baseEnd_494575 := by
    simpa [prefixWord, tailWord_494575, baseEnd_494575] using wordTrace_append hprefix tailTrace_494575
  have hstable : (prefixWord ++ tailWord_494575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494575).length < 2 ^ (prefixWord ++ tailWord_494575).sum := by decide
  have hdescent : baseEnd_494575 < baseStart_494575 := by decide
  rcases family_descends (prefixWord ++ tailWord_494575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494591 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 7]
def baseStart_494591 : Nat := 118140960795 + 494591 * 2 ^ 59
def prefixEnd_494591 : Nat := 4983230072969 + 3 ^ 40 * 494591 * 2
def baseEnd_494591 : Nat := 253962910387979644137923

theorem tailTrace_494591 : CollatzResearch.WordTrace tailWord_494591 prefixEnd_494591 253962910387979644137923 := by
  unfold tailWord_494591
  simp only [CollatzResearch.WordTrace]
  refine ⟨18039215751188751262955627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12026143834125834175303751 18039215751188751262955627)
  ·
    refine ⟨27058823626783126894433441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18039215751188751262955627 27058823626783126894433441)
    ·
      refine ⟨20294117720087345170825081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27058823626783126894433441 20294117720087345170825081)
      ·
        refine ⟨15220588290065508878118811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20294117720087345170825081 15220588290065508878118811)
        ·
          refine ⟨22830882435098263317178217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15220588290065508878118811 22830882435098263317178217)
          ·
            refine ⟨17123161826323697487883663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22830882435098263317178217 17123161826323697487883663)
            ·
              refine ⟨25684742739485546231825495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17123161826323697487883663 25684742739485546231825495)
              ·
                refine ⟨38527114109228319347738243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25684742739485546231825495 38527114109228319347738243)
                ·
                  refine ⟨57790671163842479021607365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38527114109228319347738243 57790671163842479021607365)
                  ·
                    refine ⟨10835750843220464816551381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57790671163842479021607365 10835750843220464816551381)
                    ·
                      refine ⟨253962910387979644137923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 10835750843220464816551381 253962910387979644137923)
                      ·
                        rfl

theorem cell23_494591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_494591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494591 prefixEnd_494591 := by exact prefixLift 494591
  have htrace : WordTrace (prefixWord ++ tailWord_494591) baseStart_494591 baseEnd_494591 := by
    simpa [prefixWord, tailWord_494591, baseEnd_494591] using wordTrace_append hprefix tailTrace_494591
  have hstable : (prefixWord ++ tailWord_494591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494591).length < 2 ^ (prefixWord ++ tailWord_494591).sum := by decide
  have hdescent : baseEnd_494591 < baseStart_494591 := by decide
  rcases family_descends (prefixWord ++ tailWord_494591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494615 : List Nat := [1, 1, 3, 5, 1, 1, 4, 7]
def baseStart_494615 : Nat := 118140960795 + 494615 * 2 ^ 59
def prefixEnd_494615 : Nat := 4983230072969 + 3 ^ 40 * 494615 * 2
def baseEnd_494615 : Nat := 9406490145321761119919

theorem tailTrace_494615 : CollatzResearch.WordTrace tailWord_494615 prefixEnd_494615 9406490145321761119919 := by
  unfold tailWord_494615
  simp only [CollatzResearch.WordTrace]
  refine ⟨18040091103101803361829299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12026727402067868907886199 18040091103101803361829299)
  ·
    refine ⟨27060136654652705042743949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18040091103101803361829299 27060136654652705042743949)
    ·
      refine ⟨10147551245494764391028981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27060136654652705042743949 10147551245494764391028981)
      ·
        refine ⟨951332929265134161658967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10147551245494764391028981 951332929265134161658967)
        ·
          refine ⟨1426999393897701242488451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 951332929265134161658967 1426999393897701242488451)
          ·
            refine ⟨2140499090846551863732677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1426999393897701242488451 2140499090846551863732677)
            ·
              refine ⟨401343579533728474449877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2140499090846551863732677 401343579533728474449877)
              ·
                refine ⟨9406490145321761119919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 401343579533728474449877 9406490145321761119919)
                ·
                  rfl

theorem cell23_494615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 7].length) (baseStart_494615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494615 prefixEnd_494615 := by exact prefixLift 494615
  have htrace : WordTrace (prefixWord ++ tailWord_494615) baseStart_494615 baseEnd_494615 := by
    simpa [prefixWord, tailWord_494615, baseEnd_494615] using wordTrace_append hprefix tailTrace_494615
  have hstable : (prefixWord ++ tailWord_494615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494615).length < 2 ^ (prefixWord ++ tailWord_494615).sum := by decide
  have hdescent : baseEnd_494615 < baseStart_494615 := by decide
  rcases family_descends (prefixWord ++ tailWord_494615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494626 : List Nat := [3, 3, 1, 1, 1, 3, 3, 3, 1, 2, 2]
def baseStart_494626 : Nat := 118140960795 + 494626 * 2 ^ 59
def prefixEnd_494626 : Nat := 4983230072969 + 3 ^ 40 * 494626 * 2
def baseEnd_494626 : Nat := 253980882210887007200263

theorem tailTrace_494626 : CollatzResearch.WordTrace tailWord_494626 prefixEnd_494626 253980882210887007200263 := by
  unfold tailWord_494626
  simp only [CollatzResearch.WordTrace]
  refine ⟨4510123076515488060119933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12026994870707968160319821 4510123076515488060119933)
  ·
    refine ⟨1691296153693308022544975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4510123076515488060119933 1691296153693308022544975)
    ·
      refine ⟨2536944230539962033817463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1691296153693308022544975 2536944230539962033817463)
      ·
        refine ⟨3805416345809943050726195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2536944230539962033817463 3805416345809943050726195)
        ·
          refine ⟨5708124518714914576089293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3805416345809943050726195 5708124518714914576089293)
          ·
            refine ⟨2140546694518092966033485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5708124518714914576089293 2140546694518092966033485)
            ·
              refine ⟨802705010444284862262557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2140546694518092966033485 802705010444284862262557)
              ·
                refine ⟨301014378916606823348459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 802705010444284862262557 301014378916606823348459)
                ·
                  refine ⟨451521568374910235022689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 301014378916606823348459 451521568374910235022689)
                  ·
                    refine ⟨338641176281182676267017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 451521568374910235022689 338641176281182676267017)
                    ·
                      refine ⟨253980882210887007200263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 338641176281182676267017 253980882210887007200263)
                      ·
                        rfl

theorem cell23_494626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_494626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494626 prefixEnd_494626 := by exact prefixLift 494626
  have htrace : WordTrace (prefixWord ++ tailWord_494626) baseStart_494626 baseEnd_494626 := by
    simpa [prefixWord, tailWord_494626, baseEnd_494626] using wordTrace_append hprefix tailTrace_494626
  have hstable : (prefixWord ++ tailWord_494626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494626).length < 2 ^ (prefixWord ++ tailWord_494626).sum := by decide
  have hdescent : baseEnd_494626 < baseStart_494626 := by decide
  rcases family_descends (prefixWord ++ tailWord_494626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494642 : List Nat := [3, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3]
def baseStart_494642 : Nat := 118140960795 + 494642 * 2 ^ 59
def prefixEnd_494642 : Nat := 4983230072969 + 3 ^ 40 * 494642 * 2
def baseEnd_494642 : Nat := 253989097901358944600189

theorem tailTrace_494642 : CollatzResearch.WordTrace tailWord_494642 prefixEnd_494642 253989097901358944600189 := by
  unfold tailWord_494642
  simp only [CollatzResearch.WordTrace]
  refine ⟨4510268968500996743265545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12027383916002657982041453 4510268968500996743265545)
  ·
    refine ⟨3382701726375747557449159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4510268968500996743265545 3382701726375747557449159)
    ·
      refine ⟨5074052589563621336173739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3382701726375747557449159 5074052589563621336173739)
      ·
        refine ⟨7611078884345432004260609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5074052589563621336173739 7611078884345432004260609)
        ·
          refine ⟨5708309163259074003195457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7611078884345432004260609 5708309163259074003195457)
          ·
            refine ⟨4281231872444305502396593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5708309163259074003195457 4281231872444305502396593)
            ·
              refine ⟨3210923904333229126797445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4281231872444305502396593 3210923904333229126797445)
              ·
                refine ⟨602048232062480461274521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3210923904333229126797445 602048232062480461274521)
                ·
                  refine ⟨451536174046860345955891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 602048232062480461274521 451536174046860345955891)
                  ·
                    refine ⟨677304261070290518933837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 451536174046860345955891 677304261070290518933837)
                    ·
                      refine ⟨253989097901358944600189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 677304261070290518933837 253989097901358944600189)
                      ·
                        rfl

theorem cell23_494642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_494642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494642 prefixEnd_494642 := by exact prefixLift 494642
  have htrace : WordTrace (prefixWord ++ tailWord_494642) baseStart_494642 baseEnd_494642 := by
    simpa [prefixWord, tailWord_494642, baseEnd_494642] using wordTrace_append hprefix tailTrace_494642
  have hstable : (prefixWord ++ tailWord_494642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494642).length < 2 ^ (prefixWord ++ tailWord_494642).sum := by decide
  have hdescent : baseEnd_494642 < baseStart_494642 := by decide
  rcases family_descends (prefixWord ++ tailWord_494642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494669 : List Nat := [1, 6, 1, 1, 1, 3, 1, 1, 3, 3, 2]
def baseStart_494669 : Nat := 118140960795 + 494669 * 2 ^ 59
def prefixEnd_494669 : Nat := 4983230072969 + 3 ^ 40 * 494669 * 2
def baseEnd_494669 : Nat := 254002961879030338962565

theorem tailTrace_494669 : CollatzResearch.WordTrace tailWord_494669 prefixEnd_494669 254002961879030338962565 := by
  unfold tailWord_494669
  simp only [CollatzResearch.WordTrace]
  refine ⟨18042060644906170584295061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12028040429937447056196707 18042060644906170584295061)
  ·
    refine ⟨845721592729976746138831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18042060644906170584295061 845721592729976746138831)
    ·
      refine ⟨1268582389094965119208247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 845721592729976746138831 1268582389094965119208247)
      ·
        refine ⟨1902873583642447678812371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1268582389094965119208247 1902873583642447678812371)
        ·
          refine ⟨2854310375463671518218557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1902873583642447678812371 2854310375463671518218557)
          ·
            refine ⟨1070366390798876819331959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2854310375463671518218557 1070366390798876819331959)
            ·
              refine ⟨1605549586198315228997939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1070366390798876819331959 1605549586198315228997939)
              ·
                refine ⟨2408324379297472843496909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1605549586198315228997939 2408324379297472843496909)
                ·
                  refine ⟨903121642236552316311341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2408324379297472843496909 903121642236552316311341)
                  ·
                    refine ⟨338670615838707118616753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 903121642236552316311341 338670615838707118616753)
                    ·
                      refine ⟨254002961879030338962565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 338670615838707118616753 254002961879030338962565)
                      ·
                        rfl

theorem cell23_494669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_494669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494669 prefixEnd_494669 := by exact prefixLift 494669
  have htrace : WordTrace (prefixWord ++ tailWord_494669) baseStart_494669 baseEnd_494669 := by
    simpa [prefixWord, tailWord_494669, baseEnd_494669] using wordTrace_append hprefix tailTrace_494669
  have hstable : (prefixWord ++ tailWord_494669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494669).length < 2 ^ (prefixWord ++ tailWord_494669).sum := by decide
  have hdescent : baseEnd_494669 < baseStart_494669 := by decide
  rcases family_descends (prefixWord ++ tailWord_494669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494682 : List Nat := [3, 1, 1, 2, 1, 1, 2, 4, 4, 2, 2]
def baseStart_494682 : Nat := 118140960795 + 494682 * 2 ^ 59
def prefixEnd_494682 : Nat := 4983230072969 + 3 ^ 40 * 494682 * 2
def baseEnd_494682 : Nat := 254009637127538788100005

theorem tailTrace_494682 : CollatzResearch.WordTrace tailWord_494682 prefixEnd_494682 254009637127538788100005 := by
  unfold tailWord_494682
  simp only [CollatzResearch.WordTrace]
  refine ⟨4510633698464768451129575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12028356529239382536345533 4510633698464768451129575)
  ·
    refine ⟨6765950547697152676694363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4510633698464768451129575 6765950547697152676694363)
    ·
      refine ⟨10148925821545729015041545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6765950547697152676694363 10148925821545729015041545)
      ·
        refine ⟨7611694366159296761281159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10148925821545729015041545 7611694366159296761281159)
        ·
          refine ⟨11417541549238945141921739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7611694366159296761281159 11417541549238945141921739)
          ·
            refine ⟨17126312323858417712882609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11417541549238945141921739 17126312323858417712882609)
            ·
              refine ⟨12844734242893813284661957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17126312323858417712882609 12844734242893813284661957)
              ·
                refine ⟨2408387670542589990874117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12844734242893813284661957 2408387670542589990874117)
                ·
                  refine ⟨451572688226735623288897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2408387670542589990874117 451572688226735623288897)
                  ·
                    refine ⟨338679516170051717466673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 451572688226735623288897 338679516170051717466673)
                    ·
                      refine ⟨254009637127538788100005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 338679516170051717466673 254009637127538788100005)
                      ·
                        rfl

theorem cell23_494682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 4, 2, 2].length) (baseStart_494682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494682 prefixEnd_494682 := by exact prefixLift 494682
  have htrace : WordTrace (prefixWord ++ tailWord_494682) baseStart_494682 baseEnd_494682 := by
    simpa [prefixWord, tailWord_494682, baseEnd_494682] using wordTrace_append hprefix tailTrace_494682
  have hstable : (prefixWord ++ tailWord_494682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494682).length < 2 ^ (prefixWord ++ tailWord_494682).sum := by decide
  have hdescent : baseEnd_494682 < baseStart_494682 := by decide
  rcases family_descends (prefixWord ++ tailWord_494682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494755 : List Nat := [1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 4]
def baseStart_494755 : Nat := 118140960795 + 494755 * 2 ^ 59
def prefixEnd_494755 : Nat := 4983230072969 + 3 ^ 40 * 494755 * 2
def baseEnd_494755 : Nat := 254047121215317002487169

theorem tailTrace_494755 : CollatzResearch.WordTrace tailWord_494755 prefixEnd_494755 254047121215317002487169 := by
  unfold tailWord_494755
  simp only [CollatzResearch.WordTrace]
  refine ⟨18045197322594607271925719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12030131548396404847950479 18045197322594607271925719)
  ·
    refine ⟨27067795983891910907888579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18045197322594607271925719 27067795983891910907888579)
    ·
      refine ⟨40601693975837866361832869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27067795983891910907888579 40601693975837866361832869)
      ·
        refine ⟨7612817620469599942843663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40601693975837866361832869 7612817620469599942843663)
        ·
          refine ⟨11419226430704399914265495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7612817620469599942843663 11419226430704399914265495)
          ·
            refine ⟨17128839646056599871398243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11419226430704399914265495 17128839646056599871398243)
            ·
              refine ⟨25693259469084899807097365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17128839646056599871398243 25693259469084899807097365)
              ·
                refine ⟨1204371537613354678457689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25693259469084899807097365 1204371537613354678457689)
                ·
                  refine ⟨903278653210016008843267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1204371537613354678457689 903278653210016008843267)
                  ·
                    refine ⟨1354917979815024013264901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 903278653210016008843267 1354917979815024013264901)
                    ·
                      refine ⟨254047121215317002487169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1354917979815024013264901 254047121215317002487169)
                      ·
                        rfl

theorem cell23_494755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_494755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494755 prefixEnd_494755 := by exact prefixLift 494755
  have htrace : WordTrace (prefixWord ++ tailWord_494755) baseStart_494755 baseEnd_494755 := by
    simpa [prefixWord, tailWord_494755, baseEnd_494755] using wordTrace_append hprefix tailTrace_494755
  have hstable : (prefixWord ++ tailWord_494755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494755).length < 2 ^ (prefixWord ++ tailWord_494755).sum := by decide
  have hdescent : baseEnd_494755 < baseStart_494755 := by decide
  rcases family_descends (prefixWord ++ tailWord_494755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494775 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 3, 4, 3]
def baseStart_494775 : Nat := 118140960795 + 494775 * 2 ^ 59
def prefixEnd_494775 : Nat := 4983230072969 + 3 ^ 40 * 494775 * 2
def baseEnd_494775 : Nat := 254057390828406924237077

theorem tailTrace_494775 : CollatzResearch.WordTrace tailWord_494775 prefixEnd_494775 254057390828406924237077 := by
  unfold tailWord_494775
  simp only [CollatzResearch.WordTrace]
  refine ⟨18045926782522150687653779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12030617855014767125102519 18045926782522150687653779)
  ·
    refine ⟨27068890173783226031480669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18045926782522150687653779 27068890173783226031480669)
    ·
      refine ⟨10150833815168709761805251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27068890173783226031480669 10150833815168709761805251)
      ·
        refine ⟨15226250722753064642707877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10150833815168709761805251 15226250722753064642707877)
        ·
          refine ⟨2854922010516199620507727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15226250722753064642707877 2854922010516199620507727)
          ·
            refine ⟨4282383015774299430761591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2854922010516199620507727 4282383015774299430761591)
            ·
              refine ⟨6423574523661449146142387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4282383015774299430761591 6423574523661449146142387)
              ·
                refine ⟨9635361785492173719213581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6423574523661449146142387 9635361785492173719213581)
                ·
                  refine ⟨3613260669559565144705093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9635361785492173719213581 3613260669559565144705093)
                  ·
                    refine ⟨677486375542418464632205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3613260669559565144705093 677486375542418464632205)
                    ·
                      refine ⟨254057390828406924237077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 677486375542418464632205 254057390828406924237077)
                      ·
                        rfl

theorem cell23_494775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 4, 3].length) (baseStart_494775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494775 prefixEnd_494775 := by exact prefixLift 494775
  have htrace : WordTrace (prefixWord ++ tailWord_494775) baseStart_494775 baseEnd_494775 := by
    simpa [prefixWord, tailWord_494775, baseEnd_494775] using wordTrace_append hprefix tailTrace_494775
  have hstable : (prefixWord ++ tailWord_494775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494775).length < 2 ^ (prefixWord ++ tailWord_494775).sum := by decide
  have hdescent : baseEnd_494775 < baseStart_494775 := by decide
  rcases family_descends (prefixWord ++ tailWord_494775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494790 : List Nat := [6, 1, 2, 2, 1, 2, 1, 3, 5]
def baseStart_494790 : Nat := 118140960795 + 494790 * 2 ^ 59
def prefixEnd_494790 : Nat := 4983230072969 + 3 ^ 40 * 494790 * 2
def baseEnd_494790 : Nat := 28229454782024929505501

theorem tailTrace_494790 : CollatzResearch.WordTrace tailWord_494790 prefixEnd_494790 28229454782024929505501 := by
  unfold tailWord_494790
  simp only [CollatzResearch.WordTrace]
  refine ⟨563952308670869007795307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12030982584978538832966549 563952308670869007795307)
  ·
    refine ⟨845928463006303511692961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 563952308670869007795307 845928463006303511692961)
    ·
      refine ⟨634446347254727633769721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 845928463006303511692961 634446347254727633769721)
      ·
        refine ⟨475834760441045725327291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 634446347254727633769721 475834760441045725327291)
        ·
          refine ⟨713752140661568587990937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475834760441045725327291 713752140661568587990937)
          ·
            refine ⟨535314105496176440993203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 713752140661568587990937 535314105496176440993203)
            ·
              refine ⟨802971158244264661489805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535314105496176440993203 802971158244264661489805)
              ·
                refine ⟨301114184341599248058677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 802971158244264661489805 301114184341599248058677)
                ·
                  refine ⟨28229454782024929505501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 301114184341599248058677 28229454782024929505501)
                  ·
                    rfl

theorem cell23_494790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_494790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494790 prefixEnd_494790 := by exact prefixLift 494790
  have htrace : WordTrace (prefixWord ++ tailWord_494790) baseStart_494790 baseEnd_494790 := by
    simpa [prefixWord, tailWord_494790, baseEnd_494790] using wordTrace_append hprefix tailTrace_494790
  have hstable : (prefixWord ++ tailWord_494790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494790).length < 2 ^ (prefixWord ++ tailWord_494790).sum := by decide
  have hdescent : baseEnd_494790 < baseStart_494790 := by decide
  rcases family_descends (prefixWord ++ tailWord_494790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494806 : List Nat := [5, 2, 1, 2, 2, 1, 1, 2, 2, 1, 4]
def baseStart_494806 : Nat := 118140960795 + 494806 * 2 ^ 59
def prefixEnd_494806 : Nat := 4983230072969 + 3 ^ 40 * 494806 * 2
def baseEnd_494806 : Nat := 254073308728696302949435

theorem tailTrace_494806 : CollatzResearch.WordTrace tailWord_494806 prefixEnd_494806 254073308728696302949435 := by
  unfold tailWord_494806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1127941090338115186377017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12031371630273228654688181 1127941090338115186377017)
  ·
    refine ⟨845955817753586389782763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1127941090338115186377017 845955817753586389782763)
    ·
      refine ⟨1268933726630379584674145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 845955817753586389782763 1268933726630379584674145)
      ·
        refine ⟨951700294972784688505609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1268933726630379584674145 951700294972784688505609)
        ·
          refine ⟨713775221229588516379207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 951700294972784688505609 713775221229588516379207)
          ·
            refine ⟨1070662831844382774568811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713775221229588516379207 1070662831844382774568811)
            ·
              refine ⟨1605994247766574161853217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1070662831844382774568811 1605994247766574161853217)
              ·
                refine ⟨1204495685824930621389913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1605994247766574161853217 1204495685824930621389913)
                ·
                  refine ⟨903371764368697966042435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1204495685824930621389913 903371764368697966042435)
                  ·
                    refine ⟨1355057646553046949063653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 903371764368697966042435 1355057646553046949063653)
                    ·
                      refine ⟨254073308728696302949435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1355057646553046949063653 254073308728696302949435)
                      ·
                        rfl

theorem cell23_494806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_494806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494806 prefixEnd_494806 := by exact prefixLift 494806
  have htrace : WordTrace (prefixWord ++ tailWord_494806) baseStart_494806 baseEnd_494806 := by
    simpa [prefixWord, tailWord_494806, baseEnd_494806] using wordTrace_append hprefix tailTrace_494806
  have hstable : (prefixWord ++ tailWord_494806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494806).length < 2 ^ (prefixWord ++ tailWord_494806).sum := by decide
  have hdescent : baseEnd_494806 < baseStart_494806 := by decide
  rcases family_descends (prefixWord ++ tailWord_494806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494816 : List Nat := [2, 1, 1, 3, 1, 5, 3, 2, 1, 4]
def baseStart_494816 : Nat := 118140960795 + 494816 * 2 ^ 59
def prefixEnd_494816 : Nat := 4983230072969 + 3 ^ 40 * 494816 * 2
def baseEnd_494816 : Nat := 84692814511747087941463

theorem tailTrace_494816 : CollatzResearch.WordTrace tailWord_494816 prefixEnd_494816 84692814511747087941463 := by
  unfold tailWord_494816
  simp only [CollatzResearch.WordTrace]
  refine ⟨9023711087686807344948151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12031614783582409793264201 9023711087686807344948151)
  ·
    refine ⟨13535566631530211017422227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9023711087686807344948151 13535566631530211017422227)
    ·
      refine ⟨20303349947295316526133341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13535566631530211017422227 20303349947295316526133341)
      ·
        refine ⟨7613756230235743697300003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20303349947295316526133341 7613756230235743697300003)
        ·
          refine ⟨11420634345353615545950005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7613756230235743697300003 11420634345353615545950005)
          ·
            refine ⟨1070684469876901457432813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11420634345353615545950005 1070684469876901457432813)
            ·
              refine ⟨401506676203838046537305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1070684469876901457432813 401506676203838046537305)
              ·
                refine ⟨301130007152878534902979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401506676203838046537305 301130007152878534902979)
                ·
                  refine ⟨451695010729317802354469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 301130007152878534902979 451695010729317802354469)
                  ·
                    refine ⟨84692814511747087941463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 451695010729317802354469 84692814511747087941463)
                    ·
                      rfl

theorem cell23_494816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 2, 1, 4].length) (baseStart_494816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494816 prefixEnd_494816 := by exact prefixLift 494816
  have htrace : WordTrace (prefixWord ++ tailWord_494816) baseStart_494816 baseEnd_494816 := by
    simpa [prefixWord, tailWord_494816, baseEnd_494816] using wordTrace_append hprefix tailTrace_494816
  have hstable : (prefixWord ++ tailWord_494816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494816).length < 2 ^ (prefixWord ++ tailWord_494816).sum := by decide
  have hdescent : baseEnd_494816 < baseStart_494816 := by decide
  rcases family_descends (prefixWord ++ tailWord_494816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494829 : List Nat := [1, 5, 1, 2, 2, 1, 4, 1, 6]
def baseStart_494829 : Nat := 118140960795 + 494829 * 2 ^ 59
def prefixEnd_494829 : Nat := 4983230072969 + 3 ^ 40 * 494829 * 2
def baseEnd_494829 : Nat := 28231679864861079217981

theorem tailTrace_494829 : CollatzResearch.WordTrace tailWord_494829 prefixEnd_494829 28231679864861079217981 := by
  unfold tailWord_494829
  simp only [CollatzResearch.WordTrace]
  refine ⟨18047896324326517910119541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12031930882884345273413027 18047896324326517910119541)
  ·
    refine ⟨1691990280405611054073707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18047896324326517910119541 1691990280405611054073707)
    ·
      refine ⟨2537985420608416581110561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1691990280405611054073707 2537985420608416581110561)
      ·
        refine ⟨1903489065456312435832921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2537985420608416581110561 1903489065456312435832921)
        ·
          refine ⟨1427616799092234326874691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1903489065456312435832921 1427616799092234326874691)
          ·
            refine ⟨2141425198638351490312037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1427616799092234326874691 2141425198638351490312037)
            ·
              refine ⟨401517224744690904433507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2141425198638351490312037 401517224744690904433507)
              ·
                refine ⟨602275837117036356650261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401517224744690904433507 602275837117036356650261)
                ·
                  refine ⟨28231679864861079217981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 602275837117036356650261 28231679864861079217981)
                  ·
                    rfl

theorem cell23_494829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_494829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494829 prefixEnd_494829 := by exact prefixLift 494829
  have htrace : WordTrace (prefixWord ++ tailWord_494829) baseStart_494829 baseEnd_494829 := by
    simpa [prefixWord, tailWord_494829, baseEnd_494829] using wordTrace_append hprefix tailTrace_494829
  have hstable : (prefixWord ++ tailWord_494829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494829).length < 2 ^ (prefixWord ++ tailWord_494829).sum := by decide
  have hdescent : baseEnd_494829 < baseStart_494829 := by decide
  rcases family_descends (prefixWord ++ tailWord_494829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494849 : List Nat := [1, 2, 4, 1, 1, 3, 1, 3, 2, 3, 2]
def baseStart_494849 : Nat := 118140960795 + 494849 * 2 ^ 59
def prefixEnd_494849 : Nat := 4983230072969 + 3 ^ 40 * 494849 * 2
def baseEnd_494849 : Nat := 254095388396839634711737

theorem tailTrace_494849 : CollatzResearch.WordTrace tailWord_494849 prefixEnd_494849 254095388396839634711737 := by
  unfold tailWord_494849
  simp only [CollatzResearch.WordTrace]
  refine ⟨18048625784254061325847601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12032417189502707550565067 18048625784254061325847601)
  ·
    refine ⟨13536469338190545994385701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18048625784254061325847601 13536469338190545994385701)
    ·
      refine ⟨2538088000910727373947319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13536469338190545994385701 2538088000910727373947319)
      ·
        refine ⟨3807132001366091060920979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2538088000910727373947319 3807132001366091060920979)
        ·
          refine ⟨5710698002049136591381469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3807132001366091060920979 5710698002049136591381469)
          ·
            refine ⟨2141511750768426221768051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5710698002049136591381469 2141511750768426221768051)
            ·
              refine ⟨3212267626152639332652077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2141511750768426221768051 3212267626152639332652077)
              ·
                refine ⟨1204600359807239749744529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3212267626152639332652077 1204600359807239749744529)
                ·
                  refine ⟨903450269855429812308397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1204600359807239749744529 903450269855429812308397)
                  ·
                    refine ⟨338793851195786179615649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 903450269855429812308397 338793851195786179615649)
                    ·
                      refine ⟨254095388396839634711737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 338793851195786179615649 254095388396839634711737)
                      ·
                        rfl

theorem cell23_494849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_494849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494849 prefixEnd_494849 := by exact prefixLift 494849
  have htrace : WordTrace (prefixWord ++ tailWord_494849) baseStart_494849 baseEnd_494849 := by
    simpa [prefixWord, tailWord_494849, baseEnd_494849] using wordTrace_append hprefix tailTrace_494849
  have hstable : (prefixWord ++ tailWord_494849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494849).length < 2 ^ (prefixWord ++ tailWord_494849).sum := by decide
  have hdescent : baseEnd_494849 < baseStart_494849 := by decide
  rcases family_descends (prefixWord ++ tailWord_494849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494859 : List Nat := [1, 1, 1, 1, 5, 4, 3, 1, 1, 5]
def baseStart_494859 : Nat := 118140960795 + 494859 * 2 ^ 59
def prefixEnd_494859 : Nat := 4983230072969 + 3 ^ 40 * 494859 * 2
def baseEnd_494859 : Nat := 84700174401128198528897

theorem tailTrace_494859 : CollatzResearch.WordTrace tailWord_494859 prefixEnd_494859 84700174401128198528897 := by
  unfold tailWord_494859
  simp only [CollatzResearch.WordTrace]
  refine ⟨18048990514217833033711631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12032660342811888689141087 18048990514217833033711631)
  ·
    refine ⟨27073485771326749550567447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18048990514217833033711631 27073485771326749550567447)
    ·
      refine ⟨40610228656990124325851171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27073485771326749550567447 40610228656990124325851171)
      ·
        refine ⟨60915342985485186488776757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40610228656990124325851171 60915342985485186488776757)
        ·
          refine ⟨5710813404889236233322821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60915342985485186488776757 5710813404889236233322821)
          ·
            refine ⟨1070777513416731793748029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5710813404889236233322821 1070777513416731793748029)
            ·
              refine ⟨401541567531274422655511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1070777513416731793748029 401541567531274422655511)
              ·
                refine ⟨602312351296911633983267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401541567531274422655511 602312351296911633983267)
                ·
                  refine ⟨903468526945367450974901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 602312351296911633983267 903468526945367450974901)
                  ·
                    refine ⟨84700174401128198528897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 903468526945367450974901 84700174401128198528897)
                    ·
                      rfl

theorem cell23_494859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 1, 5].length) (baseStart_494859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494859 prefixEnd_494859 := by exact prefixLift 494859
  have htrace : WordTrace (prefixWord ++ tailWord_494859) baseStart_494859 baseEnd_494859 := by
    simpa [prefixWord, tailWord_494859, baseEnd_494859] using wordTrace_append hprefix tailTrace_494859
  have hstable : (prefixWord ++ tailWord_494859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494859).length < 2 ^ (prefixWord ++ tailWord_494859).sum := by decide
  have hdescent : baseEnd_494859 < baseStart_494859 := by decide
  rcases family_descends (prefixWord ++ tailWord_494859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494875 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 4]
def baseStart_494875 : Nat := 118140960795 + 494875 * 2 ^ 59
def prefixEnd_494875 : Nat := 4983230072969 + 3 ^ 40 * 494875 * 2
def baseEnd_494875 : Nat := 254108738893856532986617

theorem tailTrace_494875 : CollatzResearch.WordTrace tailWord_494875 prefixEnd_494875 254108738893856532986617 := by
  unfold tailWord_494875
  simp only [CollatzResearch.WordTrace]
  refine ⟨18049574082159867766294079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12033049388106578510862719 18049574082159867766294079)
  ·
    refine ⟨27074361123239801649441119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18049574082159867766294079 27074361123239801649441119)
    ·
      refine ⟨40611541684859702474161679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27074361123239801649441119 40611541684859702474161679)
      ·
        refine ⟨60917312527289553711242519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40611541684859702474161679 60917312527289553711242519)
        ·
          refine ⟨91375968790934330566863779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60917312527289553711242519 91375968790934330566863779)
          ·
            refine ⟨137063953186401495850295669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91375968790934330566863779 137063953186401495850295669)
            ·
              refine ⟨12849745611225140235965219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137063953186401495850295669 12849745611225140235965219)
              ·
                refine ⟨19274618416837710353947829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12849745611225140235965219 19274618416837710353947829)
                ·
                  refine ⟨1806995476578535345682609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19274618416837710353947829 1806995476578535345682609)
                  ·
                    refine ⟨1355246607433901509261957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1806995476578535345682609 1355246607433901509261957)
                    ·
                      refine ⟨254108738893856532986617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1355246607433901509261957 254108738893856532986617)
                      ·
                        rfl

theorem cell23_494875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 4].length) (baseStart_494875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494875 prefixEnd_494875 := by exact prefixLift 494875
  have htrace : WordTrace (prefixWord ++ tailWord_494875) baseStart_494875 baseEnd_494875 := by
    simpa [prefixWord, tailWord_494875, baseEnd_494875] using wordTrace_append hprefix tailTrace_494875
  have hstable : (prefixWord ++ tailWord_494875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494875).length < 2 ^ (prefixWord ++ tailWord_494875).sum := by decide
  have hdescent : baseEnd_494875 < baseStart_494875 := by decide
  rcases family_descends (prefixWord ++ tailWord_494875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494912 : List Nat := [2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 3]
def baseStart_494912 : Nat := 118140960795 + 494912 * 2 ^ 59
def prefixEnd_494912 : Nat := 4983230072969 + 3 ^ 40 * 494912 * 2
def baseEnd_494912 : Nat := 254127737678072888223947

theorem tailTrace_494912 : CollatzResearch.WordTrace tailWord_494912 prefixEnd_494912 254127737678072888223947 := by
  unfold tailWord_494912
  simp only [CollatzResearch.WordTrace]
  refine ⟨9025461791512911542695495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12033949055350548723593993 9025461791512911542695495)
  ·
    refine ⟨13538192687269367314043243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9025461791512911542695495 13538192687269367314043243)
    ·
      refine ⟨20307289030904050971064865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13538192687269367314043243 20307289030904050971064865)
      ·
        refine ⟨15230466773178038228298649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20307289030904050971064865 15230466773178038228298649)
        ·
          refine ⟨11422850079883528671223987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15230466773178038228298649 11422850079883528671223987)
          ·
            refine ⟨17134275119825293006835981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11422850079883528671223987 17134275119825293006835981)
            ·
              refine ⟨6425353169934484877563493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17134275119825293006835981 6425353169934484877563493)
              ·
                refine ⟨1204753719362715914543155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6425353169934484877563493 1204753719362715914543155)
                ·
                  refine ⟨1807130579044073871814733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1204753719362715914543155 1807130579044073871814733)
                  ·
                    refine ⟨677673967141527701930525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1807130579044073871814733 677673967141527701930525)
                    ·
                      refine ⟨254127737678072888223947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 677673967141527701930525 254127737678072888223947)
                      ·
                        rfl

theorem cell23_494912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 1, 3, 3].length) (baseStart_494912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494912 prefixEnd_494912 := by exact prefixLift 494912
  have htrace : WordTrace (prefixWord ++ tailWord_494912) baseStart_494912 baseEnd_494912 := by
    simpa [prefixWord, tailWord_494912, baseEnd_494912] using wordTrace_append hprefix tailTrace_494912
  have hstable : (prefixWord ++ tailWord_494912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494912).length < 2 ^ (prefixWord ++ tailWord_494912).sum := by decide
  have hdescent : baseEnd_494912 < baseStart_494912 := by decide
  rcases family_descends (prefixWord ++ tailWord_494912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494913 : List Nat := [1, 2, 5, 2, 1, 3, 2, 1, 1, 1, 4]
def baseStart_494913 : Nat := 118140960795 + 494913 * 2 ^ 59
def prefixEnd_494913 : Nat := 4983230072969 + 3 ^ 40 * 494913 * 2
def baseEnd_494913 : Nat := 254128251158727384311443

theorem tailTrace_494913 : CollatzResearch.WordTrace tailWord_494913 prefixEnd_494913 254128251158727384311443 := by
  unfold tailWord_494913
  simp only [CollatzResearch.WordTrace]
  refine ⟨18050960056022200256177393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12033973370681466837451595 18050960056022200256177393)
  ·
    refine ⟨13538220042016650192133045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18050960056022200256177393 13538220042016650192133045)
    ·
      refine ⟨1269208128939060955512473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13538220042016650192133045 1269208128939060955512473)
      ·
        refine ⟨951906096704295716634355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1269208128939060955512473 951906096704295716634355)
        ·
          refine ⟨1427859145056443574951533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 951906096704295716634355 1427859145056443574951533)
          ·
            refine ⟨535447179396166340606825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1427859145056443574951533 535447179396166340606825)
            ·
              refine ⟨401585384547124755455119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 535447179396166340606825 401585384547124755455119)
              ·
                refine ⟨602378076820687133182679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401585384547124755455119 602378076820687133182679)
                ·
                  refine ⟨903567115231030699774019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 602378076820687133182679 903567115231030699774019)
                  ·
                    refine ⟨1355350672846546049661029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 903567115231030699774019 1355350672846546049661029)
                    ·
                      refine ⟨254128251158727384311443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1355350672846546049661029 254128251158727384311443)
                      ·
                        rfl

theorem cell23_494913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_494913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494913 prefixEnd_494913 := by exact prefixLift 494913
  have htrace : WordTrace (prefixWord ++ tailWord_494913) baseStart_494913 baseEnd_494913 := by
    simpa [prefixWord, tailWord_494913, baseEnd_494913] using wordTrace_append hprefix tailTrace_494913
  have hstable : (prefixWord ++ tailWord_494913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494913).length < 2 ^ (prefixWord ++ tailWord_494913).sum := by decide
  have hdescent : baseEnd_494913 < baseStart_494913 := by decide
  rcases family_descends (prefixWord ++ tailWord_494913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494929 : List Nat := [1, 2, 2, 1, 4, 1, 3, 1, 4, 1, 3]
def baseStart_494929 : Nat := 118140960795 + 494929 * 2 ^ 59
def prefixEnd_494929 : Nat := 4983230072969 + 3 ^ 40 * 494929 * 2
def baseEnd_494929 : Nat := 254136466849199321711369

theorem tailTrace_494929 : CollatzResearch.WordTrace tailWord_494929 prefixEnd_494929 254136466849199321711369 := by
  unfold tailWord_494929
  simp only [CollatzResearch.WordTrace]
  refine ⟨18051543623964234988759841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12034362415976156659173227 18051543623964234988759841)
  ·
    refine ⟨13538657717973176241569881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18051543623964234988759841 13538657717973176241569881)
    ·
      refine ⟨10153993288479882181177411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13538657717973176241569881 10153993288479882181177411)
      ·
        refine ⟨15230989932719823271766117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10153993288479882181177411 15230989932719823271766117)
        ·
          refine ⟨2855810612384966863456147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15230989932719823271766117 2855810612384966863456147)
          ·
            refine ⟨4283715918577450295184221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2855810612384966863456147 4283715918577450295184221)
            ·
              refine ⟨1606393469466543860694083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4283715918577450295184221 1606393469466543860694083)
              ·
                refine ⟨2409590204199815791041125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1606393469466543860694083 2409590204199815791041125)
                ·
                  refine ⟨451798163287465460820211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2409590204199815791041125 451798163287465460820211)
                  ·
                    refine ⟨677697244931198191230317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 451798163287465460820211 677697244931198191230317)
                    ·
                      refine ⟨254136466849199321711369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 677697244931198191230317 254136466849199321711369)
                      ·
                        rfl

theorem cell23_494929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 4, 1, 3].length) (baseStart_494929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494929 prefixEnd_494929 := by exact prefixLift 494929
  have htrace : WordTrace (prefixWord ++ tailWord_494929) baseStart_494929 baseEnd_494929 := by
    simpa [prefixWord, tailWord_494929, baseEnd_494929] using wordTrace_append hprefix tailTrace_494929
  have hstable : (prefixWord ++ tailWord_494929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494929).length < 2 ^ (prefixWord ++ tailWord_494929).sum := by decide
  have hdescent : baseEnd_494929 < baseStart_494929 := by decide
  rcases family_descends (prefixWord ++ tailWord_494929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494956 : List Nat := [2, 2, 1, 1, 5, 1, 1, 4, 1, 3, 2]
def baseStart_494956 : Nat := 118140960795 + 494956 * 2 ^ 59
def prefixEnd_494956 : Nat := 4983230072969 + 3 ^ 40 * 494956 * 2
def baseEnd_494956 : Nat := 254150330826870716073745

theorem tailTrace_494956 : CollatzResearch.WordTrace tailWord_494956 prefixEnd_494956 254150330826870716073745 := by
  unfold tailWord_494956
  simp only [CollatzResearch.WordTrace]
  refine ⟨9026264197433209299996361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12035018929910945733328481 9026264197433209299996361)
  ·
    refine ⟨6769698148074906974997271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9026264197433209299996361 6769698148074906974997271)
    ·
      refine ⟨10154547222112360462495907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6769698148074906974997271 10154547222112360462495907)
      ·
        refine ⟨15231820833168540693743861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10154547222112360462495907 15231820833168540693743861)
        ·
          refine ⟨1427983203109550690038487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15231820833168540693743861 1427983203109550690038487)
          ·
            refine ⟨2141974804664326035057731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1427983203109550690038487 2141974804664326035057731)
            ·
              refine ⟨3212962206996489052586597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2141974804664326035057731 3212962206996489052586597)
              ·
                refine ⟨602430413811841697359987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3212962206996489052586597 602430413811841697359987)
                ·
                  refine ⟨903645620717762546039981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 602430413811841697359987 903645620717762546039981)
                  ·
                    refine ⟨338867107769160954764993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 903645620717762546039981 338867107769160954764993)
                    ·
                      refine ⟨254150330826870716073745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 338867107769160954764993 254150330826870716073745)
                      ·
                        rfl

theorem cell23_494956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 3, 2].length) (baseStart_494956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494956 prefixEnd_494956 := by exact prefixLift 494956
  have htrace : WordTrace (prefixWord ++ tailWord_494956) baseStart_494956 baseEnd_494956 := by
    simpa [prefixWord, tailWord_494956, baseEnd_494956] using wordTrace_append hprefix tailTrace_494956
  have hstable : (prefixWord ++ tailWord_494956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494956).length < 2 ^ (prefixWord ++ tailWord_494956).sum := by decide
  have hdescent : baseEnd_494956 < baseStart_494956 := by decide
  rcases family_descends (prefixWord ++ tailWord_494956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494969 : List Nat := [1, 2, 1, 3, 2, 1, 2, 4, 1, 4, 2]
def baseStart_494969 : Nat := 118140960795 + 494969 * 2 ^ 59
def prefixEnd_494969 : Nat := 4983230072969 + 3 ^ 40 * 494969 * 2
def baseEnd_494969 : Nat := 254157006075379165211185

theorem tailTrace_494969 : CollatzResearch.WordTrace tailWord_494969 prefixEnd_494969 254157006075379165211185 := by
  unfold tailWord_494969
  simp only [CollatzResearch.WordTrace]
  refine ⟨18053002543819321820215961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12035335029212881213477307 18053002543819321820215961)
  ·
    refine ⟨13539751907864491365161971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18053002543819321820215961 13539751907864491365161971)
    ·
      refine ⟨20309627861796737047742957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13539751907864491365161971 20309627861796737047742957)
      ·
        refine ⟨7616110448173776392903609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20309627861796737047742957 7616110448173776392903609)
        ·
          refine ⟨5712082836130332294677707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7616110448173776392903609 5712082836130332294677707)
          ·
            refine ⟨8568124254195498442016561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5712082836130332294677707 8568124254195498442016561)
            ·
              refine ⟨6426093190646623831512421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8568124254195498442016561 6426093190646623831512421)
              ·
                refine ⟨1204892473246241968408579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6426093190646623831512421 1204892473246241968408579)
                ·
                  refine ⟨1807338709869362952612869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1204892473246241968408579 1807338709869362952612869)
                  ·
                    refine ⟨338876008100505553614913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1807338709869362952612869 338876008100505553614913)
                    ·
                      refine ⟨254157006075379165211185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 338876008100505553614913 254157006075379165211185)
                      ·
                        rfl

theorem cell23_494969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 4, 2].length) (baseStart_494969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494969 prefixEnd_494969 := by exact prefixLift 494969
  have htrace : WordTrace (prefixWord ++ tailWord_494969) baseStart_494969 baseEnd_494969 := by
    simpa [prefixWord, tailWord_494969, baseEnd_494969] using wordTrace_append hprefix tailTrace_494969
  have hstable : (prefixWord ++ tailWord_494969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494969).length < 2 ^ (prefixWord ++ tailWord_494969).sum := by decide
  have hdescent : baseEnd_494969 < baseStart_494969 := by decide
  rcases family_descends (prefixWord ++ tailWord_494969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494972 : List Nat := [2, 2, 2, 1, 1, 1, 5, 1, 2, 1, 5]
def baseStart_494972 : Nat := 118140960795 + 494972 * 2 ^ 59
def prefixEnd_494972 : Nat := 4983230072969 + 3 ^ 40 * 494972 * 2
def baseEnd_494972 : Nat := 254158546517342653473671

theorem tailTrace_494972 : CollatzResearch.WordTrace tailWord_494972 prefixEnd_494972 254158546517342653473671 := by
  unfold tailWord_494972
  simp only [CollatzResearch.WordTrace]
  refine ⟨9026555981404226666287585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12035407975205635555050113 9026555981404226666287585)
  ·
    refine ⟨6769916986053169999715689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9026555981404226666287585 6769916986053169999715689)
    ·
      refine ⟨5077437739539877499786767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6769916986053169999715689 5077437739539877499786767)
      ·
        refine ⟨7616156609309816249680151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5077437739539877499786767 7616156609309816249680151)
        ·
          refine ⟨11424234913964724374520227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7616156609309816249680151 11424234913964724374520227)
          ·
            refine ⟨17136352370947086561780341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11424234913964724374520227 17136352370947086561780341)
            ·
              refine ⟨1606533034776289365166907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17136352370947086561780341 1606533034776289365166907)
              ·
                refine ⟨2409799552164434047750361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1606533034776289365166907 2409799552164434047750361)
                ·
                  refine ⟨1807349664123325535812771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2409799552164434047750361 1807349664123325535812771)
                  ·
                    refine ⟨2711024496184988303719157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1807349664123325535812771 2711024496184988303719157)
                    ·
                      refine ⟨254158546517342653473671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2711024496184988303719157 254158546517342653473671)
                      ·
                        rfl

theorem cell23_494972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_494972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_494972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_494972 prefixEnd_494972 := by exact prefixLift 494972
  have htrace : WordTrace (prefixWord ++ tailWord_494972) baseStart_494972 baseEnd_494972 := by
    simpa [prefixWord, tailWord_494972, baseEnd_494972] using wordTrace_append hprefix tailTrace_494972
  have hstable : (prefixWord ++ tailWord_494972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494972).length < 2 ^ (prefixWord ++ tailWord_494972).sum := by decide
  have hdescent : baseEnd_494972 < baseStart_494972 := by decide
  rcases family_descends (prefixWord ++ tailWord_494972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495032 : List Nat := [2, 1, 2, 1, 2, 2, 3, 2, 1, 2, 5]
def baseStart_495032 : Nat := 118140960795 + 495032 * 2 ^ 59
def prefixEnd_495032 : Nat := 4983230072969 + 3 ^ 40 * 495032 * 2
def baseEnd_495032 : Nat := 254189355356612418723395

theorem tailTrace_495032 : CollatzResearch.WordTrace tailWord_495032 prefixEnd_495032 254189355356612418723395 := by
  unfold tailWord_495032
  simp only [CollatzResearch.WordTrace]
  refine ⟨9027650171295541789879675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12036866895060722386506233 9027650171295541789879675)
  ·
    refine ⟨13541475256943312684819513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9027650171295541789879675 13541475256943312684819513)
    ·
      refine ⟨10156106442707484513614635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13541475256943312684819513 10156106442707484513614635)
      ·
        refine ⟨15234159664061226770421953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10156106442707484513614635 15234159664061226770421953)
        ·
          refine ⟨11425619748045920077816465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15234159664061226770421953 11425619748045920077816465)
          ·
            refine ⟨8569214811034440058362349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11425619748045920077816465 8569214811034440058362349)
            ·
              refine ⟨3213455554137915021885881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8569214811034440058362349 3213455554137915021885881)
              ·
                refine ⟨2410091665603436266414411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3213455554137915021885881 2410091665603436266414411)
                ·
                  refine ⟨3615137498405154399621617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2410091665603436266414411 3615137498405154399621617)
                  ·
                    refine ⟨2711353123803865799716213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3615137498405154399621617 2711353123803865799716213)
                    ·
                      refine ⟨254189355356612418723395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2711353123803865799716213 254189355356612418723395)
                      ·
                        rfl

theorem cell23_495032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_495032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495032 prefixEnd_495032 := by exact prefixLift 495032
  have htrace : WordTrace (prefixWord ++ tailWord_495032) baseStart_495032 baseEnd_495032 := by
    simpa [prefixWord, tailWord_495032, baseEnd_495032] using wordTrace_append hprefix tailTrace_495032
  have hstable : (prefixWord ++ tailWord_495032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495032).length < 2 ^ (prefixWord ++ tailWord_495032).sum := by decide
  have hdescent : baseEnd_495032 < baseStart_495032 := by decide
  rcases family_descends (prefixWord ++ tailWord_495032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495072 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 4]
def baseStart_495072 : Nat := 118140960795 + 495072 * 2 ^ 59
def prefixEnd_495072 : Nat := 4983230072969 + 3 ^ 40 * 495072 * 2
def baseEnd_495072 : Nat := 254209894582792262223211

theorem tailTrace_495072 : CollatzResearch.WordTrace tailWord_495072 prefixEnd_495072 254209894582792262223211 := by
  unfold tailWord_495072
  simp only [CollatzResearch.WordTrace]
  refine ⟨9028379631223085205607735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12037839508297446940810313 9028379631223085205607735)
  ·
    refine ⟨13542569446834627808411603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9028379631223085205607735 13542569446834627808411603)
    ·
      refine ⟨20313854170251941712617405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13542569446834627808411603 20313854170251941712617405)
      ·
        refine ⟨7617695313844478142231527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20313854170251941712617405 7617695313844478142231527)
        ·
          refine ⟨11426542970766717213347291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7617695313844478142231527 11426542970766717213347291)
          ·
            refine ⟨17139814456150075820020937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11426542970766717213347291 17139814456150075820020937)
            ·
              refine ⟨12854860842112556865015703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17139814456150075820020937 12854860842112556865015703)
              ·
                refine ⟨19282291263168835297523555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12854860842112556865015703 19282291263168835297523555)
                ·
                  refine ⟨28923436894753252946285333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19282291263168835297523555 28923436894753252946285333)
                  ·
                    refine ⟨1355786104441558731857125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28923436894753252946285333 1355786104441558731857125)
                    ·
                      refine ⟨254209894582792262223211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1355786104441558731857125 254209894582792262223211)
                      ·
                        rfl

theorem cell23_495072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_495072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495072 prefixEnd_495072 := by exact prefixLift 495072
  have htrace : WordTrace (prefixWord ++ tailWord_495072) baseStart_495072 baseEnd_495072 := by
    simpa [prefixWord, tailWord_495072, baseEnd_495072] using wordTrace_append hprefix tailTrace_495072
  have hstable : (prefixWord ++ tailWord_495072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495072).length < 2 ^ (prefixWord ++ tailWord_495072).sum := by decide
  have hdescent : baseEnd_495072 < baseStart_495072 := by decide
  rcases family_descends (prefixWord ++ tailWord_495072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495093 : List Nat := [1, 3, 5, 1, 1, 1, 1, 2, 2, 4, 2]
def baseStart_495093 : Nat := 118140960795 + 495093 * 2 ^ 59
def prefixEnd_495093 : Nat := 4983230072969 + 3 ^ 40 * 495093 * 2
def baseEnd_495093 : Nat := 254220677676536680060615

theorem tailTrace_495093 : CollatzResearch.WordTrace tailWord_495093 prefixEnd_495093 254220677676536680060615 := by
  unfold tailWord_495093
  simp only [CollatzResearch.WordTrace]
  refine ⟨18057525195370090997729933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12038350130246727331819955 18057525195370090997729933)
  ·
    refine ⟨6771571948263784124148725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18057525195370090997729933 6771571948263784124148725)
    ·
      refine ⟨634834870149729761638943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6771571948263784124148725 634834870149729761638943)
      ·
        refine ⟨952252305224594642458415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634834870149729761638943 952252305224594642458415)
        ·
          refine ⟨1428378457836891963687623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 952252305224594642458415 1428378457836891963687623)
          ·
            refine ⟨2142567686755337945531435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1428378457836891963687623 2142567686755337945531435)
            ·
              refine ⟨3213851530133006918297153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2142567686755337945531435 3213851530133006918297153)
              ·
                refine ⟨2410388647599755188722865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3213851530133006918297153 2410388647599755188722865)
                ·
                  refine ⟨1807791485699816391542149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2410388647599755188722865 1807791485699816391542149)
                  ·
                    refine ⟨338960903568715573414153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1807791485699816391542149 338960903568715573414153)
                    ·
                      refine ⟨254220677676536680060615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 338960903568715573414153 254220677676536680060615)
                      ·
                        rfl

theorem cell23_495093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_495093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495093 prefixEnd_495093 := by exact prefixLift 495093
  have htrace : WordTrace (prefixWord ++ tailWord_495093) baseStart_495093 baseEnd_495093 := by
    simpa [prefixWord, tailWord_495093, baseEnd_495093] using wordTrace_append hprefix tailTrace_495093
  have hstable : (prefixWord ++ tailWord_495093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495093).length < 2 ^ (prefixWord ++ tailWord_495093).sum := by decide
  have hdescent : baseEnd_495093 < baseStart_495093 := by decide
  rcases family_descends (prefixWord ++ tailWord_495093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495146 : List Nat := [3, 1, 4, 1, 1, 1, 1, 5, 1, 5]
def baseStart_495146 : Nat := 118140960795 + 495146 * 2 ^ 59
def prefixEnd_495146 : Nat := 4983230072969 + 3 ^ 40 * 495146 * 2
def baseEnd_495146 : Nat := 84749297383741657565957

theorem tailTrace_495146 : CollatzResearch.WordTrace tailWord_495146 prefixEnd_495146 84749297383741657565957 := by
  unfold tailWord_495146
  simp only [CollatzResearch.WordTrace]
  refine ⟨4514864566044520262352323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12039638842785387366272861 4514864566044520262352323)
  ·
    refine ⟨6772296849066780393528485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4514864566044520262352323 6772296849066780393528485)
    ·
      refine ⟨1269805659200021323786591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6772296849066780393528485 1269805659200021323786591)
      ·
        refine ⟨1904708488800031985679887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1269805659200021323786591 1904708488800031985679887)
        ·
          refine ⟨2857062733200047978519831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1904708488800031985679887 2857062733200047978519831)
          ·
            refine ⟨4285594099800071967779747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2857062733200047978519831 4285594099800071967779747)
            ·
              refine ⟨6428391149700107951669621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4285594099800071967779747 6428391149700107951669621)
              ·
                refine ⟨602661670284385120469027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6428391149700107951669621 602661670284385120469027)
                ·
                  refine ⟨903992505426577680703541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 602661670284385120469027 903992505426577680703541)
                  ·
                    refine ⟨84749297383741657565957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 903992505426577680703541 84749297383741657565957)
                    ·
                      rfl

theorem cell23_495146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_495146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495146 prefixEnd_495146 := by exact prefixLift 495146
  have htrace : WordTrace (prefixWord ++ tailWord_495146) baseStart_495146 baseEnd_495146 := by
    simpa [prefixWord, tailWord_495146, baseEnd_495146] using wordTrace_append hprefix tailTrace_495146
  have hstable : (prefixWord ++ tailWord_495146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495146).length < 2 ^ (prefixWord ++ tailWord_495146).sum := by decide
  have hdescent : baseEnd_495146 < baseStart_495146 := by decide
  rcases family_descends (prefixWord ++ tailWord_495146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495179 : List Nat := [1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 4]
def baseStart_495179 : Nat := 118140960795 + 495179 * 2 ^ 59
def prefixEnd_495179 : Nat := 4983230072969 + 3 ^ 40 * 495179 * 2
def baseEnd_495179 : Nat := 254264837012823343585219

theorem tailTrace_495179 : CollatzResearch.WordTrace tailWord_495179 prefixEnd_495179 254264837012823343585219 := by
  unfold tailWord_495179
  simp only [CollatzResearch.WordTrace]
  refine ⟨18060661873058527685360591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12040441248705685123573727 18060661873058527685360591)
  ·
    refine ⟨27090992809587791528040887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18060661873058527685360591 27090992809587791528040887)
    ·
      refine ⟨40636489214381687292061331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27090992809587791528040887 40636489214381687292061331)
      ·
        refine ⟨60954733821572530938091997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40636489214381687292061331 60954733821572530938091997)
        ·
          refine ⟨22858025183089699101784499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60954733821572530938091997 22858025183089699101784499)
          ·
            refine ⟨34287037774634548652676749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22858025183089699101784499 34287037774634548652676749)
            ·
              refine ⟨12857639165487955744753781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34287037774634548652676749 12857639165487955744753781)
              ·
                refine ⟨1205403671764495851070667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12857639165487955744753781 1205403671764495851070667)
                ·
                  refine ⟨1808105507646743776606001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1205403671764495851070667 1808105507646743776606001)
                  ·
                    refine ⟨1356079130735057832454501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1808105507646743776606001 1356079130735057832454501)
                    ·
                      refine ⟨254264837012823343585219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1356079130735057832454501 254264837012823343585219)
                      ·
                        rfl

theorem cell23_495179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 4].length) (baseStart_495179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495179 prefixEnd_495179 := by exact prefixLift 495179
  have htrace : WordTrace (prefixWord ++ tailWord_495179) baseStart_495179 baseEnd_495179 := by
    simpa [prefixWord, tailWord_495179, baseEnd_495179] using wordTrace_append hprefix tailTrace_495179
  have hstable : (prefixWord ++ tailWord_495179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495179).length < 2 ^ (prefixWord ++ tailWord_495179).sum := by decide
  have hdescent : baseEnd_495179 < baseStart_495179 := by decide
  rcases family_descends (prefixWord ++ tailWord_495179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495196 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_495196 : Nat := 118140960795 + 495196 * 2 ^ 59
def prefixEnd_495196 : Nat := 4983230072969 + 3 ^ 40 * 495196 * 2
def baseEnd_495196 : Nat := 254273566183949777072641

theorem tailTrace_495196 : CollatzResearch.WordTrace tailWord_495196 prefixEnd_495196 254273566183949777072641 := by
  unfold tailWord_495196
  simp only [CollatzResearch.WordTrace]
  refine ⟨9030640956998469794364721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12040854609331293059152961 9030640956998469794364721)
  ·
    refine ⟨6772980717748852345773541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9030640956998469794364721 6772980717748852345773541)
    ·
      refine ⟨1269933884577909814832539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6772980717748852345773541 1269933884577909814832539)
      ·
        refine ⟨1904900826866864722248809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1269933884577909814832539 1904900826866864722248809)
        ·
          refine ⟨1428675620150148541686607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1904900826866864722248809 1428675620150148541686607)
          ·
            refine ⟨2143013430225222812529911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1428675620150148541686607 2143013430225222812529911)
            ·
              refine ⟨3214520145337834218794867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2143013430225222812529911 3214520145337834218794867)
              ·
                refine ⟨4821780218006751328192301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3214520145337834218794867 4821780218006751328192301)
                ·
                  refine ⟨1808167581752531748072113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4821780218006751328192301 1808167581752531748072113)
                  ·
                    refine ⟨1356125686314398811054085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1808167581752531748072113 1356125686314398811054085)
                    ·
                      refine ⟨254273566183949777072641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1356125686314398811054085 254273566183949777072641)
                      ·
                        rfl

theorem cell23_495196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_495196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495196 prefixEnd_495196 := by exact prefixLift 495196
  have htrace : WordTrace (prefixWord ++ tailWord_495196) baseStart_495196 baseEnd_495196 := by
    simpa [prefixWord, tailWord_495196, baseEnd_495196] using wordTrace_append hprefix tailTrace_495196
  have hstable : (prefixWord ++ tailWord_495196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495196).length < 2 ^ (prefixWord ++ tailWord_495196).sum := by decide
  have hdescent : baseEnd_495196 < baseStart_495196 := by decide
  rcases family_descends (prefixWord ++ tailWord_495196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495197 : List Nat := [1, 4, 4, 2, 1, 1, 3, 1, 1, 5]
def baseStart_495197 : Nat := 118140960795 + 495197 * 2 ^ 59
def prefixEnd_495197 : Nat := 4983230072969 + 3 ^ 40 * 495197 * 2
def baseEnd_495197 : Nat := 84758026554868091053379

theorem tailTrace_495197 : CollatzResearch.WordTrace tailWord_495197 prefixEnd_495197 84758026554868091053379 := by
  unfold tailWord_495197
  simp only [CollatzResearch.WordTrace]
  refine ⟨18061318386993316759515845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12040878924662211173010563 18061318386993316759515845)
  ·
    refine ⟨3386497197561246892409221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18061318386993316759515845 3386497197561246892409221)
    ·
      refine ⟨634968224542733792326729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3386497197561246892409221 634968224542733792326729)
      ·
        refine ⟨476226168407050344245047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 634968224542733792326729 476226168407050344245047)
        ·
          refine ⟨714339252610575516367571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476226168407050344245047 714339252610575516367571)
          ·
            refine ⟨1071508878915863274551357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 714339252610575516367571 1071508878915863274551357)
            ·
              refine ⟨401815829593448727956759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1071508878915863274551357 401815829593448727956759)
              ·
                refine ⟨602723744390173091935139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401815829593448727956759 602723744390173091935139)
                ·
                  refine ⟨904085616585259637902709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 602723744390173091935139 904085616585259637902709)
                  ·
                    refine ⟨84758026554868091053379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 904085616585259637902709 84758026554868091053379)
                    ·
                      rfl

theorem cell23_495197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_495197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495197 prefixEnd_495197 := by exact prefixLift 495197
  have htrace : WordTrace (prefixWord ++ tailWord_495197) baseStart_495197 baseEnd_495197 := by
    simpa [prefixWord, tailWord_495197, baseEnd_495197] using wordTrace_append hprefix tailTrace_495197
  have hstable : (prefixWord ++ tailWord_495197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495197).length < 2 ^ (prefixWord ++ tailWord_495197).sum := by decide
  have hdescent : baseEnd_495197 < baseStart_495197 := by decide
  rcases family_descends (prefixWord ++ tailWord_495197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495200 : List Nat := [2, 1, 1, 3, 2, 1, 1, 7, 1, 2, 2]
def baseStart_495200 : Nat := 118140960795 + 495200 * 2 ^ 59
def prefixEnd_495200 : Nat := 4983230072969 + 3 ^ 40 * 495200 * 2
def baseEnd_495200 : Nat := 254275620106567761422623

theorem tailTrace_495200 : CollatzResearch.WordTrace tailWord_495200 prefixEnd_495200 254275620106567761422623 := by
  unfold tailWord_495200
  simp only [CollatzResearch.WordTrace]
  refine ⟨9030713902991224135937527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12040951870654965514583369 9030713902991224135937527)
  ·
    refine ⟨13546070854486836203906291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9030713902991224135937527 13546070854486836203906291)
    ·
      refine ⟨20319106281730254305859437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13546070854486836203906291 20319106281730254305859437)
      ·
        refine ⟨7619664855648845364697289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20319106281730254305859437 7619664855648845364697289)
        ·
          refine ⟨5714748641736634023522967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7619664855648845364697289 5714748641736634023522967)
          ·
            refine ⟨8572122962604951035284451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5714748641736634023522967 8572122962604951035284451)
            ·
              refine ⟨12858184443907426552926677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8572122962604951035284451 12858184443907426552926677)
              ·
                refine ⟨301363697904080309834219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 12858184443907426552926677 301363697904080309834219)
                ·
                  refine ⟨452045546856120464751329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 301363697904080309834219 452045546856120464751329)
                  ·
                    refine ⟨339034160142090348563497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 452045546856120464751329 339034160142090348563497)
                    ·
                      refine ⟨254275620106567761422623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 339034160142090348563497 254275620106567761422623)
                      ·
                        rfl

theorem cell23_495200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 7, 1, 2, 2].length) (baseStart_495200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495200 prefixEnd_495200 := by exact prefixLift 495200
  have htrace : WordTrace (prefixWord ++ tailWord_495200) baseStart_495200 baseEnd_495200 := by
    simpa [prefixWord, tailWord_495200, baseEnd_495200] using wordTrace_append hprefix tailTrace_495200
  have hstable : (prefixWord ++ tailWord_495200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495200).length < 2 ^ (prefixWord ++ tailWord_495200).sum := by decide
  have hdescent : baseEnd_495200 < baseStart_495200 := by decide
  rcases family_descends (prefixWord ++ tailWord_495200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495233 : List Nat := [1, 2, 4, 2, 1, 3, 2, 1, 1, 3, 3]
def baseStart_495233 : Nat := 118140960795 + 495233 * 2 ^ 59
def prefixEnd_495233 : Nat := 4983230072969 + 3 ^ 40 * 495233 * 2
def baseEnd_495233 : Nat := 254292564968166132309971

theorem tailTrace_495233 : CollatzResearch.WordTrace tailWord_495233 prefixEnd_495233 254292564968166132309971 := by
  unfold tailWord_495233
  simp only [CollatzResearch.WordTrace]
  refine ⟨18062631414862894907826353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12041754276575263271884235 18062631414862894907826353)
  ·
    refine ⟨13546973561147171180869765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18062631414862894907826353 13546973561147171180869765)
    ·
      refine ⟨2540057542715094596413081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13546973561147171180869765 2540057542715094596413081)
      ·
        refine ⟨1905043157036320947309811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2540057542715094596413081 1905043157036320947309811)
        ·
          refine ⟨2857564735554481420964717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1905043157036320947309811 2857564735554481420964717)
          ·
            refine ⟨1071586775832930532861769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2857564735554481420964717 1071586775832930532861769)
            ·
              refine ⟨803690081874697899646327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1071586775832930532861769 803690081874697899646327)
              ·
                refine ⟨1205535122812046849469491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 803690081874697899646327 1205535122812046849469491)
                ·
                  refine ⟨1808302684218070274204237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1205535122812046849469491 1808302684218070274204237)
                  ·
                    refine ⟨678113506581776352826589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1808302684218070274204237 678113506581776352826589)
                    ·
                      refine ⟨254292564968166132309971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 678113506581776352826589 254292564968166132309971)
                      ·
                        rfl

theorem cell23_495233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_495233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495233 prefixEnd_495233 := by exact prefixLift 495233
  have htrace : WordTrace (prefixWord ++ tailWord_495233) baseStart_495233 baseEnd_495233 := by
    simpa [prefixWord, tailWord_495233, baseEnd_495233] using wordTrace_append hprefix tailTrace_495233
  have hstable : (prefixWord ++ tailWord_495233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495233).length < 2 ^ (prefixWord ++ tailWord_495233).sum := by decide
  have hdescent : baseEnd_495233 < baseStart_495233 := by decide
  rcases family_descends (prefixWord ++ tailWord_495233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495243 : List Nat := [1, 1, 1, 1, 4, 1, 4, 4, 1, 3, 2]
def baseStart_495243 : Nat := 118140960795 + 495243 * 2 ^ 59
def prefixEnd_495243 : Nat := 4983230072969 + 3 ^ 40 * 495243 * 2
def baseEnd_495243 : Nat := 254297699774711093184925

theorem tailTrace_495243 : CollatzResearch.WordTrace tailWord_495243 prefixEnd_495243 254297699774711093184925 := by
  unfold tailWord_495243
  simp only [CollatzResearch.WordTrace]
  refine ⟨18062996144826666615690383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12041997429884444410460255 18062996144826666615690383)
  ·
    refine ⟨27094494217239999923535575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18062996144826666615690383 27094494217239999923535575)
    ·
      refine ⟨40641741325859999885303363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27094494217239999923535575 40641741325859999885303363)
      ·
        refine ⟨60962611988789999827955045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40641741325859999885303363 60962611988789999827955045)
        ·
          refine ⟨11430489747898124967741571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60962611988789999827955045 11430489747898124967741571)
          ·
            refine ⟨17145734621847187451612357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11430489747898124967741571 17145734621847187451612357)
            ·
              refine ⟨3214825241596347647177317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17145734621847187451612357 3214825241596347647177317)
              ·
                refine ⟨602779732799315183845747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3214825241596347647177317 602779732799315183845747)
                ·
                  refine ⟨904169599198972775768621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 602779732799315183845747 904169599198972775768621)
                  ·
                    refine ⟨339063599699614790913233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 904169599198972775768621 339063599699614790913233)
                    ·
                      refine ⟨254297699774711093184925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 339063599699614790913233 254297699774711093184925)
                      ·
                        rfl

theorem cell23_495243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 3, 2].length) (baseStart_495243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495243 prefixEnd_495243 := by exact prefixLift 495243
  have htrace : WordTrace (prefixWord ++ tailWord_495243) baseStart_495243 baseEnd_495243 := by
    simpa [prefixWord, tailWord_495243, baseEnd_495243] using wordTrace_append hprefix tailTrace_495243
  have hstable : (prefixWord ++ tailWord_495243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495243).length < 2 ^ (prefixWord ++ tailWord_495243).sum := by decide
  have hdescent : baseEnd_495243 < baseStart_495243 := by decide
  rcases family_descends (prefixWord ++ tailWord_495243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495290 : List Nat := [3, 1, 1, 1, 2, 6, 1, 1, 1, 4, 2]
def baseStart_495290 : Nat := 118140960795 + 495290 * 2 ^ 59
def prefixEnd_495290 : Nat := 4983230072969 + 3 ^ 40 * 495290 * 2
def baseEnd_495290 : Nat := 254321833365472409297209

theorem tailTrace_495290 : CollatzResearch.WordTrace tailWord_495290 prefixEnd_495290 254321833365472409297209 := by
  unfold tailWord_495290
  simp only [CollatzResearch.WordTrace]
  refine ⟨4516177593914098410662831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12043140250437595761767549 4516177593914098410662831)
  ·
    refine ⟨6774266390871147615994247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4516177593914098410662831 6774266390871147615994247)
    ·
      refine ⟨10161399586306721423991371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6774266390871147615994247 10161399586306721423991371)
      ·
        refine ⟨15242099379460082135987057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10161399586306721423991371 15242099379460082135987057)
        ·
          refine ⟨11431574534595061601990293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15242099379460082135987057 11431574534595061601990293)
          ·
            refine ⟨535855056309143512593295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11431574534595061601990293 535855056309143512593295)
            ·
              refine ⟨803782584463715268889943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535855056309143512593295 803782584463715268889943)
              ·
                refine ⟨1205673876695572903334915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 803782584463715268889943 1205673876695572903334915)
                ·
                  refine ⟨1808510815043359355002373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1205673876695572903334915 1808510815043359355002373)
                  ·
                    refine ⟨339095777820629879062945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1808510815043359355002373 339095777820629879062945)
                    ·
                      refine ⟨254321833365472409297209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 339095777820629879062945 254321833365472409297209)
                      ·
                        rfl

theorem cell23_495290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 1, 4, 2].length) (baseStart_495290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495290 prefixEnd_495290 := by exact prefixLift 495290
  have htrace : WordTrace (prefixWord ++ tailWord_495290) baseStart_495290 baseEnd_495290 := by
    simpa [prefixWord, tailWord_495290, baseEnd_495290] using wordTrace_append hprefix tailTrace_495290
  have hstable : (prefixWord ++ tailWord_495290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495290).length < 2 ^ (prefixWord ++ tailWord_495290).sum := by decide
  have hdescent : baseEnd_495290 < baseStart_495290 := by decide
  rcases family_descends (prefixWord ++ tailWord_495290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495313 : List Nat := [1, 2, 2, 1, 2, 4, 3, 3, 5]
def baseStart_495313 : Nat := 118140960795 + 495313 * 2 ^ 59
def prefixEnd_495313 : Nat := 4983230072969 + 3 ^ 40 * 495313 * 2
def baseEnd_495313 : Nat := 28259293713391757701067

theorem tailTrace_495313 : CollatzResearch.WordTrace tailWord_495313 prefixEnd_495313 28259293713391757701067 := by
  unfold tailWord_495313
  simp only [CollatzResearch.WordTrace]
  refine ⟨18065549254573068570738593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12043699503048712380492395 18065549254573068570738593)
  ·
    refine ⟨13549161940929801428053945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18065549254573068570738593 13549161940929801428053945)
    ·
      refine ⟨10161871455697351071040459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13549161940929801428053945 10161871455697351071040459)
      ·
        refine ⟨15242807183546026606560689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10161871455697351071040459 15242807183546026606560689)
        ·
          refine ⟨11432105387659519954920517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15242807183546026606560689 11432105387659519954920517)
          ·
            refine ⟨2143519760186159991547597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11432105387659519954920517 2143519760186159991547597)
            ·
              refine ⟨803819910069809996830349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2143519760186159991547597 803819910069809996830349)
              ·
                refine ⟨301432466276178748811381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 803819910069809996830349 301432466276178748811381)
                ·
                  refine ⟨28259293713391757701067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 301432466276178748811381 28259293713391757701067)
                  ·
                    rfl

theorem cell23_495313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 3, 5].length) (baseStart_495313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495313 prefixEnd_495313 := by exact prefixLift 495313
  have htrace : WordTrace (prefixWord ++ tailWord_495313) baseStart_495313 baseEnd_495313 := by
    simpa [prefixWord, tailWord_495313, baseEnd_495313] using wordTrace_append hprefix tailTrace_495313
  have hstable : (prefixWord ++ tailWord_495313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495313).length < 2 ^ (prefixWord ++ tailWord_495313).sum := by decide
  have hdescent : baseEnd_495313 < baseStart_495313 := by decide
  rcases family_descends (prefixWord ++ tailWord_495313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495333 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 2, 5, 2]
def baseStart_495333 : Nat := 118140960795 + 495333 * 2 ^ 59
def prefixEnd_495333 : Nat := 4983230072969 + 3 ^ 40 * 495333 * 2
def baseEnd_495333 : Nat := 254343913033615741059511

theorem tailTrace_495333 : CollatzResearch.WordTrace tailWord_495333 prefixEnd_495333 254343913033615741059511 := by
  unfold tailWord_495333
  simp only [CollatzResearch.WordTrace]
  refine ⟨18066278714500611986466653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12044185809667074657644435 18066278714500611986466653)
  ·
    refine ⟨6774854517937729494924995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18066278714500611986466653 6774854517937729494924995)
    ·
      refine ⟨10162281776906594242387493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6774854517937729494924995 10162281776906594242387493)
      ·
        refine ⟨1905427833169986420447655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10162281776906594242387493 1905427833169986420447655)
        ·
          refine ⟨2858141749754979630671483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1905427833169986420447655 2858141749754979630671483)
          ·
            refine ⟨4287212624632469446007225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2858141749754979630671483 4287212624632469446007225)
            ·
              refine ⟨3215409468474352084505419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4287212624632469446007225 3215409468474352084505419)
              ·
                refine ⟨4823114202711528126758129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3215409468474352084505419 4823114202711528126758129)
                ·
                  refine ⟨3617335652033646095068597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4823114202711528126758129 3617335652033646095068597)
                  ·
                    refine ⟨339125217378154321412681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3617335652033646095068597 339125217378154321412681)
                    ·
                      refine ⟨254343913033615741059511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 339125217378154321412681 254343913033615741059511)
                      ·
                        rfl

theorem cell23_495333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_495333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495333 prefixEnd_495333 := by exact prefixLift 495333
  have htrace : WordTrace (prefixWord ++ tailWord_495333) baseStart_495333 baseEnd_495333 := by
    simpa [prefixWord, tailWord_495333, baseEnd_495333] using wordTrace_append hprefix tailTrace_495333
  have hstable : (prefixWord ++ tailWord_495333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495333).length < 2 ^ (prefixWord ++ tailWord_495333).sum := by decide
  have hdescent : baseEnd_495333 < baseStart_495333 := by decide
  rcases family_descends (prefixWord ++ tailWord_495333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495336 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 1, 1, 7]
def baseStart_495336 : Nat := 118140960795 + 495336 * 2 ^ 59
def prefixEnd_495336 : Nat := 4983230072969 + 3 ^ 40 * 495336 * 2
def baseEnd_495336 : Nat := 254345453475579229321997

theorem tailTrace_495336 : CollatzResearch.WordTrace tailWord_495336 prefixEnd_495336 254345453475579229321997 := by
  unfold tailWord_495336
  simp only [CollatzResearch.WordTrace]
  refine ⟨9033194066744871749412931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12044258755659828999217241 9033194066744871749412931)
  ·
    refine ⟨13549791100117307624119397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9033194066744871749412931 13549791100117307624119397)
    ·
      refine ⟨2540585831271995179522387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13549791100117307624119397 2540585831271995179522387)
      ·
        refine ⟨3810878746907992769283581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2540585831271995179522387 3810878746907992769283581)
        ·
          refine ⟨1429079530090497288481343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3810878746907992769283581 1429079530090497288481343)
          ·
            refine ⟨2143619295135745932722015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1429079530090497288481343 2143619295135745932722015)
            ·
              refine ⟨3215428942703618899083023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2143619295135745932722015 3215428942703618899083023)
              ·
                refine ⟨4823143414055428348624535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3215428942703618899083023 4823143414055428348624535)
                ·
                  refine ⟨7234715121083142522936803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4823143414055428348624535 7234715121083142522936803)
                  ·
                    refine ⟨10852072681624713784405205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7234715121083142522936803 10852072681624713784405205)
                    ·
                      refine ⟨254345453475579229321997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 10852072681624713784405205 254345453475579229321997)
                      ·
                        rfl

theorem cell23_495336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_495336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495336 prefixEnd_495336 := by exact prefixLift 495336
  have htrace : WordTrace (prefixWord ++ tailWord_495336) baseStart_495336 baseEnd_495336 := by
    simpa [prefixWord, tailWord_495336, baseEnd_495336] using wordTrace_append hprefix tailTrace_495336
  have hstable : (prefixWord ++ tailWord_495336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495336).length < 2 ^ (prefixWord ++ tailWord_495336).sum := by decide
  have hdescent : baseEnd_495336 < baseStart_495336 := by decide
  rcases family_descends (prefixWord ++ tailWord_495336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495433 : List Nat := [1, 2, 1, 1, 2, 4, 3, 3, 1, 5]
def baseStart_495433 : Nat := 118140960795 + 495433 * 2 ^ 59
def prefixEnd_495433 : Nat := 4983230072969 + 3 ^ 40 * 495433 * 2
def baseEnd_495433 : Nat := 84798420366355116603017

theorem tailTrace_495433 : CollatzResearch.WordTrace tailWord_495433 prefixEnd_495433 84798420366355116603017 := by
  unfold tailWord_495433
  simp only [CollatzResearch.WordTrace]
  refine ⟨18069926014138329065106953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12046617342758886043404635 18069926014138329065106953)
  ·
    refine ⟨13552444510603746798830215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18069926014138329065106953 13552444510603746798830215)
    ·
      refine ⟨20328666765905620198245323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13552444510603746798830215 20328666765905620198245323)
      ·
        refine ⟨30493000148858430297367985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20328666765905620198245323 30493000148858430297367985)
        ·
          refine ⟨22869750111643822723025989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30493000148858430297367985 22869750111643822723025989)
          ·
            refine ⟨4288078145933216760567373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22869750111643822723025989 4288078145933216760567373)
            ·
              refine ⟨1608029304724956285212765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4288078145933216760567373 1608029304724956285212765)
              ·
                refine ⟨603010989271858606954787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1608029304724956285212765 603010989271858606954787)
                ·
                  refine ⟨904516483907787910432181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 603010989271858606954787 904516483907787910432181)
                  ·
                    refine ⟨84798420366355116603017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 904516483907787910432181 84798420366355116603017)
                    ·
                      rfl

theorem cell23_495433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 3, 1, 5].length) (baseStart_495433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495433 prefixEnd_495433 := by exact prefixLift 495433
  have htrace : WordTrace (prefixWord ++ tailWord_495433) baseStart_495433 baseEnd_495433 := by
    simpa [prefixWord, tailWord_495433, baseEnd_495433] using wordTrace_append hprefix tailTrace_495433
  have hstable : (prefixWord ++ tailWord_495433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495433).length < 2 ^ (prefixWord ++ tailWord_495433).sum := by decide
  have hdescent : baseEnd_495433 < baseStart_495433 := by decide
  rcases family_descends (prefixWord ++ tailWord_495433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495437 : List Nat := [1, 6, 1, 2, 1, 3, 1, 2, 6]
def baseStart_495437 : Nat := 118140960795 + 495437 * 2 ^ 59
def prefixEnd_495437 : Nat := 4983230072969 + 3 ^ 40 * 495437 * 2
def baseEnd_495437 : Nat := 28266368335742592684337

theorem tailTrace_495437 : CollatzResearch.WordTrace tailWord_495437 prefixEnd_495437 28266368335742592684337 := by
  unfold tailWord_495437
  simp only [CollatzResearch.WordTrace]
  refine ⟨18070071906123837748252565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12046714604082558498835043 18070071906123837748252565)
  ·
    refine ⟨847034620599554894449339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18070071906123837748252565 847034620599554894449339)
    ·
      refine ⟨1270551930899332341674009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 847034620599554894449339 1270551930899332341674009)
      ·
        refine ⟨952913948174499256255507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1270551930899332341674009 952913948174499256255507)
        ·
          refine ⟨1429370922261748884383261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 952913948174499256255507 1429370922261748884383261)
          ·
            refine ⟨536014095848155831643723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1429370922261748884383261 536014095848155831643723)
            ·
              refine ⟨804021143772233747465585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536014095848155831643723 804021143772233747465585)
              ·
                refine ⟨603015857829175310599189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 804021143772233747465585 603015857829175310599189)
                ·
                  refine ⟨28266368335742592684337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 603015857829175310599189 28266368335742592684337)
                  ·
                    rfl

theorem cell23_495437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_495437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495437 prefixEnd_495437 := by exact prefixLift 495437
  have htrace : WordTrace (prefixWord ++ tailWord_495437) baseStart_495437 baseEnd_495437 := by
    simpa [prefixWord, tailWord_495437, baseEnd_495437] using wordTrace_append hprefix tailTrace_495437
  have hstable : (prefixWord ++ tailWord_495437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495437).length < 2 ^ (prefixWord ++ tailWord_495437).sum := by decide
  have hdescent : baseEnd_495437 < baseStart_495437 := by decide
  rcases family_descends (prefixWord ++ tailWord_495437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495447 : List Nat := [1, 1, 3, 2, 5, 1, 2, 1, 3, 1, 3]
def baseStart_495447 : Nat := 118140960795 + 495447 * 2 ^ 59
def prefixEnd_495447 : Nat := 4983230072969 + 3 ^ 40 * 495447 * 2
def baseEnd_495447 : Nat := 254402449828228295033987

theorem tailTrace_495447 : CollatzResearch.WordTrace tailWord_495447 prefixEnd_495447 254402449828228295033987 := by
  unfold tailWord_495447
  simp only [CollatzResearch.WordTrace]
  refine ⟨18070436636087609456116595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12046957757391739637411063 18070436636087609456116595)
  ·
    refine ⟨27105654954131414184174893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18070436636087609456116595 27105654954131414184174893)
    ·
      refine ⟨10164620607799280319065585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27105654954131414184174893 10164620607799280319065585)
      ·
        refine ⟨7623465455849460239299189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10164620607799280319065585 7623465455849460239299189)
        ·
          refine ⟨714699886485886897434299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7623465455849460239299189 714699886485886897434299)
          ·
            refine ⟨1072049829728830346151449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 714699886485886897434299 1072049829728830346151449)
            ·
              refine ⟨804037372296622759613587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1072049829728830346151449 804037372296622759613587)
              ·
                refine ⟨1206056058444934139420381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 804037372296622759613587 1206056058444934139420381)
                ·
                  refine ⟨452271021916850302282643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1206056058444934139420381 452271021916850302282643)
                  ·
                    refine ⟨678406532875275453423965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 452271021916850302282643 678406532875275453423965)
                    ·
                      refine ⟨254402449828228295033987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 678406532875275453423965 254402449828228295033987)
                      ·
                        rfl

theorem cell23_495447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_495447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495447 prefixEnd_495447 := by exact prefixLift 495447
  have htrace : WordTrace (prefixWord ++ tailWord_495447) baseStart_495447 baseEnd_495447 := by
    simpa [prefixWord, tailWord_495447, baseEnd_495447] using wordTrace_append hprefix tailTrace_495447
  have hstable : (prefixWord ++ tailWord_495447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495447).length < 2 ^ (prefixWord ++ tailWord_495447).sum := by decide
  have hdescent : baseEnd_495447 < baseStart_495447 := by decide
  rcases family_descends (prefixWord ++ tailWord_495447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495514 : List Nat := [3, 1, 1, 4, 2, 3, 2, 1, 2, 4]
def baseStart_495514 : Nat := 118140960795 + 495514 * 2 ^ 59
def prefixEnd_495514 : Nat := 4983230072969 + 3 ^ 40 * 495514 * 2
def baseEnd_495514 : Nat := 84812284344026510965393

theorem tailTrace_495514 : CollatzResearch.WordTrace tailWord_495514 prefixEnd_495514 84812284344026510965393 := by
  unfold tailWord_495514
  simp only [CollatzResearch.WordTrace]
  refine ⟨4518220081711219974701399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12048586884563253265870397 4518220081711219974701399)
  ·
    refine ⟨6777330122566829962052099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4518220081711219974701399 6777330122566829962052099)
    ·
      refine ⟨10165995183850244943078149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6777330122566829962052099 10165995183850244943078149)
      ·
        refine ⟨1906124096971920926827153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10165995183850244943078149 1906124096971920926827153)
        ·
          refine ⟨1429593072728940695120365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1906124096971920926827153 1429593072728940695120365)
          ·
            refine ⟨536097402273352760670137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1429593072728940695120365 536097402273352760670137)
            ·
              refine ⟨402073051705014570502603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 536097402273352760670137 402073051705014570502603)
              ·
                refine ⟨603109577557521855753905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402073051705014570502603 603109577557521855753905)
                ·
                  refine ⟨452332183168141391815429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 603109577557521855753905 452332183168141391815429)
                  ·
                    refine ⟨84812284344026510965393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 452332183168141391815429 84812284344026510965393)
                    ·
                      rfl

theorem cell23_495514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 1, 2, 4].length) (baseStart_495514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495514 prefixEnd_495514 := by exact prefixLift 495514
  have htrace : WordTrace (prefixWord ++ tailWord_495514) baseStart_495514 baseEnd_495514 := by
    simpa [prefixWord, tailWord_495514, baseEnd_495514] using wordTrace_append hprefix tailTrace_495514
  have hstable : (prefixWord ++ tailWord_495514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495514).length < 2 ^ (prefixWord ++ tailWord_495514).sum := by decide
  have hdescent : baseEnd_495514 < baseStart_495514 := by decide
  rcases family_descends (prefixWord ++ tailWord_495514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495563 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 1, 6, 3]
def baseStart_495563 : Nat := 118140960795 + 495563 * 2 ^ 59
def prefixEnd_495563 : Nat := 4983230072969 + 3 ^ 40 * 495563 * 2
def baseEnd_495563 : Nat := 254462013584149841183453

theorem tailTrace_495563 : CollatzResearch.WordTrace tailWord_495563 prefixEnd_495563 254462013584149841183453 := by
  unfold tailWord_495563
  simp only [CollatzResearch.WordTrace]
  refine ⟨18074667503667361267339343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12049778335778240844892895 18074667503667361267339343)
  ·
    refine ⟨27112001255501041901009015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18074667503667361267339343 27112001255501041901009015)
    ·
      refine ⟨40668001883251562851513523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27112001255501041901009015 40668001883251562851513523)
      ·
        refine ⟨61002002824877344277270285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40668001883251562851513523 61002002824877344277270285)
        ·
          refine ⟨22875751059329004103976357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61002002824877344277270285 22875751059329004103976357)
          ·
            refine ⟨4289203323624188269495567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22875751059329004103976357 4289203323624188269495567)
            ·
              refine ⟨6433804985436282404243351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4289203323624188269495567 6433804985436282404243351)
              ·
                refine ⟨9650707478154423606365027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6433804985436282404243351 9650707478154423606365027)
                ·
                  refine ⟨14476061217231635409547541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9650707478154423606365027 14476061217231635409547541)
                  ·
                    refine ⟨678565369557732909822541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14476061217231635409547541 678565369557732909822541)
                    ·
                      refine ⟨254462013584149841183453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 678565369557732909822541 254462013584149841183453)
                      ·
                        rfl

theorem cell23_495563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 6, 3].length) (baseStart_495563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495563 prefixEnd_495563 := by exact prefixLift 495563
  have htrace : WordTrace (prefixWord ++ tailWord_495563) baseStart_495563 baseEnd_495563 := by
    simpa [prefixWord, tailWord_495563, baseEnd_495563] using wordTrace_append hprefix tailTrace_495563
  have hstable : (prefixWord ++ tailWord_495563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495563).length < 2 ^ (prefixWord ++ tailWord_495563).sum := by decide
  have hdescent : baseEnd_495563 < baseStart_495563 := by decide
  rcases family_descends (prefixWord ++ tailWord_495563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495583 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 9]
def baseStart_495583 : Nat := 118140960795 + 495583 * 2 ^ 59
def prefixEnd_495583 : Nat := 4983230072969 + 3 ^ 40 * 495583 * 2
def baseEnd_495583 : Nat := 28274698133026640325929

theorem tailTrace_495583 : CollatzResearch.WordTrace tailWord_495583 prefixEnd_495583 28274698133026640325929 := by
  unfold tailWord_495583
  simp only [CollatzResearch.WordTrace]
  refine ⟨18075396963594904683067403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12050264642396603122044935 18075396963594904683067403)
  ·
    refine ⟨27113095445392357024601105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18075396963594904683067403 27113095445392357024601105)
    ·
      refine ⟨20334821584044267768450829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27113095445392357024601105 20334821584044267768450829)
      ·
        refine ⟨7625558094016600413169061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20334821584044267768450829 7625558094016600413169061)
        ·
          refine ⟨1429792142628112577469199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7625558094016600413169061 1429792142628112577469199)
          ·
            refine ⟨2144688213942168866203799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1429792142628112577469199 2144688213942168866203799)
            ·
              refine ⟨3217032320913253299305699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2144688213942168866203799 3217032320913253299305699)
              ·
                refine ⟨4825548481369879948958549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3217032320913253299305699 4825548481369879948958549)
                ·
                  refine ⟨28274698133026640325929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4825548481369879948958549 28274698133026640325929)
                  ·
                    rfl

theorem cell23_495583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 9].length) (baseStart_495583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495583 prefixEnd_495583 := by exact prefixLift 495583
  have htrace : WordTrace (prefixWord ++ tailWord_495583) baseStart_495583 baseEnd_495583 := by
    simpa [prefixWord, tailWord_495583, baseEnd_495583] using wordTrace_append hprefix tailTrace_495583
  have hstable : (prefixWord ++ tailWord_495583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495583).length < 2 ^ (prefixWord ++ tailWord_495583).sum := by decide
  have hdescent : baseEnd_495583 < baseStart_495583 := by decide
  rcases family_descends (prefixWord ++ tailWord_495583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495600 : List Nat := [2, 1, 1, 1, 3, 2, 3, 5, 5]
def baseStart_495600 : Nat := 118140960795 + 495600 * 2 ^ 59
def prefixEnd_495600 : Nat := 4983230072969 + 3 ^ 40 * 495600 * 2
def baseEnd_495600 : Nat := 28275668040929577380087

theorem tailTrace_495600 : CollatzResearch.WordTrace tailWord_495600 prefixEnd_495600 28275668040929577380087 := by
  unfold tailWord_495600
  simp only [CollatzResearch.WordTrace]
  refine ⟨9038008502266658293218127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12050678003022211057624169 9038008502266658293218127)
  ·
    refine ⟨13557012753399987439827191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9038008502266658293218127 13557012753399987439827191)
    ·
      refine ⟨20335519130099981159740787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13557012753399987439827191 20335519130099981159740787)
      ·
        refine ⟨30503278695149971739611181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20335519130099981159740787 30503278695149971739611181)
        ·
          refine ⟨11438729510681239402354193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30503278695149971739611181 11438729510681239402354193)
          ·
            refine ⟨8579047133010929551765645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11438729510681239402354193 8579047133010929551765645)
            ·
              refine ⟨3217142674879098581912117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8579047133010929551765645 3217142674879098581912117)
              ·
                refine ⟨301607125769915492054261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3217142674879098581912117 301607125769915492054261)
                ·
                  refine ⟨28275668040929577380087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 301607125769915492054261 28275668040929577380087)
                  ·
                    rfl

theorem cell23_495600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 5, 5].length) (baseStart_495600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495600 prefixEnd_495600 := by exact prefixLift 495600
  have htrace : WordTrace (prefixWord ++ tailWord_495600) baseStart_495600 baseEnd_495600 := by
    simpa [prefixWord, tailWord_495600, baseEnd_495600] using wordTrace_append hprefix tailTrace_495600
  have hstable : (prefixWord ++ tailWord_495600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495600).length < 2 ^ (prefixWord ++ tailWord_495600).sum := by decide
  have hdescent : baseEnd_495600 < baseStart_495600 := by decide
  rcases family_descends (prefixWord ++ tailWord_495600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495622 : List Nat := [6, 2, 1, 2, 1, 1, 3, 1, 2, 1, 3]
def baseStart_495622 : Nat := 118140960795 + 495622 * 2 ^ 59
def prefixEnd_495622 : Nat := 4983230072969 + 3 ^ 40 * 495622 * 2
def baseEnd_495622 : Nat := 254492308942765110345683

theorem tailTrace_495622 : CollatzResearch.WordTrace tailWord_495622 prefixEnd_495622 254492308942765110345683 := by
  unfold tailWord_495622
  simp only [CollatzResearch.WordTrace]
  refine ⟨564900606576675448241785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12051212940302409562491413 564900606576675448241785)
  ·
    refine ⟨423675454932506586181339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 564900606576675448241785 423675454932506586181339)
    ·
      refine ⟨635513182398759879272009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423675454932506586181339 635513182398759879272009)
      ·
        refine ⟨476634886799069909454007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 635513182398759879272009 476634886799069909454007)
        ·
          refine ⟨714952330198604864181011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476634886799069909454007 714952330198604864181011)
          ·
            refine ⟨1072428495297907296271517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 714952330198604864181011 1072428495297907296271517)
            ·
              refine ⟨402160685736715236101819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1072428495297907296271517 402160685736715236101819)
              ·
                refine ⟨603241028605072854152729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402160685736715236101819 603241028605072854152729)
                ·
                  refine ⟨452430771453804640614547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 603241028605072854152729 452430771453804640614547)
                  ·
                    refine ⟨678646157180706960921821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 452430771453804640614547 678646157180706960921821)
                    ·
                      refine ⟨254492308942765110345683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 678646157180706960921821 254492308942765110345683)
                      ·
                        rfl

theorem cell23_495622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_495622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495622 prefixEnd_495622 := by exact prefixLift 495622
  have htrace : WordTrace (prefixWord ++ tailWord_495622) baseStart_495622 baseEnd_495622 := by
    simpa [prefixWord, tailWord_495622, baseEnd_495622] using wordTrace_append hprefix tailTrace_495622
  have hstable : (prefixWord ++ tailWord_495622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495622).length < 2 ^ (prefixWord ++ tailWord_495622).sum := by decide
  have hdescent : baseEnd_495622 < baseStart_495622 := by decide
  rcases family_descends (prefixWord ++ tailWord_495622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495650 : List Nat := [3, 3, 1, 1, 1, 2, 1, 3, 1, 3, 4]
def baseStart_495650 : Nat := 118140960795 + 495650 * 2 ^ 59
def prefixEnd_495650 : Nat := 4983230072969 + 3 ^ 40 * 495650 * 2
def baseEnd_495650 : Nat := 254506686401091000795553

theorem tailTrace_495650 : CollatzResearch.WordTrace tailWord_495650 prefixEnd_495650 254506686401091000795553 := by
  unfold tailWord_495650
  simp only [CollatzResearch.WordTrace]
  refine ⟨4519460163588043781439101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12051893769568116750504269 4519460163588043781439101)
  ·
    refine ⟨1694797561345516418039663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4519460163588043781439101 1694797561345516418039663)
    ·
      refine ⟨2542196342018274627059495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1694797561345516418039663 2542196342018274627059495)
      ·
        refine ⟨3813294513027411940589243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2542196342018274627059495 3813294513027411940589243)
        ·
          refine ⟨5719941769541117910883865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3813294513027411940589243 5719941769541117910883865)
          ·
            refine ⟨4289956327155838433162899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5719941769541117910883865 4289956327155838433162899)
            ·
              refine ⟨6434934490733757649744349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4289956327155838433162899 6434934490733757649744349)
              ·
                refine ⟨2413100434025159118654131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6434934490733757649744349 2413100434025159118654131)
                ·
                  refine ⟨3619650651037738677981197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2413100434025159118654131 3619650651037738677981197)
                  ·
                    refine ⟨1357368994139152004242949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3619650651037738677981197 1357368994139152004242949)
                    ·
                      refine ⟨254506686401091000795553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1357368994139152004242949 254506686401091000795553)
                      ·
                        rfl

theorem cell23_495650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_495650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495650 prefixEnd_495650 := by exact prefixLift 495650
  have htrace : WordTrace (prefixWord ++ tailWord_495650) baseStart_495650 baseEnd_495650 := by
    simpa [prefixWord, tailWord_495650, baseEnd_495650] using wordTrace_append hprefix tailTrace_495650
  have hstable : (prefixWord ++ tailWord_495650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495650).length < 2 ^ (prefixWord ++ tailWord_495650).sum := by decide
  have hdescent : baseEnd_495650 < baseStart_495650 := by decide
  rcases family_descends (prefixWord ++ tailWord_495650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495663 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 6]
def baseStart_495663 : Nat := 118140960795 + 495663 * 2 ^ 59
def prefixEnd_495663 : Nat := 4983230072969 + 3 ^ 40 * 495663 * 2
def baseEnd_495663 : Nat := 254513361649599449932993

theorem tailTrace_495663 : CollatzResearch.WordTrace tailWord_495663 prefixEnd_495663 254513361649599449932993 := by
  unfold tailWord_495663
  simp only [CollatzResearch.WordTrace]
  refine ⟨18078314803305078345979643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12052209868870052230653095 18078314803305078345979643)
  ·
    refine ⟨27117472204957617518969465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18078314803305078345979643 27117472204957617518969465)
    ·
      refine ⟨20338104153718213139227099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27117472204957617518969465 20338104153718213139227099)
      ·
        refine ⟨30507156230577319708840649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20338104153718213139227099 30507156230577319708840649)
        ·
          refine ⟨22880367172932989781630487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30507156230577319708840649 22880367172932989781630487)
          ·
            refine ⟨34320550759399484672445731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22880367172932989781630487 34320550759399484672445731)
            ·
              refine ⟨51480826139099227008668597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34320550759399484672445731 51480826139099227008668597)
              ·
                refine ⟨4826327450540552532062681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51480826139099227008668597 4826327450540552532062681)
                ·
                  refine ⟨3619745587905414399047011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4826327450540552532062681 3619745587905414399047011)
                  ·
                    refine ⟨5429618381858121598570517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3619745587905414399047011 5429618381858121598570517)
                    ·
                      refine ⟨254513361649599449932993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5429618381858121598570517 254513361649599449932993)
                      ·
                        rfl

theorem cell23_495663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 6].length) (baseStart_495663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495663 prefixEnd_495663 := by exact prefixLift 495663
  have htrace : WordTrace (prefixWord ++ tailWord_495663) baseStart_495663 baseEnd_495663 := by
    simpa [prefixWord, tailWord_495663, baseEnd_495663] using wordTrace_append hprefix tailTrace_495663
  have hstable : (prefixWord ++ tailWord_495663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495663).length < 2 ^ (prefixWord ++ tailWord_495663).sum := by decide
  have hdescent : baseEnd_495663 < baseStart_495663 := by decide
  rcases family_descends (prefixWord ++ tailWord_495663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495768 : List Nat := [2, 1, 2, 4, 3, 1, 2, 3, 1, 1, 3]
def baseStart_495768 : Nat := 118140960795 + 495768 * 2 ^ 59
def prefixEnd_495768 : Nat := 4983230072969 + 3 ^ 40 * 495768 * 2
def baseEnd_495768 : Nat := 254567277118321539120011

theorem tailTrace_495768 : CollatzResearch.WordTrace tailWord_495768 prefixEnd_495768 254567277118321539120011 := by
  unfold tailWord_495768
  simp only [CollatzResearch.WordTrace]
  refine ⟨9041072233962340639275979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12054762978616454185701305 9041072233962340639275979)
  ·
    refine ⟨13561608350943510958913969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9041072233962340639275979 13561608350943510958913969)
    ·
      refine ⟨10171206263207633219185477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13561608350943510958913969 10171206263207633219185477)
      ·
        refine ⟨1907101174351431228597277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10171206263207633219185477 1907101174351431228597277)
        ·
          refine ⟨715162940381786710723979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1907101174351431228597277 715162940381786710723979)
          ·
            refine ⟨1072744410572680066085969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715162940381786710723979 1072744410572680066085969)
            ·
              refine ⟨804558307929510049564477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1072744410572680066085969 804558307929510049564477)
              ·
                refine ⟨301709365473566268586679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 804558307929510049564477 301709365473566268586679)
                ·
                  refine ⟨452564048210349402880019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 301709365473566268586679 452564048210349402880019)
                  ·
                    refine ⟨678846072315524104320029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 452564048210349402880019 678846072315524104320029)
                    ·
                      refine ⟨254567277118321539120011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 678846072315524104320029 254567277118321539120011)
                      ·
                        rfl

theorem cell23_495768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_495768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495768 prefixEnd_495768 := by exact prefixLift 495768
  have htrace : WordTrace (prefixWord ++ tailWord_495768) baseStart_495768 baseEnd_495768 := by
    simpa [prefixWord, tailWord_495768, baseEnd_495768] using wordTrace_append hprefix tailTrace_495768
  have hstable : (prefixWord ++ tailWord_495768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495768).length < 2 ^ (prefixWord ++ tailWord_495768).sum := by decide
  have hdescent : baseEnd_495768 < baseStart_495768 := by decide
  rcases family_descends (prefixWord ++ tailWord_495768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495858 : List Nat := [3, 2, 1, 3, 2, 1, 4, 1, 2, 1, 3]
def baseStart_495858 : Nat := 118140960795 + 495858 * 2 ^ 59
def prefixEnd_495858 : Nat := 4983230072969 + 3 ^ 40 * 495858 * 2
def baseEnd_495858 : Nat := 254613490377226186994597

theorem tailTrace_495858 : CollatzResearch.WordTrace tailWord_495858 prefixEnd_495858 254613490377226186994597 := by
  unfold tailWord_495858
  simp only [CollatzResearch.WordTrace]
  refine ⟨4521356759399656662332057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12056951358399084432885485 4521356759399656662332057)
  ·
    refine ⟨3391017569549742496749043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4521356759399656662332057 3391017569549742496749043)
    ·
      refine ⟨5086526354324613745123565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3391017569549742496749043 5086526354324613745123565)
      ·
        refine ⟨1907447382871730154421337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5086526354324613745123565 1907447382871730154421337)
        ·
          refine ⟨1430585537153797615816003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1907447382871730154421337 1430585537153797615816003)
          ·
            refine ⟨2145878305730696423724005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1430585537153797615816003 2145878305730696423724005)
            ·
              refine ⟨402352182324505579448251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2145878305730696423724005 402352182324505579448251)
              ·
                refine ⟨603528273486758369172377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402352182324505579448251 603528273486758369172377)
                ·
                  refine ⟨452646205115068776879283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 603528273486758369172377 452646205115068776879283)
                  ·
                    refine ⟨678969307672603165318925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 452646205115068776879283 678969307672603165318925)
                    ·
                      refine ⟨254613490377226186994597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 678969307672603165318925 254613490377226186994597)
                      ·
                        rfl

theorem cell23_495858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_495858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495858 prefixEnd_495858 := by exact prefixLift 495858
  have htrace : WordTrace (prefixWord ++ tailWord_495858) baseStart_495858 baseEnd_495858 := by
    simpa [prefixWord, tailWord_495858, baseEnd_495858] using wordTrace_append hprefix tailTrace_495858
  have hstable : (prefixWord ++ tailWord_495858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495858).length < 2 ^ (prefixWord ++ tailWord_495858).sum := by decide
  have hdescent : baseEnd_495858 < baseStart_495858 := by decide
  rcases family_descends (prefixWord ++ tailWord_495858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495868 : List Nat := [2, 2, 2, 1, 4, 3, 1, 2, 1, 3, 2]
def baseStart_495868 : Nat := 118140960795 + 495868 * 2 ^ 59
def prefixEnd_495868 : Nat := 4983230072969 + 3 ^ 40 * 495868 * 2
def baseEnd_495868 : Nat := 254618625183771147869551

theorem tailTrace_495868 : CollatzResearch.WordTrace tailWord_495868 prefixEnd_495868 254618625183771147869551 := by
  unfold tailWord_495868
  simp only [CollatzResearch.WordTrace]
  refine ⟨9042895883781199178596129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12057194511708265571461505 9042895883781199178596129)
  ·
    refine ⟨6782171912835899383947097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9042895883781199178596129 6782171912835899383947097)
    ·
      refine ⟨5086628934626924537960323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6782171912835899383947097 5086628934626924537960323)
      ·
        refine ⟨7629943401940386806940485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5086628934626924537960323 7629943401940386806940485)
        ·
          refine ⟨1430614387863822526301341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7629943401940386806940485 1430614387863822526301341)
          ·
            refine ⟨536480395448933447363003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1430614387863822526301341 536480395448933447363003)
            ·
              refine ⟨804720593173400171044505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536480395448933447363003 804720593173400171044505)
              ·
                refine ⟨603540444880050128283379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 804720593173400171044505 603540444880050128283379)
                ·
                  refine ⟨905310667320075192425069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 603540444880050128283379 905310667320075192425069)
                  ·
                    refine ⟨339491500245028197159401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 905310667320075192425069 339491500245028197159401)
                    ·
                      refine ⟨254618625183771147869551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 339491500245028197159401 254618625183771147869551)
                      ·
                        rfl

theorem cell23_495868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 1, 3, 2].length) (baseStart_495868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495868 prefixEnd_495868 := by exact prefixLift 495868
  have htrace : WordTrace (prefixWord ++ tailWord_495868) baseStart_495868 baseEnd_495868 := by
    simpa [prefixWord, tailWord_495868, baseEnd_495868] using wordTrace_append hprefix tailTrace_495868
  have hstable : (prefixWord ++ tailWord_495868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495868).length < 2 ^ (prefixWord ++ tailWord_495868).sum := by decide
  have hdescent : baseEnd_495868 < baseStart_495868 := by decide
  rcases family_descends (prefixWord ++ tailWord_495868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495934 : List Nat := [4, 2, 1, 2, 1, 3, 1, 1, 1, 7]
def baseStart_495934 : Nat := 118140960795 + 495934 * 2 ^ 59
def prefixEnd_495934 : Nat := 4983230072969 + 3 ^ 40 * 495934 * 2
def baseEnd_495934 : Nat := 84884171635655963214749

theorem tailTrace_495934 : CollatzResearch.WordTrace tailWord_495934 prefixEnd_495934 84884171635655963214749 := by
  unfold tailWord_495934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2261024873165411453636857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12058799323548861086063237 2261024873165411453636857)
  ·
    refine ⟨1695768654874058590227643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2261024873165411453636857 1695768654874058590227643)
    ·
      refine ⟨2543652982311087885341465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1695768654874058590227643 2543652982311087885341465)
      ·
        refine ⟨1907739736733315914006099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2543652982311087885341465 1907739736733315914006099)
        ·
          refine ⟨2861609605099973871009149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1907739736733315914006099 2861609605099973871009149)
          ·
            refine ⟨1073103601912490201628431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2861609605099973871009149 1073103601912490201628431)
            ·
              refine ⟨1609655402868735302442647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1073103601912490201628431 1609655402868735302442647)
              ·
                refine ⟨2414483104303102953663971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1609655402868735302442647 2414483104303102953663971)
                ·
                  refine ⟨3621724656454654430495957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2414483104303102953663971 3621724656454654430495957)
                  ·
                    refine ⟨84884171635655963214749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3621724656454654430495957 84884171635655963214749)
                    ·
                      rfl

theorem cell23_495934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_495934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495934 prefixEnd_495934 := by exact prefixLift 495934
  have htrace : WordTrace (prefixWord ++ tailWord_495934) baseStart_495934 baseEnd_495934 := by
    simpa [prefixWord, tailWord_495934, baseEnd_495934] using wordTrace_append hprefix tailTrace_495934
  have hstable : (prefixWord ++ tailWord_495934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495934).length < 2 ^ (prefixWord ++ tailWord_495934).sum := by decide
  have hdescent : baseEnd_495934 < baseStart_495934 := by decide
  rcases family_descends (prefixWord ++ tailWord_495934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495954 : List Nat := [3, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4]
def baseStart_495954 : Nat := 118140960795 + 495954 * 2 ^ 59
def prefixEnd_495954 : Nat := 4983230072969 + 3 ^ 40 * 495954 * 2
def baseEnd_495954 : Nat := 254662784520057811394155

theorem tailTrace_495954 : CollatzResearch.WordTrace tailWord_495954 prefixEnd_495954 254662784520057811394155 := by
  unfold tailWord_495954
  simp only [CollatzResearch.WordTrace]
  refine ⟨4522232111312708761205729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12059285630167223363215277 4522232111312708761205729)
  ·
    refine ⟨3391674083484531570904297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4522232111312708761205729 3391674083484531570904297)
    ·
      refine ⟨2543755562613398678178223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3391674083484531570904297 2543755562613398678178223)
      ·
        refine ⟨3815633343920098017267335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2543755562613398678178223 3815633343920098017267335)
        ·
          refine ⟨5723450015880147025901003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3815633343920098017267335 5723450015880147025901003)
          ·
            refine ⟨8585175023820220538851505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5723450015880147025901003 8585175023820220538851505)
            ·
              refine ⟨6438881267865165404138629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8585175023820220538851505 6438881267865165404138629)
              ·
                refine ⟨1207290237724718513275993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6438881267865165404138629 1207290237724718513275993)
                ·
                  refine ⟨905467678293538884956995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1207290237724718513275993 905467678293538884956995)
                  ·
                    refine ⟨1358201517440308327435493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 905467678293538884956995 1358201517440308327435493)
                    ·
                      refine ⟨254662784520057811394155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1358201517440308327435493 254662784520057811394155)
                      ·
                        rfl

theorem cell23_495954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_495954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495954 prefixEnd_495954 := by exact prefixLift 495954
  have htrace : WordTrace (prefixWord ++ tailWord_495954) baseStart_495954 baseEnd_495954 := by
    simpa [prefixWord, tailWord_495954, baseEnd_495954] using wordTrace_append hprefix tailTrace_495954
  have hstable : (prefixWord ++ tailWord_495954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495954).length < 2 ^ (prefixWord ++ tailWord_495954).sum := by decide
  have hdescent : baseEnd_495954 < baseStart_495954 := by decide
  rcases family_descends (prefixWord ++ tailWord_495954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495966 : List Nat := [4, 4, 2, 1, 2, 1, 1, 1, 1, 4, 2]
def baseStart_495966 : Nat := 118140960795 + 495966 * 2 ^ 59
def prefixEnd_495966 : Nat := 4983230072969 + 3 ^ 40 * 495966 * 2
def baseEnd_495966 : Nat := 254668946287911764444101

theorem tailTrace_495966 : CollatzResearch.WordTrace tailWord_495966 prefixEnd_495966 254668946287911764444101 := by
  unfold tailWord_495966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2261170765150920136782469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12059577414138240729506501 2261170765150920136782469)
  ·
    refine ⟨423969518465797525646713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2261170765150920136782469 423969518465797525646713)
    ·
      refine ⟨317977138849348144235035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423969518465797525646713 317977138849348144235035)
      ·
        refine ⟨476965708274022216352553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317977138849348144235035 476965708274022216352553)
        ·
          refine ⟨357724281205516662264415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476965708274022216352553 357724281205516662264415)
          ·
            refine ⟨536586421808274993396623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357724281205516662264415 536586421808274993396623)
            ·
              refine ⟨804879632712412490094935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536586421808274993396623 804879632712412490094935)
              ·
                refine ⟨1207319449068618735142403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 804879632712412490094935 1207319449068618735142403)
                ·
                  refine ⟨1810979173602928102713605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1207319449068618735142403 1810979173602928102713605)
                  ·
                    refine ⟨339558595050549019258801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1810979173602928102713605 339558595050549019258801)
                    ·
                      refine ⟨254668946287911764444101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 339558595050549019258801 254668946287911764444101)
                      ·
                        rfl

theorem cell23_495966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_495966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_495966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_495966 prefixEnd_495966 := by exact prefixLift 495966
  have htrace : WordTrace (prefixWord ++ tailWord_495966) baseStart_495966 baseEnd_495966 := by
    simpa [prefixWord, tailWord_495966, baseEnd_495966] using wordTrace_append hprefix tailTrace_495966
  have hstable : (prefixWord ++ tailWord_495966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495966).length < 2 ^ (prefixWord ++ tailWord_495966).sum := by decide
  have hdescent : baseEnd_495966 < baseStart_495966 := by decide
  rcases family_descends (prefixWord ++ tailWord_495966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496031 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 4, 3, 2]
def baseStart_496031 : Nat := 118140960795 + 496031 * 2 ^ 59
def prefixEnd_496031 : Nat := 4983230072969 + 3 ^ 40 * 496031 * 2
def baseEnd_496031 : Nat := 254702322530454010131301

theorem tailTrace_496031 : CollatzResearch.WordTrace tailWord_496031 prefixEnd_496031 254702322530454010131301 := by
  unfold tailWord_496031
  simp only [CollatzResearch.WordTrace]
  refine ⟨18091736865971877195375947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12061157910647918130250631 18091736865971877195375947)
  ·
    refine ⟨27137605298957815793063921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18091736865971877195375947 27137605298957815793063921)
    ·
      refine ⟨20353203974218361844797941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27137605298957815793063921 20353203974218361844797941)
      ·
        refine ⟨1908112872582971422949807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20353203974218361844797941 1908112872582971422949807)
        ·
          refine ⟨2862169308874457134424711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1908112872582971422949807 2862169308874457134424711)
          ·
            refine ⟨4293253963311685701637067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2862169308874457134424711 4293253963311685701637067)
            ·
              refine ⟨6439880944967528552455601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4293253963311685701637067 6439880944967528552455601)
              ·
                refine ⟨4829910708725646414341701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6439880944967528552455601 4829910708725646414341701)
                ·
                  refine ⟨905608257886058702689069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4829910708725646414341701 905608257886058702689069)
                  ·
                    refine ⟨339603096707272013508401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 905608257886058702689069 339603096707272013508401)
                    ·
                      refine ⟨254702322530454010131301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 339603096707272013508401 254702322530454010131301)
                      ·
                        rfl

theorem cell23_496031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_496031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496031 prefixEnd_496031 := by exact prefixLift 496031
  have htrace : WordTrace (prefixWord ++ tailWord_496031) baseStart_496031 baseEnd_496031 := by
    simpa [prefixWord, tailWord_496031, baseEnd_496031] using wordTrace_append hprefix tailTrace_496031
  have hstable : (prefixWord ++ tailWord_496031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496031).length < 2 ^ (prefixWord ++ tailWord_496031).sum := by decide
  have hdescent : baseEnd_496031 < baseStart_496031 := by decide
  rcases family_descends (prefixWord ++ tailWord_496031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496042 : List Nat := [3, 1, 6, 1, 1, 1, 2, 1, 2, 2, 3]
def baseStart_496042 : Nat := 118140960795 + 496042 * 2 ^ 59
def prefixEnd_496042 : Nat := 4983230072969 + 3 ^ 40 * 496042 * 2
def baseEnd_496042 : Nat := 254707970817653467093751

theorem tailTrace_496042 : CollatzResearch.WordTrace tailWord_496042 prefixEnd_496042 254707970817653467093751 := by
  unfold tailWord_496042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4523034517233006518506595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12061425379288017382684253 4523034517233006518506595)
  ·
    refine ⟨6784551775849509777759893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4523034517233006518506595 6784551775849509777759893)
    ·
      refine ⟨318025864492945770832495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6784551775849509777759893 318025864492945770832495)
      ·
        refine ⟨477038796739418656248743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318025864492945770832495 477038796739418656248743)
        ·
          refine ⟨715558195109127984373115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477038796739418656248743 715558195109127984373115)
          ·
            refine ⟨1073337292663691976559673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715558195109127984373115 1073337292663691976559673)
            ·
              refine ⟨805002969497768982419755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1073337292663691976559673 805002969497768982419755)
              ·
                refine ⟨1207504454246653473629633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 805002969497768982419755 1207504454246653473629633)
                ·
                  refine ⟨905628340684990105222225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1207504454246653473629633 905628340684990105222225)
                  ·
                    refine ⟨679221255513742578916669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 905628340684990105222225 679221255513742578916669)
                    ·
                      refine ⟨254707970817653467093751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 679221255513742578916669 254707970817653467093751)
                      ·
                        rfl

theorem cell23_496042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_496042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496042 prefixEnd_496042 := by exact prefixLift 496042
  have htrace : WordTrace (prefixWord ++ tailWord_496042) baseStart_496042 baseEnd_496042 := by
    simpa [prefixWord, tailWord_496042, baseEnd_496042] using wordTrace_append hprefix tailTrace_496042
  have hstable : (prefixWord ++ tailWord_496042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496042).length < 2 ^ (prefixWord ++ tailWord_496042).sum := by decide
  have hdescent : baseEnd_496042 < baseStart_496042 := by decide
  rcases family_descends (prefixWord ++ tailWord_496042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496047 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 5]
def baseStart_496047 : Nat := 118140960795 + 496047 * 2 ^ 59
def prefixEnd_496047 : Nat := 4983230072969 + 3 ^ 40 * 496047 * 2
def baseEnd_496047 : Nat := 254710538220925947531227

theorem tailTrace_496047 : CollatzResearch.WordTrace tailWord_496047 prefixEnd_496047 254710538220925947531227 := by
  unfold tailWord_496047
  simp only [CollatzResearch.WordTrace]
  refine ⟨18092320433913911927958395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12061546955942607951972263 18092320433913911927958395)
  ·
    refine ⟨27138480650870867891937593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18092320433913911927958395 27138480650870867891937593)
    ·
      refine ⟨20353860488153150918953195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27138480650870867891937593 20353860488153150918953195)
      ·
        refine ⟨30530790732229726378429793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20353860488153150918953195 30530790732229726378429793)
        ·
          refine ⟨22898093049172294783822345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30530790732229726378429793 22898093049172294783822345)
          ·
            refine ⟨17173569786879221087866759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22898093049172294783822345 17173569786879221087866759)
            ·
              refine ⟨25760354680318831631800139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17173569786879221087866759 25760354680318831631800139)
              ·
                refine ⟨38640532020478247447700209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25760354680318831631800139 38640532020478247447700209)
                ·
                  refine ⟨28980399015358685585775157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38640532020478247447700209 28980399015358685585775157)
                  ·
                    refine ⟨2716912407689876773666421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28980399015358685585775157 2716912407689876773666421)
                    ·
                      refine ⟨254710538220925947531227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2716912407689876773666421 254710538220925947531227)
                      ·
                        rfl

theorem cell23_496047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 5].length) (baseStart_496047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496047 prefixEnd_496047 := by exact prefixLift 496047
  have htrace : WordTrace (prefixWord ++ tailWord_496047) baseStart_496047 baseEnd_496047 := by
    simpa [prefixWord, tailWord_496047, baseEnd_496047] using wordTrace_append hprefix tailTrace_496047
  have hstable : (prefixWord ++ tailWord_496047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496047).length < 2 ^ (prefixWord ++ tailWord_496047).sum := by decide
  have hdescent : baseEnd_496047 < baseStart_496047 := by decide
  rcases family_descends (prefixWord ++ tailWord_496047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496071 : List Nat := [1, 1, 4, 1, 1, 4, 1, 4, 2, 4]
def baseStart_496071 : Nat := 118140960795 + 496071 * 2 ^ 59
def prefixEnd_496071 : Nat := 4983230072969 + 3 ^ 40 * 496071 * 2
def baseEnd_496071 : Nat := 84907620585544617877039

theorem tailTrace_496071 : CollatzResearch.WordTrace tailWord_496071 prefixEnd_496071 84907620585544617877039 := by
  unfold tailWord_496071
  simp only [CollatzResearch.WordTrace]
  refine ⟨18093195785826964026832067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12062130523884642684554711 18093195785826964026832067)
  ·
    refine ⟨27139793678740446040248101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18093195785826964026832067 27139793678740446040248101)
    ·
      refine ⟨5088711314763833632546519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27139793678740446040248101 5088711314763833632546519)
      ·
        refine ⟨7633066972145750448819779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5088711314763833632546519 7633066972145750448819779)
        ·
          refine ⟨11449600458218625673229669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7633066972145750448819779 11449600458218625673229669)
          ·
            refine ⟨2146800085915992313730563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11449600458218625673229669 2146800085915992313730563)
            ·
              refine ⟨3220200128873988470595845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2146800085915992313730563 3220200128873988470595845)
              ·
                refine ⟨603787524163872838236721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3220200128873988470595845 603787524163872838236721)
                ·
                  refine ⟨452840643122904628677541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 603787524163872838236721 452840643122904628677541)
                  ·
                    refine ⟨84907620585544617877039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 452840643122904628677541 84907620585544617877039)
                    ·
                      rfl

theorem cell23_496071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_496071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496071 prefixEnd_496071 := by exact prefixLift 496071
  have htrace : WordTrace (prefixWord ++ tailWord_496071) baseStart_496071 baseEnd_496071 := by
    simpa [prefixWord, tailWord_496071, baseEnd_496071] using wordTrace_append hprefix tailTrace_496071
  have hstable : (prefixWord ++ tailWord_496071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496071).length < 2 ^ (prefixWord ++ tailWord_496071).sum := by decide
  have hdescent : baseEnd_496071 < baseStart_496071 := by decide
  rcases family_descends (prefixWord ++ tailWord_496071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496072 : List Nat := [2, 1, 3, 1, 3, 4, 2, 2, 1, 1, 3]
def baseStart_496072 : Nat := 118140960795 + 496072 * 2 ^ 59
def prefixEnd_496072 : Nat := 4983230072969 + 3 ^ 40 * 496072 * 2
def baseEnd_496072 : Nat := 254723375237288349718613

theorem tailTrace_496072 : CollatzResearch.WordTrace tailWord_496072 prefixEnd_496072 254723375237288349718613 := by
  unfold tailWord_496072
  simp only [CollatzResearch.WordTrace]
  refine ⟨9046616129411670598809235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12062154839215560798412313 9046616129411670598809235)
  ·
    refine ⟨13569924194117505898213853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9046616129411670598809235 13569924194117505898213853)
    ·
      refine ⟨5088721572794064711830195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13569924194117505898213853 5088721572794064711830195)
      ·
        refine ⟨7633082359191097067745293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5088721572794064711830195 7633082359191097067745293)
        ·
          refine ⟨2862405884696661400404485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7633082359191097067745293 2862405884696661400404485)
          ·
            refine ⟨536701103380624012575841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2862405884696661400404485 536701103380624012575841)
            ·
              refine ⟨402525827535468009431881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 536701103380624012575841 402525827535468009431881)
              ·
                refine ⟨301894370651601007073911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 402525827535468009431881 301894370651601007073911)
                ·
                  refine ⟨452841555977401510610867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 301894370651601007073911 452841555977401510610867)
                  ·
                    refine ⟨679262333966102265916301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 452841555977401510610867 679262333966102265916301)
                    ·
                      refine ⟨254723375237288349718613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 679262333966102265916301 254723375237288349718613)
                      ·
                        rfl

theorem cell23_496072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 2, 1, 1, 3].length) (baseStart_496072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496072 prefixEnd_496072 := by exact prefixLift 496072
  have htrace : WordTrace (prefixWord ++ tailWord_496072) baseStart_496072 baseEnd_496072 := by
    simpa [prefixWord, tailWord_496072, baseEnd_496072] using wordTrace_append hprefix tailTrace_496072
  have hstable : (prefixWord ++ tailWord_496072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496072).length < 2 ^ (prefixWord ++ tailWord_496072).sum := by decide
  have hdescent : baseEnd_496072 < baseStart_496072 := by decide
  rcases family_descends (prefixWord ++ tailWord_496072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496074 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 3, 2, 4]
def baseStart_496074 : Nat := 118140960795 + 496074 * 2 ^ 59
def prefixEnd_496074 : Nat := 4983230072969 + 3 ^ 40 * 496074 * 2
def baseEnd_496074 : Nat := 254724402198597341893603

theorem tailTrace_496074 : CollatzResearch.WordTrace tailWord_496074 prefixEnd_496074 254724402198597341893603 := by
  unfold tailWord_496074
  simp only [CollatzResearch.WordTrace]
  refine ⟨4523326301204023884797819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12062203469877397026127517 4523326301204023884797819)
  ·
    refine ⟨6784989451806035827196729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4523326301204023884797819 6784989451806035827196729)
    ·
      refine ⟨5088742088854526870397547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6784989451806035827196729 5088742088854526870397547)
      ·
        refine ⟨7633113133281790305596321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5088742088854526870397547 7633113133281790305596321)
        ·
          refine ⟨5724834849961342729197241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7633113133281790305596321 5724834849961342729197241)
          ·
            refine ⟨4293626137471007046897931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5724834849961342729197241 4293626137471007046897931)
            ·
              refine ⟨6440439206206510570346897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4293626137471007046897931 6440439206206510570346897)
              ·
                refine ⟨4830329404654882927760173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6440439206206510570346897 4830329404654882927760173)
                ·
                  refine ⟨1811373526745581097910065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4830329404654882927760173 1811373526745581097910065)
                  ·
                    refine ⟨1358530145059185823432549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1811373526745581097910065 1358530145059185823432549)
                    ·
                      refine ⟨254724402198597341893603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1358530145059185823432549 254724402198597341893603)
                      ·
                        rfl

theorem cell23_496074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_496074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496074 prefixEnd_496074 := by exact prefixLift 496074
  have htrace : WordTrace (prefixWord ++ tailWord_496074) baseStart_496074 baseEnd_496074 := by
    simpa [prefixWord, tailWord_496074, baseEnd_496074] using wordTrace_append hprefix tailTrace_496074
  have hstable : (prefixWord ++ tailWord_496074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496074).length < 2 ^ (prefixWord ++ tailWord_496074).sum := by decide
  have hdescent : baseEnd_496074 < baseStart_496074 := by decide
  rcases family_descends (prefixWord ++ tailWord_496074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496078 : List Nat := [4, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2]
def baseStart_496078 : Nat := 118140960795 + 496078 * 2 ^ 59
def prefixEnd_496078 : Nat := 4983230072969 + 3 ^ 40 * 496078 * 2
def baseEnd_496078 : Nat := 254726456121215326243585

theorem tailTrace_496078 : CollatzResearch.WordTrace tailWord_496078 prefixEnd_496078 254726456121215326243585 := by
  unfold tailWord_496078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2261681387100200527792111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12062300731201069481557925 2261681387100200527792111)
  ·
    refine ⟨3392522080650300791688167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2261681387100200527792111 3392522080650300791688167)
    ·
      refine ⟨5088783120975451187532251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3392522080650300791688167 5088783120975451187532251)
      ·
        refine ⟨7633174681463176781298377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5088783120975451187532251 7633174681463176781298377)
        ·
          refine ⟨5724881011097382585973783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7633174681463176781298377 5724881011097382585973783)
          ·
            refine ⟨8587321516646073878960675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5724881011097382585973783 8587321516646073878960675)
            ·
              refine ⟨12880982274969110818441013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8587321516646073878960675 12880982274969110818441013)
              ·
                refine ⟨1207592088278354139228845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12880982274969110818441013 1207592088278354139228845)
                ·
                  refine ⟨452847033104382802210817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1207592088278354139228845 452847033104382802210817)
                  ·
                    refine ⟨339635274828287101658113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 452847033104382802210817 339635274828287101658113)
                    ·
                      refine ⟨254726456121215326243585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 339635274828287101658113 254726456121215326243585)
                      ·
                        rfl

theorem cell23_496078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2].length) (baseStart_496078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496078 prefixEnd_496078 := by exact prefixLift 496078
  have htrace : WordTrace (prefixWord ++ tailWord_496078) baseStart_496078 baseEnd_496078 := by
    simpa [prefixWord, tailWord_496078, baseEnd_496078] using wordTrace_append hprefix tailTrace_496078
  have hstable : (prefixWord ++ tailWord_496078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496078).length < 2 ^ (prefixWord ++ tailWord_496078).sum := by decide
  have hdescent : baseEnd_496078 < baseStart_496078 := by decide
  rcases family_descends (prefixWord ++ tailWord_496078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496111 : List Nat := [1, 1, 2, 1, 4, 1, 1, 4, 4, 1, 3]
def baseStart_496111 : Nat := 118140960795 + 496111 * 2 ^ 59
def prefixEnd_496111 : Nat := 4983230072969 + 3 ^ 40 * 496111 * 2
def baseEnd_496111 : Nat := 254743400982813697130933

theorem tailTrace_496111 : CollatzResearch.WordTrace tailWord_496111 prefixEnd_496111 254743400982813697130933 := by
  unfold tailWord_496111
  simp only [CollatzResearch.WordTrace]
  refine ⟨18094654705682050858288187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12063103137121367238858791 18094654705682050858288187)
  ·
    refine ⟨27141982058523076287432281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18094654705682050858288187 27141982058523076287432281)
    ·
      refine ⟨20356486543892307215574211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27141982058523076287432281 20356486543892307215574211)
      ·
        refine ⟨30534729815838460823361317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20356486543892307215574211 30534729815838460823361317)
        ·
          refine ⟨5725261840469711404380247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30534729815838460823361317 5725261840469711404380247)
          ·
            refine ⟨8587892760704567106570371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5725261840469711404380247 8587892760704567106570371)
            ·
              refine ⟨12881839141056850659855557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8587892760704567106570371 12881839141056850659855557)
              ·
                refine ⟨2415344838948159498722917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12881839141056850659855557 2415344838948159498722917)
                ·
                  refine ⟨452877157302779906010547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2415344838948159498722917 452877157302779906010547)
                  ·
                    refine ⟨679315735954169859015821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 452877157302779906010547 679315735954169859015821)
                    ·
                      refine ⟨254743400982813697130933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 679315735954169859015821 254743400982813697130933)
                      ·
                        rfl

theorem cell23_496111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 4, 1, 3].length) (baseStart_496111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496111 prefixEnd_496111 := by exact prefixLift 496111
  have htrace : WordTrace (prefixWord ++ tailWord_496111) baseStart_496111 baseEnd_496111 := by
    simpa [prefixWord, tailWord_496111, baseEnd_496111] using wordTrace_append hprefix tailTrace_496111
  have hstable : (prefixWord ++ tailWord_496111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496111).length < 2 ^ (prefixWord ++ tailWord_496111).sum := by decide
  have hdescent : baseEnd_496111 < baseStart_496111 := by decide
  rcases family_descends (prefixWord ++ tailWord_496111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496184 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 1, 2, 7]
def baseStart_496184 : Nat := 118140960795 + 496184 * 2 ^ 59
def prefixEnd_496184 : Nat := 4983230072969 + 3 ^ 40 * 496184 * 2
def baseEnd_496184 : Nat := 254780885070591911518097

theorem tailTrace_496184 : CollatzResearch.WordTrace tailWord_496184 prefixEnd_496184 254780885070591911518097 := by
  unfold tailWord_496184
  simp only [CollatzResearch.WordTrace]
  refine ⟨9048658617208792162847803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12064878156278389550463737 9048658617208792162847803)
  ·
    refine ⟨13572987925813188244271705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9048658617208792162847803 13572987925813188244271705)
    ·
      refine ⟨10179740944359891183203779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13572987925813188244271705 10179740944359891183203779)
      ·
        refine ⟨15269611416539836774805669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10179740944359891183203779 15269611416539836774805669)
        ·
          refine ⟨2863052140601219395276063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15269611416539836774805669 2863052140601219395276063)
          ·
            refine ⟨4294578210901829092914095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2863052140601219395276063 4294578210901829092914095)
            ·
              refine ⟨6441867316352743639371143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4294578210901829092914095 6441867316352743639371143)
              ·
                refine ⟨9662800974529115459056715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6441867316352743639371143 9662800974529115459056715)
                ·
                  refine ⟨14494201461793673188585073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9662800974529115459056715 14494201461793673188585073)
                  ·
                    refine ⟨10870651096345254891438805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14494201461793673188585073 10870651096345254891438805)
                    ·
                      refine ⟨254780885070591911518097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 10870651096345254891438805 254780885070591911518097)
                      ·
                        rfl

theorem cell23_496184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_496184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496184 prefixEnd_496184 := by exact prefixLift 496184
  have htrace : WordTrace (prefixWord ++ tailWord_496184) baseStart_496184 baseEnd_496184 := by
    simpa [prefixWord, tailWord_496184, baseEnd_496184] using wordTrace_append hprefix tailTrace_496184
  have hstable : (prefixWord ++ tailWord_496184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496184).length < 2 ^ (prefixWord ++ tailWord_496184).sum := by decide
  have hdescent : baseEnd_496184 < baseStart_496184 := by decide
  rcases family_descends (prefixWord ++ tailWord_496184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496185 : List Nat := [1, 2, 1, 5, 1, 1, 2, 4, 2, 2, 2]
def baseStart_496185 : Nat := 118140960795 + 496185 * 2 ^ 59
def prefixEnd_496185 : Nat := 4983230072969 + 3 ^ 40 * 496185 * 2
def baseEnd_496185 : Nat := 254781398551246407605593

theorem tailTrace_496185 : CollatzResearch.WordTrace tailWord_496185 prefixEnd_496185 254781398551246407605593 := by
  unfold tailWord_496185
  simp only [CollatzResearch.WordTrace]
  refine ⟨18097353707413961496482009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12064902471609307664321339 18097353707413961496482009)
  ·
    refine ⟨13573015280560471122361507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18097353707413961496482009 13573015280560471122361507)
    ·
      refine ⟨20359522920840706683542261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13573015280560471122361507 20359522920840706683542261)
      ·
        refine ⟨1908705273828816251582087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20359522920840706683542261 1908705273828816251582087)
        ·
          refine ⟨2863057910743224377373131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1908705273828816251582087 2863057910743224377373131)
          ·
            refine ⟨4294586866114836566059697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2863057910743224377373131 4294586866114836566059697)
            ·
              refine ⟨3220940149586127424544773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4294586866114836566059697 3220940149586127424544773)
              ·
                refine ⟨603926278047398892102145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3220940149586127424544773 603926278047398892102145)
                ·
                  refine ⟨452944708535549169076609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 603926278047398892102145 452944708535549169076609)
                  ·
                    refine ⟨339708531401661876807457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 452944708535549169076609 339708531401661876807457)
                    ·
                      refine ⟨254781398551246407605593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 339708531401661876807457 254781398551246407605593)
                      ·
                        rfl

theorem cell23_496185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_496185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496185 prefixEnd_496185 := by exact prefixLift 496185
  have htrace : WordTrace (prefixWord ++ tailWord_496185) baseStart_496185 baseEnd_496185 := by
    simpa [prefixWord, tailWord_496185, baseEnd_496185] using wordTrace_append hprefix tailTrace_496185
  have hstable : (prefixWord ++ tailWord_496185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496185).length < 2 ^ (prefixWord ++ tailWord_496185).sum := by decide
  have hdescent : baseEnd_496185 < baseStart_496185 := by decide
  rcases family_descends (prefixWord ++ tailWord_496185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496202 : List Nat := [3, 1, 2, 1, 1, 4, 4, 1, 2, 2, 2]
def baseStart_496202 : Nat := 118140960795 + 496202 * 2 ^ 59
def prefixEnd_496202 : Nat := 4983230072969 + 3 ^ 40 * 496202 * 2
def baseEnd_496202 : Nat := 254790127722372841093015

theorem tailTrace_496202 : CollatzResearch.WordTrace tailWord_496202 prefixEnd_496202 254790127722372841093015 := by
  unfold tailWord_496202
  simp only [CollatzResearch.WordTrace]
  refine ⟨4524493437088093349962715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12065315832234915599900573 4524493437088093349962715)
  ·
    refine ⟨6786740155632140024944073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4524493437088093349962715 6786740155632140024944073)
    ·
      refine ⟨5090055116724105018708055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6786740155632140024944073 5090055116724105018708055)
      ·
        refine ⟨7635082675086157528062083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5090055116724105018708055 7635082675086157528062083)
        ·
          refine ⟨11452624012629236292093125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7635082675086157528062083 11452624012629236292093125)
          ·
            refine ⟨2147367002367981804767461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11452624012629236292093125 2147367002367981804767461)
            ·
              refine ⟨402631312943996588393899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2147367002367981804767461 402631312943996588393899)
              ·
                refine ⟨603946969415994882590849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402631312943996588393899 603946969415994882590849)
                ·
                  refine ⟨452960227061996161943137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 603946969415994882590849 452960227061996161943137)
                  ·
                    refine ⟨339720170296497121457353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 452960227061996161943137 339720170296497121457353)
                    ·
                      refine ⟨254790127722372841093015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 339720170296497121457353 254790127722372841093015)
                      ·
                        rfl

theorem cell23_496202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 2, 2, 2].length) (baseStart_496202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496202 prefixEnd_496202 := by exact prefixLift 496202
  have htrace : WordTrace (prefixWord ++ tailWord_496202) baseStart_496202 baseEnd_496202 := by
    simpa [prefixWord, tailWord_496202, baseEnd_496202] using wordTrace_append hprefix tailTrace_496202
  have hstable : (prefixWord ++ tailWord_496202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496202).length < 2 ^ (prefixWord ++ tailWord_496202).sum := by decide
  have hdescent : baseEnd_496202 < baseStart_496202 := by decide
  rcases family_descends (prefixWord ++ tailWord_496202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496238 : List Nat := [4, 1, 2, 2, 2, 1, 2, 2, 2, 5]
def baseStart_496238 : Nat := 118140960795 + 496238 * 2 ^ 59
def prefixEnd_496238 : Nat := 4983230072969 + 3 ^ 40 * 496238 * 2
def baseEnd_496238 : Nat := 84936204341978233414283

theorem tailTrace_496238 : CollatzResearch.WordTrace tailWord_496238 prefixEnd_496238 84936204341978233414283 := by
  unfold tailWord_496238
  simp only [CollatzResearch.WordTrace]
  refine ⟨2262410847027743943520171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12066191184147967698774245 2262410847027743943520171)
  ·
    refine ⟨3393616270541615915280257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2262410847027743943520171 3393616270541615915280257)
    ·
      refine ⟨2545212202906211936460193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3393616270541615915280257 2545212202906211936460193)
      ·
        refine ⟨1908909152179658952345145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2545212202906211936460193 1908909152179658952345145)
        ·
          refine ⟨1431681864134744214258859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1908909152179658952345145 1431681864134744214258859)
          ·
            refine ⟨2147522796202116321388289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1431681864134744214258859 2147522796202116321388289)
            ·
              refine ⟨1610642097151587241041217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2147522796202116321388289 1610642097151587241041217)
              ·
                refine ⟨1207981572863690430780913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1610642097151587241041217 1207981572863690430780913)
                ·
                  refine ⟨905986179647767823085685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1207981572863690430780913 905986179647767823085685)
                  ·
                    refine ⟨84936204341978233414283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 905986179647767823085685 84936204341978233414283)
                    ·
                      rfl

theorem cell23_496238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_496238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496238 prefixEnd_496238 := by exact prefixLift 496238
  have htrace : WordTrace (prefixWord ++ tailWord_496238) baseStart_496238 baseEnd_496238 := by
    simpa [prefixWord, tailWord_496238, baseEnd_496238] using wordTrace_append hprefix tailTrace_496238
  have hstable : (prefixWord ++ tailWord_496238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496238).length < 2 ^ (prefixWord ++ tailWord_496238).sum := by decide
  have hdescent : baseEnd_496238 < baseStart_496238 := by decide
  rcases family_descends (prefixWord ++ tailWord_496238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496242 : List Nat := [3, 2, 1, 2, 4, 2, 2, 2, 5]
def baseStart_496242 : Nat := 118140960795 + 496242 * 2 ^ 59
def prefixEnd_496242 : Nat := 4983230072969 + 3 ^ 40 * 496242 * 2
def baseEnd_496242 : Nat := 28312296327616964954759

theorem tailTrace_496242 : CollatzResearch.WordTrace tailWord_496242 prefixEnd_496242 28312296327616964954759 := by
  unfold tailWord_496242
  simp only [CollatzResearch.WordTrace]
  refine ⟨4524858167051865057826745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12066288445471640154204653 4524858167051865057826745)
  ·
    refine ⟨3393643625288898793370059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4524858167051865057826745 3393643625288898793370059)
    ·
      refine ⟨5090465437933348190055089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3393643625288898793370059 5090465437933348190055089)
      ·
        refine ⟨3817849078450011142541317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5090465437933348190055089 3817849078450011142541317)
        ·
          refine ⟨715846702209377089226497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3817849078450011142541317 715846702209377089226497)
          ·
            refine ⟨536885026657032816919873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 715846702209377089226497 536885026657032816919873)
            ·
              refine ⟨402663769992774612689905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 536885026657032816919873 402663769992774612689905)
              ·
                refine ⟨301997827494580959517429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 402663769992774612689905 301997827494580959517429)
                ·
                  refine ⟨28312296327616964954759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 301997827494580959517429 28312296327616964954759)
                  ·
                    rfl

theorem cell23_496242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 2, 5].length) (baseStart_496242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496242 prefixEnd_496242 := by exact prefixLift 496242
  have htrace : WordTrace (prefixWord ++ tailWord_496242) baseStart_496242 baseEnd_496242 := by
    simpa [prefixWord, tailWord_496242, baseEnd_496242] using wordTrace_append hprefix tailTrace_496242
  have hstable : (prefixWord ++ tailWord_496242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496242).length < 2 ^ (prefixWord ++ tailWord_496242).sum := by decide
  have hdescent : baseEnd_496242 < baseStart_496242 := by decide
  rcases family_descends (prefixWord ++ tailWord_496242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496285 : List Nat := [1, 4, 2, 1, 1, 1, 3, 5, 1, 4]
def baseStart_496285 : Nat := 118140960795 + 496285 * 2 ^ 59
def prefixEnd_496285 : Nat := 4983230072969 + 3 ^ 40 * 496285 * 2
def baseEnd_496285 : Nat := 84944248872232005451711

theorem tailTrace_496285 : CollatzResearch.WordTrace tailWord_496285 prefixEnd_496285 84944248872232005451711 := by
  unfold tailWord_496285
  simp only [CollatzResearch.WordTrace]
  refine ⟨18101001007051678575122309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12067334004701119050081539 18101001007051678575122309)
  ·
    refine ⟨3393937688822189732835433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18101001007051678575122309 3393937688822189732835433)
    ·
      refine ⟨2545453266616642299626575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3393937688822189732835433 2545453266616642299626575)
      ·
        refine ⟨3818179899924963449439863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2545453266616642299626575 3818179899924963449439863)
        ·
          refine ⟨5727269849887445174159795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3818179899924963449439863 5727269849887445174159795)
          ·
            refine ⟨8590904774831167761239693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5727269849887445174159795 8590904774831167761239693)
            ·
              refine ⟨3221589290561687910464885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8590904774831167761239693 3221589290561687910464885)
              ·
                refine ⟨302023995990158241606083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3221589290561687910464885 302023995990158241606083)
                ·
                  refine ⟨453035993985237362409125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302023995990158241606083 453035993985237362409125)
                  ·
                    refine ⟨84944248872232005451711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 453035993985237362409125 84944248872232005451711)
                    ·
                      rfl

theorem cell23_496285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_496285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496285 prefixEnd_496285 := by exact prefixLift 496285
  have htrace : WordTrace (prefixWord ++ tailWord_496285) baseStart_496285 baseEnd_496285 := by
    simpa [prefixWord, tailWord_496285, baseEnd_496285] using wordTrace_append hprefix tailTrace_496285
  have hstable : (prefixWord ++ tailWord_496285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496285).length < 2 ^ (prefixWord ++ tailWord_496285).sum := by decide
  have hdescent : baseEnd_496285 < baseStart_496285 := by decide
  rcases family_descends (prefixWord ++ tailWord_496285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496302 : List Nat := [4, 1, 4, 1, 1, 2, 2, 1, 3, 4]
def baseStart_496302 : Nat := 118140960795 + 496302 * 2 ^ 59
def prefixEnd_496302 : Nat := 4983230072969 + 3 ^ 40 * 496302 * 2
def baseEnd_496302 : Nat := 84947158595940816614185

theorem tailTrace_496302 : CollatzResearch.WordTrace tailWord_496302 prefixEnd_496302 84947158595940816614185 := by
  unfold tailWord_496302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2262702630998761309811395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12067747365326726985660773 2262702630998761309811395)
  ·
    refine ⟨3394053946498141964717093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2262702630998761309811395 3394053946498141964717093)
    ·
      refine ⟨636385114968401618384455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3394053946498141964717093 636385114968401618384455)
      ·
        refine ⟨954577672452602427576683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636385114968401618384455 954577672452602427576683)
        ·
          refine ⟨1431866508678903641365025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 954577672452602427576683 1431866508678903641365025)
          ·
            refine ⟨1073899881509177731023769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1431866508678903641365025 1073899881509177731023769)
            ·
              refine ⟨805424911131883298267827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1073899881509177731023769 805424911131883298267827)
              ·
                refine ⟨1208137366697824947401741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 805424911131883298267827 1208137366697824947401741)
                ·
                  refine ⟨453051512511684355275653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1208137366697824947401741 453051512511684355275653)
                  ·
                    refine ⟨84947158595940816614185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 453051512511684355275653 84947158595940816614185)
                    ·
                      rfl

theorem cell23_496302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_496302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496302 prefixEnd_496302 := by exact prefixLift 496302
  have htrace : WordTrace (prefixWord ++ tailWord_496302) baseStart_496302 baseEnd_496302 := by
    simpa [prefixWord, tailWord_496302, baseEnd_496302] using wordTrace_append hprefix tailTrace_496302
  have hstable : (prefixWord ++ tailWord_496302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496302).length < 2 ^ (prefixWord ++ tailWord_496302).sum := by decide
  have hdescent : baseEnd_496302 < baseStart_496302 := by decide
  rcases family_descends (prefixWord ++ tailWord_496302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496328 : List Nat := [2, 1, 3, 1, 2, 3, 1, 4, 1, 5]
def baseStart_496328 : Nat := 118140960795 + 496328 * 2 ^ 59
def prefixEnd_496328 : Nat := 4983230072969 + 3 ^ 40 * 496328 * 2
def baseEnd_496328 : Nat := 84951608761613116039145

theorem tailTrace_496328 : CollatzResearch.WordTrace tailWord_496328 prefixEnd_496328 84951608761613116039145 := by
  unfold tailWord_496328
  simp only [CollatzResearch.WordTrace]
  refine ⟨9051284672947948459468819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12068379563930597945958425 9051284672947948459468819)
  ·
    refine ⟨13576927009421922689203229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9051284672947948459468819 13576927009421922689203229)
    ·
      refine ⟨5091347628533221008451211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13576927009421922689203229 5091347628533221008451211)
      ·
        refine ⟨7637021442799831512676817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5091347628533221008451211 7637021442799831512676817)
        ·
          refine ⟨5727766082099873634507613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7637021442799831512676817 5727766082099873634507613)
          ·
            refine ⟨2147912280787452612940355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5727766082099873634507613 2147912280787452612940355)
            ·
              refine ⟨3221868421181178919410533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2147912280787452612940355 3221868421181178919410533)
              ·
                refine ⟨604100328971471047389475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3221868421181178919410533 604100328971471047389475)
                ·
                  refine ⟨906150493457206571084213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 604100328971471047389475 906150493457206571084213)
                  ·
                    refine ⟨84951608761613116039145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 906150493457206571084213 84951608761613116039145)
                    ·
                      rfl

theorem cell23_496328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_496328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496328 prefixEnd_496328 := by exact prefixLift 496328
  have htrace : WordTrace (prefixWord ++ tailWord_496328) baseStart_496328 baseEnd_496328 := by
    simpa [prefixWord, tailWord_496328, baseEnd_496328] using wordTrace_append hprefix tailTrace_496328
  have hstable : (prefixWord ++ tailWord_496328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496328).length < 2 ^ (prefixWord ++ tailWord_496328).sum := by decide
  have hdescent : baseEnd_496328 < baseStart_496328 := by decide
  rcases family_descends (prefixWord ++ tailWord_496328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496361 : List Nat := [1, 2, 1, 1, 1, 2, 5, 2, 1, 1, 6]
def baseStart_496361 : Nat := 118140960795 + 496361 * 2 ^ 59
def prefixEnd_496361 : Nat := 4983230072969 + 3 ^ 40 * 496361 * 2
def baseEnd_496361 : Nat := 254871771146437719004783

theorem tailTrace_496361 : CollatzResearch.WordTrace tailWord_496361 prefixEnd_496361 254871771146437719004783 := by
  unfold tailWord_496361
  simp only [CollatzResearch.WordTrace]
  refine ⟨18103772954776343554888937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12069181969850895703259291 18103772954776343554888937)
  ·
    refine ⟨13577829716082257666166703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18103772954776343554888937 13577829716082257666166703)
    ·
      refine ⟨20366744574123386499250055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13577829716082257666166703 20366744574123386499250055)
      ·
        refine ⟨30550116861185079748875083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20366744574123386499250055 30550116861185079748875083)
        ·
          refine ⟨45825175291777619623312625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30550116861185079748875083 45825175291777619623312625)
          ·
            refine ⟨34368881468833214717484469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45825175291777619623312625 34368881468833214717484469)
            ·
              refine ⟨3222082637703113879764169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34368881468833214717484469 3222082637703113879764169)
              ·
                refine ⟨2416561978277335409823127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3222082637703113879764169 2416561978277335409823127)
                ·
                  refine ⟨3624842967416003114734691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2416561978277335409823127 3624842967416003114734691)
                  ·
                    refine ⟨5437264451124004672102037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3624842967416003114734691 5437264451124004672102037)
                    ·
                      refine ⟨254871771146437719004783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5437264451124004672102037 254871771146437719004783)
                      ·
                        rfl

theorem cell23_496361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 1, 6].length) (baseStart_496361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496361 prefixEnd_496361 := by exact prefixLift 496361
  have htrace : WordTrace (prefixWord ++ tailWord_496361) baseStart_496361 baseEnd_496361 := by
    simpa [prefixWord, tailWord_496361, baseEnd_496361] using wordTrace_append hprefix tailTrace_496361
  have hstable : (prefixWord ++ tailWord_496361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496361).length < 2 ^ (prefixWord ++ tailWord_496361).sum := by decide
  have hdescent : baseEnd_496361 < baseStart_496361 := by decide
  rcases family_descends (prefixWord ++ tailWord_496361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496368 : List Nat := [2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 3]
def baseStart_496368 : Nat := 118140960795 + 496368 * 2 ^ 59
def prefixEnd_496368 : Nat := 4983230072969 + 3 ^ 40 * 496368 * 2
def baseEnd_496368 : Nat := 254875365511019191617251

theorem tailTrace_496368 : CollatzResearch.WordTrace tailWord_496368 prefixEnd_496368 254875365511019191617251 := by
  unfold tailWord_496368
  simp only [CollatzResearch.WordTrace]
  refine ⟨9052014132875491875196879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12069352177167322500262505 9052014132875491875196879)
  ·
    refine ⟨13578021199313237812795319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9052014132875491875196879 13578021199313237812795319)
    ·
      refine ⟨20367031798969856719192979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13578021199313237812795319 20367031798969856719192979)
      ·
        refine ⟨30550547698454785078789469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20367031798969856719192979 30550547698454785078789469)
        ·
          refine ⟨11456455386920544404546051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30550547698454785078789469 11456455386920544404546051)
          ·
            refine ⟨17184683080380816606819077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11456455386920544404546051 17184683080380816606819077)
            ·
              refine ⟨3222128077571403113778577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17184683080380816606819077 3222128077571403113778577)
              ·
                refine ⟨2416596058178552335333933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3222128077571403113778577 2416596058178552335333933)
                ·
                  refine ⟨906223521816957125750225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2416596058178552335333933 906223521816957125750225)
                  ·
                    refine ⟨679667641362717844312669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 906223521816957125750225 679667641362717844312669)
                    ·
                      refine ⟨254875365511019191617251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 679667641362717844312669 254875365511019191617251)
                      ·
                        rfl

theorem cell23_496368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 3].length) (baseStart_496368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496368 prefixEnd_496368 := by exact prefixLift 496368
  have htrace : WordTrace (prefixWord ++ tailWord_496368) baseStart_496368 baseEnd_496368 := by
    simpa [prefixWord, tailWord_496368, baseEnd_496368] using wordTrace_append hprefix tailTrace_496368
  have hstable : (prefixWord ++ tailWord_496368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496368).length < 2 ^ (prefixWord ++ tailWord_496368).sum := by decide
  have hdescent : baseEnd_496368 < baseStart_496368 := by decide
  rcases family_descends (prefixWord ++ tailWord_496368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496382 : List Nat := [4, 2, 2, 1, 2, 1, 3, 2, 1, 1, 4]
def baseStart_496382 : Nat := 118140960795 + 496382 * 2 ^ 59
def prefixEnd_496382 : Nat := 4983230072969 + 3 ^ 40 * 496382 * 2
def baseEnd_496382 : Nat := 254882554240182136842187

theorem tailTrace_496382 : CollatzResearch.WordTrace tailWord_496382 prefixEnd_496382 254882554240182136842187 := by
  unfold tailWord_496382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2263067360962533017675425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12069692591800176094268933 2263067360962533017675425)
  ·
    refine ⟨1697300520721899763256569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2263067360962533017675425 1697300520721899763256569)
    ·
      refine ⟨1272975390541424822442427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1697300520721899763256569 1272975390541424822442427)
      ·
        refine ⟨1909463085812137233663641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1272975390541424822442427 1909463085812137233663641)
        ·
          refine ⟨1432097314359102925247731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1909463085812137233663641 1432097314359102925247731)
          ·
            refine ⟨2148145971538654387871597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1432097314359102925247731 2148145971538654387871597)
            ·
              refine ⟨805554739326995395451849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2148145971538654387871597 805554739326995395451849)
              ·
                refine ⟨604166054495246546588887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 805554739326995395451849 604166054495246546588887)
                ·
                  refine ⟨906249081742869819883331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 604166054495246546588887 906249081742869819883331)
                  ·
                    refine ⟨1359373622614304729824997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 906249081742869819883331 1359373622614304729824997)
                    ·
                      refine ⟨254882554240182136842187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1359373622614304729824997 254882554240182136842187)
                      ·
                        rfl

theorem cell23_496382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_496382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496382 prefixEnd_496382 := by exact prefixLift 496382
  have htrace : WordTrace (prefixWord ++ tailWord_496382) baseStart_496382 baseEnd_496382 := by
    simpa [prefixWord, tailWord_496382, baseEnd_496382] using wordTrace_append hprefix tailTrace_496382
  have hstable : (prefixWord ++ tailWord_496382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496382).length < 2 ^ (prefixWord ++ tailWord_496382).sum := by decide
  have hdescent : baseEnd_496382 < baseStart_496382 := by decide
  rcases family_descends (prefixWord ++ tailWord_496382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496416 : List Nat := [2, 1, 1, 5, 1, 2, 4, 2, 1, 2, 2]
def baseStart_496416 : Nat := 118140960795 + 496416 * 2 ^ 59
def prefixEnd_496416 : Nat := 4983230072969 + 3 ^ 40 * 496416 * 2
def baseEnd_496416 : Nat := 254900012582435003817031

theorem tailTrace_496416 : CollatzResearch.WordTrace tailWord_496416 prefixEnd_496416 254900012582435003817031 := by
  unfold tailWord_496416
  simp only [CollatzResearch.WordTrace]
  refine ⟨9052889484788543974070551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12070519313051391965427401 9052889484788543974070551)
  ·
    refine ⟨13579334227182815961105827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9052889484788543974070551 13579334227182815961105827)
    ·
      refine ⟨20369001340774223941658741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13579334227182815961105827 20369001340774223941658741)
      ·
        refine ⟨1909593875697583494530507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20369001340774223941658741 1909593875697583494530507)
        ·
          refine ⟨2864390813546375241795761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1909593875697583494530507 2864390813546375241795761)
          ·
            refine ⟨2148293110159781431346821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2864390813546375241795761 2148293110159781431346821)
            ·
              refine ⟨402804958154959018377529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2148293110159781431346821 402804958154959018377529)
              ·
                refine ⟨302103718616219263783147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 402804958154959018377529 302103718616219263783147)
                ·
                  refine ⟨453155577924328895674721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302103718616219263783147 453155577924328895674721)
                  ·
                    refine ⟨339866683443246671756041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 453155577924328895674721 339866683443246671756041)
                    ·
                      refine ⟨254900012582435003817031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 339866683443246671756041 254900012582435003817031)
                      ·
                        rfl

theorem cell23_496416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_496416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496416 prefixEnd_496416 := by exact prefixLift 496416
  have htrace : WordTrace (prefixWord ++ tailWord_496416) baseStart_496416 baseEnd_496416 := by
    simpa [prefixWord, tailWord_496416, baseEnd_496416] using wordTrace_append hprefix tailTrace_496416
  have hstable : (prefixWord ++ tailWord_496416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496416).length < 2 ^ (prefixWord ++ tailWord_496416).sum := by decide
  have hdescent : baseEnd_496416 < baseStart_496416 := by decide
  rcases family_descends (prefixWord ++ tailWord_496416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496418 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 2, 7]
def baseStart_496418 : Nat := 118140960795 + 496418 * 2 ^ 59
def prefixEnd_496418 : Nat := 4983230072969 + 3 ^ 40 * 496418 * 2
def baseEnd_496418 : Nat := 84967013181247998664007

theorem tailTrace_496418 : CollatzResearch.WordTrace tailWord_496418 prefixEnd_496418 84967013181247998664007 := by
  unfold tailWord_496418
  simp only [CollatzResearch.WordTrace]
  refine ⟨4526462978892460572428477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12070567943713228193142605 4526462978892460572428477)
  ·
    refine ⟨1697423617084672714660679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4526462978892460572428477 1697423617084672714660679)
    ·
      refine ⟨2546135425627009071991019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1697423617084672714660679 2546135425627009071991019)
      ·
        refine ⟨3819203138440513607986529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2546135425627009071991019 3819203138440513607986529)
        ·
          refine ⟨2864402353830385205989897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3819203138440513607986529 2864402353830385205989897)
          ·
            refine ⟨2148301765372788904492423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2864402353830385205989897 2148301765372788904492423)
            ·
              refine ⟨3222452648059183356738635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2148301765372788904492423 3222452648059183356738635)
              ·
                refine ⟨4833678972088775035107953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3222452648059183356738635 4833678972088775035107953)
                ·
                  refine ⟨3625259229066581276330965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4833678972088775035107953 3625259229066581276330965)
                  ·
                    refine ⟨84967013181247998664007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3625259229066581276330965 84967013181247998664007)
                    ·
                      rfl

theorem cell23_496418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_496418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496418 prefixEnd_496418 := by exact prefixLift 496418
  have htrace : WordTrace (prefixWord ++ tailWord_496418) baseStart_496418 baseEnd_496418 := by
    simpa [prefixWord, tailWord_496418, baseEnd_496418] using wordTrace_append hprefix tailTrace_496418
  have hstable : (prefixWord ++ tailWord_496418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496418).length < 2 ^ (prefixWord ++ tailWord_496418).sum := by decide
  have hdescent : baseEnd_496418 < baseStart_496418 := by decide
  rcases family_descends (prefixWord ++ tailWord_496418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496429 : List Nat := [1, 5, 3, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_496429 : Nat := 118140960795 + 496429 * 2 ^ 59
def prefixEnd_496429 : Nat := 4983230072969 + 3 ^ 40 * 496429 * 2
def baseEnd_496429 : Nat := 254906687830943452954471

theorem tailTrace_496429 : CollatzResearch.WordTrace tailWord_496429 prefixEnd_496429 254906687830943452954471 := by
  unfold tailWord_496429
  simp only [CollatzResearch.WordTrace]
  refine ⟨18106253118529991168364341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12070835412353327445576227 18106253118529991168364341)
  ·
    refine ⟨1697461229862186672034157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18106253118529991168364341 1697461229862186672034157)
    ·
      refine ⟨636547961198320002012809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1697461229862186672034157 636547961198320002012809)
      ·
        refine ⟨477410970898740001509607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 636547961198320002012809 477410970898740001509607)
        ·
          refine ⟨716116456348110002264411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477410970898740001509607 716116456348110002264411)
          ·
            refine ⟨1074174684522165003396617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716116456348110002264411 1074174684522165003396617)
            ·
              refine ⟨805631013391623752547463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1074174684522165003396617 805631013391623752547463)
              ·
                refine ⟨1208446520087435628821195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 805631013391623752547463 1208446520087435628821195)
                ·
                  refine ⟨1812669780131153443231793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1208446520087435628821195 1812669780131153443231793)
                  ·
                    refine ⟨1359502335098365082423845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1812669780131153443231793 1359502335098365082423845)
                    ·
                      refine ⟨254906687830943452954471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1359502335098365082423845 254906687830943452954471)
                      ·
                        rfl

theorem cell23_496429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_496429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496429 prefixEnd_496429 := by exact prefixLift 496429
  have htrace : WordTrace (prefixWord ++ tailWord_496429) baseStart_496429 baseEnd_496429 := by
    simpa [prefixWord, tailWord_496429, baseEnd_496429] using wordTrace_append hprefix tailTrace_496429
  have hstable : (prefixWord ++ tailWord_496429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496429).length < 2 ^ (prefixWord ++ tailWord_496429).sum := by decide
  have hdescent : baseEnd_496429 < baseStart_496429 := by decide
  rcases family_descends (prefixWord ++ tailWord_496429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496458 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 1, 6, 3]
def baseStart_496458 : Nat := 118140960795 + 496458 * 2 ^ 59
def prefixEnd_496458 : Nat := 4983230072969 + 3 ^ 40 * 496458 * 2
def baseEnd_496458 : Nat := 254921578769923839491837

theorem tailTrace_496458 : CollatzResearch.WordTrace tailWord_496458 prefixEnd_496458 254921578769923839491837 := by
  unfold tailWord_496458
  simp only [CollatzResearch.WordTrace]
  refine ⟨4526827708856232280292507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12071540556949952747446685 4526827708856232280292507)
  ·
    refine ⟨6790241563284348420438761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4526827708856232280292507 6790241563284348420438761)
    ·
      refine ⟨5092681172463261315329071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6790241563284348420438761 5092681172463261315329071)
      ·
        refine ⟨7639021758694891972993607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5092681172463261315329071 7639021758694891972993607)
        ·
          refine ⟨11458532638042337959490411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7639021758694891972993607 11458532638042337959490411)
          ·
            refine ⟨17187798957063506939235617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11458532638042337959490411 17187798957063506939235617)
            ·
              refine ⟨12890849217797630204426713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17187798957063506939235617 12890849217797630204426713)
              ·
                refine ⟨9668136913348222653320035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12890849217797630204426713 9668136913348222653320035)
                ·
                  refine ⟨14502205370022333979980053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9668136913348222653320035 14502205370022333979980053)
                  ·
                    refine ⟨679790876719796905311565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14502205370022333979980053 679790876719796905311565)
                    ·
                      refine ⟨254921578769923839491837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 679790876719796905311565 254921578769923839491837)
                      ·
                        rfl

theorem cell23_496458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_496458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496458 prefixEnd_496458 := by exact prefixLift 496458
  have htrace : WordTrace (prefixWord ++ tailWord_496458) baseStart_496458 baseEnd_496458 := by
    simpa [prefixWord, tailWord_496458, baseEnd_496458] using wordTrace_append hprefix tailTrace_496458
  have hstable : (prefixWord ++ tailWord_496458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496458).length < 2 ^ (prefixWord ++ tailWord_496458).sum := by decide
  have hdescent : baseEnd_496458 < baseStart_496458 := by decide
  rcases family_descends (prefixWord ++ tailWord_496458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496508 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 6, 5]
def baseStart_496508 : Nat := 118140960795 + 496508 * 2 ^ 59
def prefixEnd_496508 : Nat := 4983230072969 + 3 ^ 40 * 496508 * 2
def baseEnd_496508 : Nat := 84982417600882881288869

theorem tailTrace_496508 : CollatzResearch.WordTrace tailWord_496508 prefixEnd_496508 84982417600882881288869 := by
  unfold tailWord_496508
  simp only [CollatzResearch.WordTrace]
  refine ⟨9054567242621893830245089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12072756323495858440326785 9054567242621893830245089)
  ·
    refine ⟨6790925431966420372683817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9054567242621893830245089 6790925431966420372683817)
    ·
      refine ⟨5093194073974815279512863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6790925431966420372683817 5093194073974815279512863)
      ·
        refine ⟨7639791110962222919269295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5093194073974815279512863 7639791110962222919269295)
        ·
          refine ⟨11459686666443334378903943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7639791110962222919269295 11459686666443334378903943)
          ·
            refine ⟨17189529999665001568355915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11459686666443334378903943 17189529999665001568355915)
            ·
              refine ⟨25784294999497502352533873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17189529999665001568355915 25784294999497502352533873)
              ·
                refine ⟨19338221249623126764400405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25784294999497502352533873 19338221249623126764400405)
                ·
                  refine ⟨906479121076084067081269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19338221249623126764400405 906479121076084067081269)
                  ·
                    refine ⟨84982417600882881288869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 906479121076084067081269 84982417600882881288869)
                    ·
                      rfl

theorem cell23_496508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_496508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496508 prefixEnd_496508 := by exact prefixLift 496508
  have htrace : WordTrace (prefixWord ++ tailWord_496508) baseStart_496508 baseEnd_496508 := by
    simpa [prefixWord, tailWord_496508, baseEnd_496508] using wordTrace_append hprefix tailTrace_496508
  have hstable : (prefixWord ++ tailWord_496508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496508).length < 2 ^ (prefixWord ++ tailWord_496508).sum := by decide
  have hdescent : baseEnd_496508 < baseStart_496508 := by decide
  rcases family_descends (prefixWord ++ tailWord_496508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496532 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 2, 5, 2]
def baseStart_496532 : Nat := 118140960795 + 496532 * 2 ^ 59
def prefixEnd_496532 : Nat := 4983230072969 + 3 ^ 40 * 496532 * 2
def baseEnd_496532 : Nat := 254959576338356549966497

theorem tailTrace_496532 : CollatzResearch.WordTrace tailWord_496532 prefixEnd_496532 254959576338356549966497 := by
  unfold tailWord_496532
  simp only [CollatzResearch.WordTrace]
  refine ⟨9055004918578419879681925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12073339891437893172909233 9055004918578419879681925)
  ·
    refine ⟨1697813422233453727440361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9055004918578419879681925 1697813422233453727440361)
    ·
      refine ⟨1273360066675090295580271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1697813422233453727440361 1273360066675090295580271)
      ·
        refine ⟨1910040100012635443370407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1273360066675090295580271 1910040100012635443370407)
        ·
          refine ⟨2865060150018953165055611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1910040100012635443370407 2865060150018953165055611)
          ·
            refine ⟨4297590225028429747583417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2865060150018953165055611 4297590225028429747583417)
            ·
              refine ⟨3223192668771322310687563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4297590225028429747583417 3223192668771322310687563)
              ·
                refine ⟨4834789003156983466031345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3223192668771322310687563 4834789003156983466031345)
                ·
                  refine ⟨3626091752367737599523509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4834789003156983466031345 3626091752367737599523509)
                  ·
                    refine ⟨339946101784475399955329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3626091752367737599523509 339946101784475399955329)
                    ·
                      refine ⟨254959576338356549966497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 339946101784475399955329 254959576338356549966497)
                      ·
                        rfl

theorem cell23_496532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_496532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496532 prefixEnd_496532 := by exact prefixLift 496532
  have htrace : WordTrace (prefixWord ++ tailWord_496532) baseStart_496532 baseEnd_496532 := by
    simpa [prefixWord, tailWord_496532, baseEnd_496532] using wordTrace_append hprefix tailTrace_496532
  have hstable : (prefixWord ++ tailWord_496532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496532).length < 2 ^ (prefixWord ++ tailWord_496532).sum := by decide
  have hdescent : baseEnd_496532 < baseStart_496532 := by decide
  rcases family_descends (prefixWord ++ tailWord_496532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496540 : List Nat := [2, 2, 3, 3, 3, 1, 2, 1, 2, 2, 2]
def baseStart_496540 : Nat := 118140960795 + 496540 * 2 ^ 59
def prefixEnd_496540 : Nat := 4983230072969 + 3 ^ 40 * 496540 * 2
def baseEnd_496540 : Nat := 254963684183592518666461

theorem tailTrace_496540 : CollatzResearch.WordTrace tailWord_496540 prefixEnd_496540 254963684183592518666461 := by
  unfold tailWord_496540
  simp only [CollatzResearch.WordTrace]
  refine ⟨9055150810563928562827537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12073534414085238083770049 9055150810563928562827537)
  ·
    refine ⟨6791363107922946422120653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9055150810563928562827537 6791363107922946422120653)
    ·
      refine ⟨2546761165471104908295245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6791363107922946422120653 2546761165471104908295245)
      ·
        refine ⟨955035437051664340610717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2546761165471104908295245 955035437051664340610717)
        ·
          refine ⟨358138288894374127729019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 955035437051664340610717 358138288894374127729019)
          ·
            refine ⟨537207433341561191593529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358138288894374127729019 537207433341561191593529)
            ·
              refine ⟨402905575006170893695147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 537207433341561191593529 402905575006170893695147)
              ·
                refine ⟨604358362509256340542721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402905575006170893695147 604358362509256340542721)
                ·
                  refine ⟨453268771881942255407041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 604358362509256340542721 453268771881942255407041)
                  ·
                    refine ⟨339951578911456691555281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 453268771881942255407041 339951578911456691555281)
                    ·
                      refine ⟨254963684183592518666461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 339951578911456691555281 254963684183592518666461)
                      ·
                        rfl

theorem cell23_496540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_496540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496540 prefixEnd_496540 := by exact prefixLift 496540
  have htrace : WordTrace (prefixWord ++ tailWord_496540) baseStart_496540 baseEnd_496540 := by
    simpa [prefixWord, tailWord_496540, baseEnd_496540] using wordTrace_append hprefix tailTrace_496540
  have hstable : (prefixWord ++ tailWord_496540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496540).length < 2 ^ (prefixWord ++ tailWord_496540).sum := by decide
  have hdescent : baseEnd_496540 < baseStart_496540 := by decide
  rcases family_descends (prefixWord ++ tailWord_496540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496675 : List Nat := [1, 1, 1, 4, 3, 3, 1, 9]
def baseStart_496675 : Nat := 118140960795 + 496675 * 2 ^ 59
def prefixEnd_496675 : Nat := 4983230072969 + 3 ^ 40 * 496675 * 2
def baseEnd_496675 : Nat := 9445666817479610758457

theorem tailTrace_496675 : CollatzResearch.WordTrace tailWord_496675 prefixEnd_496675 9445666817479610758457 := by
  unfold tailWord_496675
  simp only [CollatzResearch.WordTrace]
  refine ⟨18115225475638775181819479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12076816983759183454546319 18115225475638775181819479)
  ·
    refine ⟨27172838213458162772729219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18115225475638775181819479 27172838213458162772729219)
    ·
      refine ⟨40759257320187244159093829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27172838213458162772729219 40759257320187244159093829)
      ·
        refine ⟨7642360747535108279830093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40759257320187244159093829 7642360747535108279830093)
        ·
          refine ⟨2865885280325665604936285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7642360747535108279830093 2865885280325665604936285)
          ·
            refine ⟨1074706980122124601851107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2865885280325665604936285 1074706980122124601851107)
            ·
              refine ⟨1612060470183186902776661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1074706980122124601851107 1612060470183186902776661)
              ·
                refine ⟨9445666817479610758457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1612060470183186902776661 9445666817479610758457)
                ·
                  rfl

theorem cell23_496675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 9].length) (baseStart_496675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496675 prefixEnd_496675 := by exact prefixLift 496675
  have htrace : WordTrace (prefixWord ++ tailWord_496675) baseStart_496675 baseEnd_496675 := by
    simpa [prefixWord, tailWord_496675, baseEnd_496675] using wordTrace_append hprefix tailTrace_496675
  have hstable : (prefixWord ++ tailWord_496675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496675).length < 2 ^ (prefixWord ++ tailWord_496675).sum := by decide
  have hdescent : baseEnd_496675 < baseStart_496675 := by decide
  rcases family_descends (prefixWord ++ tailWord_496675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496679 : List Nat := [1, 1, 7, 1, 1, 1, 1, 2, 4, 4]
def baseStart_496679 : Nat := 118140960795 + 496679 * 2 ^ 59
def prefixEnd_496679 : Nat := 4983230072969 + 3 ^ 40 * 496679 * 2
def baseEnd_496679 : Nat := 85011685998189158276107

theorem tailTrace_496679 : CollatzResearch.WordTrace tailWord_496679 prefixEnd_496679 85011685998189158276107 := by
  unfold tailWord_496679
  simp only [CollatzResearch.WordTrace]
  refine ⟨18115371367624283864965091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12076914245082855909976727 18115371367624283864965091)
  ·
    refine ⟨27173057051436425797447637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18115371367624283864965091 27173057051436425797447637)
    ·
      refine ⟨636868524643041229627679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 27173057051436425797447637 636868524643041229627679)
      ·
        refine ⟨955302786964561844441519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636868524643041229627679 955302786964561844441519)
        ·
          refine ⟨1432954180446842766662279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 955302786964561844441519 1432954180446842766662279)
          ·
            refine ⟨2149431270670264149993419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1432954180446842766662279 2149431270670264149993419)
            ·
              refine ⟨3224146906005396224990129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2149431270670264149993419 3224146906005396224990129)
              ·
                refine ⟨2418110179504047168742597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3224146906005396224990129 2418110179504047168742597)
                ·
                  refine ⟨453395658657008844139237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2418110179504047168742597 453395658657008844139237)
                  ·
                    refine ⟨85011685998189158276107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 453395658657008844139237 85011685998189158276107)
                    ·
                      rfl

theorem cell23_496679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_496679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496679 prefixEnd_496679 := by exact prefixLift 496679
  have htrace : WordTrace (prefixWord ++ tailWord_496679) baseStart_496679 baseEnd_496679 := by
    simpa [prefixWord, tailWord_496679, baseEnd_496679] using wordTrace_append hprefix tailTrace_496679
  have hstable : (prefixWord ++ tailWord_496679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496679).length < 2 ^ (prefixWord ++ tailWord_496679).sum := by decide
  have hdescent : baseEnd_496679 < baseStart_496679 := by decide
  rcases family_descends (prefixWord ++ tailWord_496679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496692 : List Nat := [2, 5, 1, 2, 1, 1, 11]
def baseStart_496692 : Nat := 118140960795 + 496692 * 2 ^ 59
def prefixEnd_496692 : Nat := 4983230072969 + 3 ^ 40 * 496692 * 2
def baseEnd_496692 : Nat := 3148663373371307703281

theorem tailTrace_496692 : CollatzResearch.WordTrace tailWord_496692 prefixEnd_496692 3148663373371307703281 := by
  unfold tailWord_496692
  simp only [CollatzResearch.WordTrace]
  refine ⟨9057922758288593542594165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12077230344384791390125553 9057922758288593542594165)
  ·
    refine ⟨849180258589555644618203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9057922758288593542594165 849180258589555644618203)
    ·
      refine ⟨1273770387884333466927305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 849180258589555644618203 1273770387884333466927305)
      ·
        refine ⟨955327790913250100195479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1273770387884333466927305 955327790913250100195479)
        ·
          refine ⟨1432991686369875150293219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 955327790913250100195479 1432991686369875150293219)
          ·
            refine ⟨2149487529554812725439829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1432991686369875150293219 2149487529554812725439829)
            ·
              refine ⟨3148663373371307703281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 2149487529554812725439829 3148663373371307703281)
              ·
                rfl

theorem cell23_496692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 11].length) (baseStart_496692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496692 prefixEnd_496692 := by exact prefixLift 496692
  have htrace : WordTrace (prefixWord ++ tailWord_496692) baseStart_496692 baseEnd_496692 := by
    simpa [prefixWord, tailWord_496692, baseEnd_496692] using wordTrace_append hprefix tailTrace_496692
  have hstable : (prefixWord ++ tailWord_496692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496692).length < 2 ^ (prefixWord ++ tailWord_496692).sum := by decide
  have hdescent : baseEnd_496692 < baseStart_496692 := by decide
  rcases family_descends (prefixWord ++ tailWord_496692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496729 : List Nat := [1, 2, 1, 2, 2, 1, 2, 6, 1, 3, 2]
def baseStart_496729 : Nat := 118140960795 + 496729 * 2 ^ 59
def prefixEnd_496729 : Nat := 4983230072969 + 3 ^ 40 * 496729 * 2
def baseEnd_496729 : Nat := 255060732027292279203091

theorem tailTrace_496729 : CollatzResearch.WordTrace tailWord_496729 prefixEnd_496729 255060732027292279203091 := by
  unfold tailWord_496729
  simp only [CollatzResearch.WordTrace]
  refine ⟨18117195017443142404285241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12078130011628761602856827 18117195017443142404285241)
  ·
    refine ⟨13587896263082356803213931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18117195017443142404285241 13587896263082356803213931)
    ·
      refine ⟨20381844394623535204820897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13587896263082356803213931 20381844394623535204820897)
      ·
        refine ⟨15286383295967651403615673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20381844394623535204820897 15286383295967651403615673)
        ·
          refine ⟨11464787471975738552711755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15286383295967651403615673 11464787471975738552711755)
          ·
            refine ⟨17197181207963607829067633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11464787471975738552711755 17197181207963607829067633)
            ·
              refine ⟨12897885905972705871800725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17197181207963607829067633 12897885905972705871800725)
              ·
                refine ⟨604588401842470587740659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12897885905972705871800725 604588401842470587740659)
                ·
                  refine ⟨906882602763705881610989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 604588401842470587740659 906882602763705881610989)
                  ·
                    refine ⟨340080976036389705604121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 906882602763705881610989 340080976036389705604121)
                    ·
                      refine ⟨255060732027292279203091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 340080976036389705604121 255060732027292279203091)
                      ·
                        rfl

theorem cell23_496729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 3, 2].length) (baseStart_496729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496729 prefixEnd_496729 := by exact prefixLift 496729
  have htrace : WordTrace (prefixWord ++ tailWord_496729) baseStart_496729 baseEnd_496729 := by
    simpa [prefixWord, tailWord_496729, baseEnd_496729] using wordTrace_append hprefix tailTrace_496729
  have hstable : (prefixWord ++ tailWord_496729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496729).length < 2 ^ (prefixWord ++ tailWord_496729).sum := by decide
  have hdescent : baseEnd_496729 < baseStart_496729 := by decide
  rcases family_descends (prefixWord ++ tailWord_496729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496755 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 4]
def baseStart_496755 : Nat := 118140960795 + 496755 * 2 ^ 59
def prefixEnd_496755 : Nat := 4983230072969 + 3 ^ 40 * 496755 * 2
def baseEnd_496755 : Nat := 255074082524309177477971

theorem tailTrace_496755 : CollatzResearch.WordTrace tailWord_496755 prefixEnd_496755 255074082524309177477971 := by
  unfold tailWord_496755
  simp only [CollatzResearch.WordTrace]
  refine ⟨18118143315348948844731719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12078762210232632563154479 18118143315348948844731719)
  ·
    refine ⟨27177214973023423267097579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18118143315348948844731719 27177214973023423267097579)
    ·
      refine ⟨40765822459535134900646369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27177214973023423267097579 40765822459535134900646369)
      ·
        refine ⟨30574366844651351175484777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40765822459535134900646369 30574366844651351175484777)
        ·
          refine ⟨22930775133488513381613583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30574366844651351175484777 22930775133488513381613583)
          ·
            refine ⟨34396162700232770072420375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22930775133488513381613583 34396162700232770072420375)
            ·
              refine ⟨51594244050349155108630563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34396162700232770072420375 51594244050349155108630563)
              ·
                refine ⟨77391366075523732662945845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51594244050349155108630563 77391366075523732662945845)
                ·
                  refine ⟨7255440569580349937151173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 77391366075523732662945845 7255440569580349937151173)
                  ·
                    refine ⟨1360395106796315613215845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7255440569580349937151173 1360395106796315613215845)
                    ·
                      refine ⟨255074082524309177477971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1360395106796315613215845 255074082524309177477971)
                      ·
                        rfl

theorem cell23_496755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 4].length) (baseStart_496755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496755 prefixEnd_496755 := by exact prefixLift 496755
  have htrace : WordTrace (prefixWord ++ tailWord_496755) baseStart_496755 baseEnd_496755 := by
    simpa [prefixWord, tailWord_496755, baseEnd_496755] using wordTrace_append hprefix tailTrace_496755
  have hstable : (prefixWord ++ tailWord_496755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496755).length < 2 ^ (prefixWord ++ tailWord_496755).sum := by decide
  have hdescent : baseEnd_496755 < baseStart_496755 := by decide
  rcases family_descends (prefixWord ++ tailWord_496755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496772 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 1, 4, 4]
def baseStart_496772 : Nat := 118140960795 + 496772 * 2 ^ 59
def prefixEnd_496772 : Nat := 4983230072969 + 3 ^ 40 * 496772 * 2
def baseEnd_496772 : Nat := 255082811695435610965393

theorem tailTrace_496772 : CollatzResearch.WordTrace tailWord_496772 prefixEnd_496772 255082811695435610965393 := by
  unfold tailWord_496772
  simp only [CollatzResearch.WordTrace]
  refine ⟨9059381678143680374050285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12079175570858240498733713 9059381678143680374050285)
  ·
    refine ⟨3397268129303880140268857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9059381678143680374050285 3397268129303880140268857)
    ·
      refine ⟨2547951096977910105201643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3397268129303880140268857 2547951096977910105201643)
      ·
        refine ⟨3821926645466865157802465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2547951096977910105201643 3821926645466865157802465)
        ·
          refine ⟨2866444984100148868351849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3821926645466865157802465 2866444984100148868351849)
          ·
            refine ⟨2149833738075111651263887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2866444984100148868351849 2149833738075111651263887)
            ·
              refine ⟨3224750607112667476895831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2149833738075111651263887 3224750607112667476895831)
              ·
                refine ⟨4837125910669001215343747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3224750607112667476895831 4837125910669001215343747)
                ·
                  refine ⟨7255688866003501823015621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4837125910669001215343747 7255688866003501823015621)
                  ·
                    refine ⟨1360441662375656591815429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7255688866003501823015621 1360441662375656591815429)
                    ·
                      refine ⟨255082811695435610965393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1360441662375656591815429 255082811695435610965393)
                      ·
                        rfl

theorem cell23_496772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_496772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496772 prefixEnd_496772 := by exact prefixLift 496772
  have htrace : WordTrace (prefixWord ++ tailWord_496772) baseStart_496772 baseEnd_496772 := by
    simpa [prefixWord, tailWord_496772, baseEnd_496772] using wordTrace_append hprefix tailTrace_496772
  have hstable : (prefixWord ++ tailWord_496772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496772).length < 2 ^ (prefixWord ++ tailWord_496772).sum := by decide
  have hdescent : baseEnd_496772 < baseStart_496772 := by decide
  rcases family_descends (prefixWord ++ tailWord_496772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496782 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 9]
def baseStart_496782 : Nat := 118140960795 + 496782 * 2 ^ 59
def prefixEnd_496782 : Nat := 4983230072969 + 3 ^ 40 * 496782 * 2
def baseEnd_496782 : Nat := 28343105166886730204483

theorem tailTrace_496782 : CollatzResearch.WordTrace tailWord_496782 prefixEnd_496782 28343105166886730204483 := by
  unfold tailWord_496782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2264891010781391556995575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12079418724167421637309733 2264891010781391556995575)
  ·
    refine ⟨3397336516172087335493363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2264891010781391556995575 3397336516172087335493363)
    ·
      refine ⟨5096004774258131003240045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3397336516172087335493363 5096004774258131003240045)
      ·
        refine ⟨1911001790346799126215017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5096004774258131003240045 1911001790346799126215017)
        ·
          refine ⟨1433251342760099344661263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1911001790346799126215017 1433251342760099344661263)
          ·
            refine ⟨2149877014140149016991895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1433251342760099344661263 2149877014140149016991895)
            ·
              refine ⟨3224815521210223525487843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2149877014140149016991895 3224815521210223525487843)
              ·
                refine ⟨4837223281815335288231765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3224815521210223525487843 4837223281815335288231765)
                ·
                  refine ⟨28343105166886730204483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4837223281815335288231765 28343105166886730204483)
                  ·
                    rfl

theorem cell23_496782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 9].length) (baseStart_496782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496782 prefixEnd_496782 := by exact prefixLift 496782
  have htrace : WordTrace (prefixWord ++ tailWord_496782) baseStart_496782 baseEnd_496782 := by
    simpa [prefixWord, tailWord_496782, baseEnd_496782] using wordTrace_append hprefix tailTrace_496782
  have hstable : (prefixWord ++ tailWord_496782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496782).length < 2 ^ (prefixWord ++ tailWord_496782).sum := by decide
  have hdescent : baseEnd_496782 < baseStart_496782 := by decide
  rcases family_descends (prefixWord ++ tailWord_496782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496810 : List Nat := [3, 1, 5, 1, 1, 1, 3, 2, 2, 2, 2]
def baseStart_496810 : Nat := 118140960795 + 496810 * 2 ^ 59
def prefixEnd_496810 : Nat := 4983230072969 + 3 ^ 40 * 496810 * 2
def baseEnd_496810 : Nat := 255102323960306462290219

theorem tailTrace_496810 : CollatzResearch.WordTrace tailWord_496810 prefixEnd_496810 255102323960306462290219 := by
  unfold tailWord_496810
  simp only [CollatzResearch.WordTrace]
  refine ⟨4530037332537423309495971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12080099553433128825322589 4530037332537423309495971)
  ·
    refine ⟨6795055998806134964243957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4530037332537423309495971 6795055998806134964243957)
    ·
      refine ⟨637036499888075152897871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6795055998806134964243957 637036499888075152897871)
      ·
        refine ⟨955554749832112729346807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637036499888075152897871 955554749832112729346807)
        ·
          refine ⟨1433332124748169094020211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 955554749832112729346807 1433332124748169094020211)
          ·
            refine ⟨2149998187122253641030317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1433332124748169094020211 2149998187122253641030317)
            ·
              refine ⟨806249320170845115386369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2149998187122253641030317 806249320170845115386369)
              ·
                refine ⟨604686990128133836539777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 806249320170845115386369 604686990128133836539777)
                ·
                  refine ⟨453515242596100377404833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 604686990128133836539777 453515242596100377404833)
                  ·
                    refine ⟨340136431947075283053625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 453515242596100377404833 340136431947075283053625)
                    ·
                      refine ⟨255102323960306462290219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 340136431947075283053625 255102323960306462290219)
                      ·
                        rfl

theorem cell23_496810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_496810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496810 prefixEnd_496810 := by exact prefixLift 496810
  have htrace : WordTrace (prefixWord ++ tailWord_496810) baseStart_496810 baseEnd_496810 := by
    simpa [prefixWord, tailWord_496810, baseEnd_496810] using wordTrace_append hprefix tailTrace_496810
  have hstable : (prefixWord ++ tailWord_496810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496810).length < 2 ^ (prefixWord ++ tailWord_496810).sum := by decide
  have hdescent : baseEnd_496810 < baseStart_496810 := by decide
  rcases family_descends (prefixWord ++ tailWord_496810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496872 : List Nat := [2, 1, 4, 1, 2, 1, 1, 3, 8]
def baseStart_496872 : Nat := 118140960795 + 496872 * 2 ^ 59
def prefixEnd_496872 : Nat := 4983230072969 + 3 ^ 40 * 496872 * 2
def baseEnd_496872 : Nat := 28348239973431691079437

theorem tailTrace_496872 : CollatzResearch.WordTrace tailWord_496872 prefixEnd_496872 28348239973431691079437 := by
  unfold tailWord_496872
  simp only [CollatzResearch.WordTrace]
  refine ⟨9061205327962538913370435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12081607103950051884493913 9061205327962538913370435)
  ·
    refine ⟨13591807991943808370055653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9061205327962538913370435 13591807991943808370055653)
    ·
      refine ⟨2548463998489464069385435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13591807991943808370055653 2548463998489464069385435)
      ·
        refine ⟨3822695997734196104078153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2548463998489464069385435 3822695997734196104078153)
        ·
          refine ⟨2867021998300647078058615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3822695997734196104078153 2867021998300647078058615)
          ·
            refine ⟨4300532997450970617087923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2867021998300647078058615 4300532997450970617087923)
            ·
              refine ⟨6450799496176455925631885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4300532997450970617087923 6450799496176455925631885)
              ·
                refine ⟨2419049811066170972111957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6450799496176455925631885 2419049811066170972111957)
                ·
                  refine ⟨28348239973431691079437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2419049811066170972111957 28348239973431691079437)
                  ·
                    rfl

theorem cell23_496872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 8].length) (baseStart_496872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496872 prefixEnd_496872 := by exact prefixLift 496872
  have htrace : WordTrace (prefixWord ++ tailWord_496872) baseStart_496872 baseEnd_496872 := by
    simpa [prefixWord, tailWord_496872, baseEnd_496872] using wordTrace_append hprefix tailTrace_496872
  have hstable : (prefixWord ++ tailWord_496872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496872).length < 2 ^ (prefixWord ++ tailWord_496872).sum := by decide
  have hdescent : baseEnd_496872 < baseStart_496872 := by decide
  rcases family_descends (prefixWord ++ tailWord_496872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496876 : List Nat := [2, 2, 1, 1, 2, 6, 1, 1, 3, 4]
def baseStart_496876 : Nat := 118140960795 + 496876 * 2 ^ 59
def prefixEnd_496876 : Nat := 4983230072969 + 3 ^ 40 * 496876 * 2
def baseEnd_496876 : Nat := 85045404561167734688305

theorem tailTrace_496876 : CollatzResearch.WordTrace tailWord_496876 prefixEnd_496876 85045404561167734688305 := by
  unfold tailWord_496876
  simp only [CollatzResearch.WordTrace]
  refine ⟨9061278273955293254943241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12081704365273724339924321 9061278273955293254943241)
  ·
    refine ⟨6795958705466469941207431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9061278273955293254943241 6795958705466469941207431)
    ·
      refine ⟨10193938058199704911811147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6795958705466469941207431 10193938058199704911811147)
      ·
        refine ⟨15290907087299557367716721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10193938058199704911811147 15290907087299557367716721)
        ·
          refine ⟨11468180315474668025787541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15290907087299557367716721 11468180315474668025787541)
          ·
            refine ⟨537570952287875063708791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11468180315474668025787541 537570952287875063708791)
            ·
              refine ⟨806356428431812595563187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537570952287875063708791 806356428431812595563187)
              ·
                refine ⟨1209534642647718893344781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 806356428431812595563187 1209534642647718893344781)
                ·
                  refine ⟨453575490992894585004293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1209534642647718893344781 453575490992894585004293)
                  ·
                    refine ⟨85045404561167734688305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 453575490992894585004293 85045404561167734688305)
                    ·
                      rfl

theorem cell23_496876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 4].length) (baseStart_496876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496876 prefixEnd_496876 := by exact prefixLift 496876
  have htrace : WordTrace (prefixWord ++ tailWord_496876) baseStart_496876 baseEnd_496876 := by
    simpa [prefixWord, tailWord_496876, baseEnd_496876] using wordTrace_append hprefix tailTrace_496876
  have hstable : (prefixWord ++ tailWord_496876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496876).length < 2 ^ (prefixWord ++ tailWord_496876).sum := by decide
  have hdescent : baseEnd_496876 < baseStart_496876 := by decide
  rcases family_descends (prefixWord ++ tailWord_496876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496927 : List Nat := [1, 1, 2, 4, 5, 1, 2, 2, 1, 4]
def baseStart_496927 : Nat := 118140960795 + 496927 * 2 ^ 59
def prefixEnd_496927 : Nat := 4983230072969 + 3 ^ 40 * 496927 * 2
def baseEnd_496927 : Nat := 85054133732294168175727

theorem tailTrace_496927 : CollatzResearch.WordTrace tailWord_496927 prefixEnd_496927 85054133732294168175727 := by
  unfold tailWord_496927
  simp only [CollatzResearch.WordTrace]
  refine ⟨18124416670725822219993035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12082944447150548146662023 18124416670725822219993035)
  ·
    refine ⟨27186625006088733329989553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18124416670725822219993035 27186625006088733329989553)
    ·
      refine ⟨20389968754566549997492165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27186625006088733329989553 20389968754566549997492165)
      ·
        refine ⟨3823119141481228124529781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20389968754566549997492165 3823119141481228124529781)
        ·
          refine ⟨358417419513865136674667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3823119141481228124529781 358417419513865136674667)
          ·
            refine ⟨537626129270797705012001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358417419513865136674667 537626129270797705012001)
            ·
              refine ⟨403219596953098278759001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 537626129270797705012001 403219596953098278759001)
              ·
                refine ⟨302414697714823709069251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 403219596953098278759001 302414697714823709069251)
                ·
                  refine ⟨453622046572235563603877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302414697714823709069251 453622046572235563603877)
                  ·
                    refine ⟨85054133732294168175727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 453622046572235563603877 85054133732294168175727)
                    ·
                      rfl

theorem cell23_496927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 2, 1, 4].length) (baseStart_496927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496927 prefixEnd_496927 := by exact prefixLift 496927
  have htrace : WordTrace (prefixWord ++ tailWord_496927) baseStart_496927 baseEnd_496927 := by
    simpa [prefixWord, tailWord_496927, baseEnd_496927] using wordTrace_append hprefix tailTrace_496927
  have hstable : (prefixWord ++ tailWord_496927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496927).length < 2 ^ (prefixWord ++ tailWord_496927).sum := by decide
  have hdescent : baseEnd_496927 < baseStart_496927 := by decide
  rcases family_descends (prefixWord ++ tailWord_496927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496949 : List Nat := [1, 3, 3, 1, 2, 2, 1, 3, 1, 6]
def baseStart_496949 : Nat := 118140960795 + 496949 * 2 ^ 59
def prefixEnd_496949 : Nat := 4983230072969 + 3 ^ 40 * 496949 * 2
def baseEnd_496949 : Nat := 85057899257093806150693

theorem tailTrace_496949 : CollatzResearch.WordTrace tailWord_496949 prefixEnd_496949 85057899257093806150693 := by
  unfold tailWord_496949
  simp only [CollatzResearch.WordTrace]
  refine ⟨18125219076646119977293901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12083479384430746651529267 18125219076646119977293901)
  ·
    refine ⟨6796957153742294991485213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18125219076646119977293901 6796957153742294991485213)
    ·
      refine ⟨2548858932653360621806955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6796957153742294991485213 2548858932653360621806955)
      ·
        refine ⟨3823288398980040932710433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2548858932653360621806955 3823288398980040932710433)
        ·
          refine ⟨2867466299235030699532825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3823288398980040932710433 2867466299235030699532825)
          ·
            refine ⟨2150599724426273024649619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2867466299235030699532825 2150599724426273024649619)
            ·
              refine ⟨3225899586639409536974429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2150599724426273024649619 3225899586639409536974429)
              ·
                refine ⟨1209712344989778576365411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3225899586639409536974429 1209712344989778576365411)
                ·
                  refine ⟨1814568517484667864548117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1209712344989778576365411 1814568517484667864548117)
                  ·
                    refine ⟨85057899257093806150693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1814568517484667864548117 85057899257093806150693)
                    ·
                      rfl

theorem cell23_496949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_496949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496949 prefixEnd_496949 := by exact prefixLift 496949
  have htrace : WordTrace (prefixWord ++ tailWord_496949) baseStart_496949 baseEnd_496949 := by
    simpa [prefixWord, tailWord_496949, baseEnd_496949] using wordTrace_append hprefix tailTrace_496949
  have hstable : (prefixWord ++ tailWord_496949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496949).length < 2 ^ (prefixWord ++ tailWord_496949).sum := by decide
  have hdescent : baseEnd_496949 < baseStart_496949 := by decide
  rcases family_descends (prefixWord ++ tailWord_496949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496969 : List Nat := [1, 2, 1, 1, 2, 3, 4, 2, 1, 2, 4]
def baseStart_496969 : Nat := 118140960795 + 496969 * 2 ^ 59
def prefixEnd_496969 : Nat := 4983230072969 + 3 ^ 40 * 496969 * 2
def baseEnd_496969 : Nat := 255183967384371340201987

theorem tailTrace_496969 : CollatzResearch.WordTrace tailWord_496969 prefixEnd_496969 255183967384371340201987 := by
  unfold tailWord_496969
  simp only [CollatzResearch.WordTrace]
  refine ⟨18125948536573663393021961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12083965691049108928681307 18125948536573663393021961)
  ·
    refine ⟨13594461402430247544766471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18125948536573663393021961 13594461402430247544766471)
    ·
      refine ⟨20391692103645371317149707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13594461402430247544766471 20391692103645371317149707)
      ·
        refine ⟨30587538155468056975724561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20391692103645371317149707 30587538155468056975724561)
        ·
          refine ⟨22940653616601042731793421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30587538155468056975724561 22940653616601042731793421)
          ·
            refine ⟨8602745106225391024422533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22940653616601042731793421 8602745106225391024422533)
            ·
              refine ⟨1613014707417260817079225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8602745106225391024422533 1613014707417260817079225)
              ·
                refine ⟨1209761030562945612809419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1613014707417260817079225 1209761030562945612809419)
                ·
                  refine ⟨1814641545844418419214129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1209761030562945612809419 1814641545844418419214129)
                  ·
                    refine ⟨1360981159383313814410597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1814641545844418419214129 1360981159383313814410597)
                    ·
                      refine ⟨255183967384371340201987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1360981159383313814410597 255183967384371340201987)
                      ·
                        rfl

theorem cell23_496969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 2, 4].length) (baseStart_496969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496969 prefixEnd_496969 := by exact prefixLift 496969
  have htrace : WordTrace (prefixWord ++ tailWord_496969) baseStart_496969 baseEnd_496969 := by
    simpa [prefixWord, tailWord_496969, baseEnd_496969] using wordTrace_append hprefix tailTrace_496969
  have hstable : (prefixWord ++ tailWord_496969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496969).length < 2 ^ (prefixWord ++ tailWord_496969).sum := by decide
  have hdescent : baseEnd_496969 < baseStart_496969 := by decide
  rcases family_descends (prefixWord ++ tailWord_496969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496976 : List Nat := [2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 3]
def baseStart_496976 : Nat := 118140960795 + 496976 * 2 ^ 59
def prefixEnd_496976 : Nat := 4983230072969 + 3 ^ 40 * 496976 * 2
def baseEnd_496976 : Nat := 255187561748952812814455

theorem tailTrace_496976 : CollatzResearch.WordTrace tailWord_496976 prefixEnd_496976 255187561748952812814455 := by
  unfold tailWord_496976
  simp only [CollatzResearch.WordTrace]
  refine ⟨9063101923774151794263391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12084135898365535725684521 9063101923774151794263391)
  ·
    refine ⟨13594652885661227691395087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9063101923774151794263391 13594652885661227691395087)
    ·
      refine ⟨20391979328491841537092631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13594652885661227691395087 20391979328491841537092631)
      ·
        refine ⟨30587968992737762305638947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20391979328491841537092631 30587968992737762305638947)
        ·
          refine ⟨45881953489106643458458421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30587968992737762305638947 45881953489106643458458421)
          ·
            refine ⟨4301433139603747824230477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45881953489106643458458421 4301433139603747824230477)
            ·
              refine ⟨1613037427351405434086429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4301433139603747824230477 1613037427351405434086429)
              ·
                refine ⟨604889035256777037782411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1613037427351405434086429 604889035256777037782411)
                ·
                  refine ⟨907333552885165556673617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 604889035256777037782411 907333552885165556673617)
                  ·
                    refine ⟨680500164663874167505213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 907333552885165556673617 680500164663874167505213)
                    ·
                      refine ⟨255187561748952812814455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 680500164663874167505213 255187561748952812814455)
                      ·
                        rfl

theorem cell23_496976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 3].length) (baseStart_496976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496976 prefixEnd_496976 := by exact prefixLift 496976
  have htrace : WordTrace (prefixWord ++ tailWord_496976) baseStart_496976 baseEnd_496976 := by
    simpa [prefixWord, tailWord_496976, baseEnd_496976] using wordTrace_append hprefix tailTrace_496976
  have hstable : (prefixWord ++ tailWord_496976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496976).length < 2 ^ (prefixWord ++ tailWord_496976).sum := by decide
  have hdescent : baseEnd_496976 < baseStart_496976 := by decide
  rcases family_descends (prefixWord ++ tailWord_496976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496983 : List Nat := [1, 1, 3, 2, 3, 4, 1, 2, 2, 4]
def baseStart_496983 : Nat := 118140960795 + 496983 * 2 ^ 59
def prefixEnd_496983 : Nat := 4983230072969 + 3 ^ 40 * 496983 * 2
def baseEnd_496983 : Nat := 85063718704511428475641

theorem tailTrace_496983 : CollatzResearch.WordTrace tailWord_496983 prefixEnd_496983 85063718704511428475641 := by
  unfold tailWord_496983
  simp only [CollatzResearch.WordTrace]
  refine ⟨18126459158522943784031603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12084306105681962522687735 18126459158522943784031603)
  ·
    refine ⟨27189688737784415676047405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18126459158522943784031603 27189688737784415676047405)
    ·
      refine ⟨10196133276669155878517777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27189688737784415676047405 10196133276669155878517777)
      ·
        refine ⟨7647099957501866908888333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10196133276669155878517777 7647099957501866908888333)
        ·
          refine ⟨2867662484063200090833125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7647099957501866908888333 2867662484063200090833125)
          ·
            refine ⟨537686715761850017031211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2867662484063200090833125 537686715761850017031211)
            ·
              refine ⟨806530073642775025546817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537686715761850017031211 806530073642775025546817)
              ·
                refine ⟨604897555232081269160113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 806530073642775025546817 604897555232081269160113)
                ·
                  refine ⟨453673166424060951870085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 604897555232081269160113 453673166424060951870085)
                  ·
                    refine ⟨85063718704511428475641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 453673166424060951870085 85063718704511428475641)
                    ·
                      rfl

theorem cell23_496983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 2, 4].length) (baseStart_496983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_496983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_496983 prefixEnd_496983 := by exact prefixLift 496983
  have htrace : WordTrace (prefixWord ++ tailWord_496983) baseStart_496983 baseEnd_496983 := by
    simpa [prefixWord, tailWord_496983, baseEnd_496983] using wordTrace_append hprefix tailTrace_496983
  have hstable : (prefixWord ++ tailWord_496983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496983).length < 2 ^ (prefixWord ++ tailWord_496983).sum := by decide
  have hdescent : baseEnd_496983 < baseStart_496983 := by decide
  rcases family_descends (prefixWord ++ tailWord_496983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497000 : List Nat := [2, 1, 4, 2, 3, 1, 3, 1, 2, 4]
def baseStart_497000 : Nat := 118140960795 + 497000 * 2 ^ 59
def prefixEnd_497000 : Nat := 4983230072969 + 3 ^ 40 * 497000 * 2
def baseEnd_497000 : Nat := 85066628428220239638115

theorem tailTrace_497000 : CollatzResearch.WordTrace tailWord_497000 prefixEnd_497000 85066628428220239638115 := by
  unfold tailWord_497000
  simp only [CollatzResearch.WordTrace]
  refine ⟨9063539599730677843700227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12084719466307570458266969 9063539599730677843700227)
  ·
    refine ⟨13595309399596016765550341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9063539599730677843700227 13595309399596016765550341)
    ·
      refine ⟨2549120512424253143540689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13595309399596016765550341 2549120512424253143540689)
      ·
        refine ⟨1911840384318189857655517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2549120512424253143540689 1911840384318189857655517)
        ·
          refine ⟨716940144119321196620819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1911840384318189857655517 716940144119321196620819)
          ·
            refine ⟨1075410216178981794931229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 716940144119321196620819 1075410216178981794931229)
            ·
              refine ⟨403278831067118173099211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1075410216178981794931229 403278831067118173099211)
              ·
                refine ⟨604918246600677259648817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403278831067118173099211 604918246600677259648817)
                ·
                  refine ⟨453688684950507944736613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 604918246600677259648817 453688684950507944736613)
                  ·
                    refine ⟨85066628428220239638115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 453688684950507944736613 85066628428220239638115)
                    ·
                      rfl

theorem cell23_497000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_497000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497000 prefixEnd_497000 := by exact prefixLift 497000
  have htrace : WordTrace (prefixWord ++ tailWord_497000) baseStart_497000 baseEnd_497000 := by
    simpa [prefixWord, tailWord_497000, baseEnd_497000] using wordTrace_append hprefix tailTrace_497000
  have hstable : (prefixWord ++ tailWord_497000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497000).length < 2 ^ (prefixWord ++ tailWord_497000).sum := by decide
  have hdescent : baseEnd_497000 < baseStart_497000 := by decide
  rcases family_descends (prefixWord ++ tailWord_497000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497013 : List Nat := [1, 3, 4, 1, 3, 2, 2, 7]
def baseStart_497013 : Nat := 118140960795 + 497013 * 2 ^ 59
def prefixEnd_497013 : Nat := 4983230072969 + 3 ^ 40 * 497013 * 2
def baseEnd_497013 : Nat := 9452094834561821038955

theorem tailTrace_497013 : CollatzResearch.WordTrace tailWord_497013 prefixEnd_497013 9452094834561821038955 := by
  unfold tailWord_497013
  simp only [CollatzResearch.WordTrace]
  refine ⟨18127553348414258907623693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12085035565609505938415795 18127553348414258907623693)
  ·
    refine ⟨6797832505655347090358885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18127553348414258907623693 6797832505655347090358885)
    ·
      refine ⟨1274593594810377579442291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6797832505655347090358885 1274593594810377579442291)
      ·
        refine ⟨1911890392215566369163437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1274593594810377579442291 1911890392215566369163437)
        ·
          refine ⟨716958897080837388436289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1911890392215566369163437 716958897080837388436289)
          ·
            refine ⟨537719172810628041327217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 716958897080837388436289 537719172810628041327217)
            ·
              refine ⟨403289379607971030995413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 537719172810628041327217 403289379607971030995413)
              ·
                refine ⟨9452094834561821038955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 403289379607971030995413 9452094834561821038955)
                ·
                  rfl

theorem cell23_497013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 7].length) (baseStart_497013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497013 prefixEnd_497013 := by exact prefixLift 497013
  have htrace : WordTrace (prefixWord ++ tailWord_497013) baseStart_497013 baseEnd_497013 := by
    simpa [prefixWord, tailWord_497013, baseEnd_497013] using wordTrace_append hprefix tailTrace_497013
  have hstable : (prefixWord ++ tailWord_497013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497013).length < 2 ^ (prefixWord ++ tailWord_497013).sum := by decide
  have hdescent : baseEnd_497013 < baseStart_497013 := by decide
  rcases family_descends (prefixWord ++ tailWord_497013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497059 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 4]
def baseStart_497059 : Nat := 118140960795 + 497059 * 2 ^ 59
def prefixEnd_497059 : Nat := 4983230072969 + 3 ^ 40 * 497059 * 2
def baseEnd_497059 : Nat := 255230180643275988076573

theorem tailTrace_497059 : CollatzResearch.WordTrace tailWord_497059 prefixEnd_497059 255230180643275988076573 := by
  unfold tailWord_497059
  simp only [CollatzResearch.WordTrace]
  refine ⟨18129231106247608763798231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12086154070831739175865487 18129231106247608763798231)
  ·
    refine ⟨27193846659371413145697347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18129231106247608763798231 27193846659371413145697347)
    ·
      refine ⟨40790769989057119718546021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27193846659371413145697347 40790769989057119718546021)
      ·
        refine ⟨7648269372948209947227379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40790769989057119718546021 7648269372948209947227379)
        ·
          refine ⟨11472404059422314920841069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7648269372948209947227379 11472404059422314920841069)
          ·
            refine ⟨4302151522283368095315401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11472404059422314920841069 4302151522283368095315401)
            ·
              refine ⟨3226613641712526071486551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4302151522283368095315401 3226613641712526071486551)
              ·
                refine ⟨4839920462568789107229827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3226613641712526071486551 4839920462568789107229827)
                ·
                  refine ⟨7259880693853183660844741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4839920462568789107229827 7259880693853183660844741)
                  ·
                    refine ⟨1361227630097471936408389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7259880693853183660844741 1361227630097471936408389)
                    ·
                      refine ⟨255230180643275988076573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1361227630097471936408389 255230180643275988076573)
                      ·
                        rfl

theorem cell23_497059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_497059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497059 prefixEnd_497059 := by exact prefixLift 497059
  have htrace : WordTrace (prefixWord ++ tailWord_497059) baseStart_497059 baseEnd_497059 := by
    simpa [prefixWord, tailWord_497059, baseEnd_497059] using wordTrace_append hprefix tailTrace_497059
  have hstable : (prefixWord ++ tailWord_497059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497059).length < 2 ^ (prefixWord ++ tailWord_497059).sum := by decide
  have hdescent : baseEnd_497059 < baseStart_497059 := by decide
  rcases family_descends (prefixWord ++ tailWord_497059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497063 : List Nat := [1, 1, 6, 1, 1, 1, 2, 3, 1, 4, 2]
def baseStart_497063 : Nat := 118140960795 + 497063 * 2 ^ 59
def prefixEnd_497063 : Nat := 4983230072969 + 3 ^ 40 * 497063 * 2
def baseEnd_497063 : Nat := 255232234565893972426555

theorem tailTrace_497063 : CollatzResearch.WordTrace tailWord_497063 prefixEnd_497063 255232234565893972426555 := by
  unfold tailWord_497063
  simp only [CollatzResearch.WordTrace]
  refine ⟨18129376998233117446943843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12086251332155411631295895 18129376998233117446943843)
  ·
    refine ⟨27194065497349676170415765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18129376998233117446943843 27194065497349676170415765)
    ·
      refine ⟨1274721820188266070488239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27194065497349676170415765 1274721820188266070488239)
      ·
        refine ⟨1912082730282399105732359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1274721820188266070488239 1912082730282399105732359)
        ·
          refine ⟨2868124095423598658598539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1912082730282399105732359 2868124095423598658598539)
          ·
            refine ⟨4302186143135397987897809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2868124095423598658598539 4302186143135397987897809)
            ·
              refine ⟨3226639607351548490923357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4302186143135397987897809 3226639607351548490923357)
              ·
                refine ⟨1209989852756830684096259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3226639607351548490923357 1209989852756830684096259)
                ·
                  refine ⟨1814984779135246026144389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1209989852756830684096259 1814984779135246026144389)
                  ·
                    refine ⟨340309646087858629902073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1814984779135246026144389 340309646087858629902073)
                    ·
                      refine ⟨255232234565893972426555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 340309646087858629902073 255232234565893972426555)
                      ·
                        rfl

theorem cell23_497063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_497063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497063 prefixEnd_497063 := by exact prefixLift 497063
  have htrace : WordTrace (prefixWord ++ tailWord_497063) baseStart_497063 baseEnd_497063 := by
    simpa [prefixWord, tailWord_497063, baseEnd_497063] using wordTrace_append hprefix tailTrace_497063
  have hstable : (prefixWord ++ tailWord_497063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497063).length < 2 ^ (prefixWord ++ tailWord_497063).sum := by decide
  have hdescent : baseEnd_497063 < baseStart_497063 := by decide
  rcases family_descends (prefixWord ++ tailWord_497063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497096 : List Nat := [2, 1, 3, 1, 3, 1, 2, 2, 2, 3, 3]
def baseStart_497096 : Nat := 118140960795 + 497096 * 2 ^ 59
def prefixEnd_497096 : Nat := 4983230072969 + 3 ^ 40 * 497096 * 2
def baseEnd_497096 : Nat := 255249179427492343313903

theorem tailTrace_497096 : CollatzResearch.WordTrace tailWord_497096 prefixEnd_497096 255249179427492343313903 := by
  unfold tailWord_497096
  simp only [CollatzResearch.WordTrace]
  refine ⟨9065290303556782041447571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12087053738075709388596761 9065290303556782041447571)
  ·
    refine ⟨13597935455335173062171357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9065290303556782041447571 13597935455335173062171357)
    ·
      refine ⟨5099225795750689898314259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13597935455335173062171357 5099225795750689898314259)
      ·
        refine ⟨7648838693626034847471389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5099225795750689898314259 7648838693626034847471389)
        ·
          refine ⟨2868314510109763067801771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7648838693626034847471389 2868314510109763067801771)
          ·
            refine ⟨4302471765164644601702657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2868314510109763067801771 4302471765164644601702657)
            ·
              refine ⟨3226853823873483451276993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4302471765164644601702657 3226853823873483451276993)
              ·
                refine ⟨2420140367905112588457745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3226853823873483451276993 2420140367905112588457745)
                ·
                  refine ⟨1815105275928834441343309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2420140367905112588457745 1815105275928834441343309)
                  ·
                    refine ⟨680664478473312915503741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1815105275928834441343309 680664478473312915503741)
                    ·
                      refine ⟨255249179427492343313903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 680664478473312915503741 255249179427492343313903)
                      ·
                        rfl

theorem cell23_497096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_497096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497096 prefixEnd_497096 := by exact prefixLift 497096
  have htrace : WordTrace (prefixWord ++ tailWord_497096) baseStart_497096 baseEnd_497096 := by
    simpa [prefixWord, tailWord_497096, baseEnd_497096] using wordTrace_append hprefix tailTrace_497096
  have hstable : (prefixWord ++ tailWord_497096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497096).length < 2 ^ (prefixWord ++ tailWord_497096).sum := by decide
  have hdescent : baseEnd_497096 < baseStart_497096 := by decide
  rcases family_descends (prefixWord ++ tailWord_497096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497103 : List Nat := [1, 1, 2, 1, 1, 4, 6, 2, 5]
def baseStart_497103 : Nat := 118140960795 + 497103 * 2 ^ 59
def prefixEnd_497103 : Nat := 4983230072969 + 3 ^ 40 * 497103 * 2
def baseEnd_497103 : Nat := 28361419310230423991819

theorem tailTrace_497103 : CollatzResearch.WordTrace tailWord_497103 prefixEnd_497103 28361419310230423991819 := by
  unfold tailWord_497103
  simp only [CollatzResearch.WordTrace]
  refine ⟨18130835918088204278399963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12087223945392136185599975 18130835918088204278399963)
  ·
    refine ⟨27196253877132306417599945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18130835918088204278399963 27196253877132306417599945)
    ·
      refine ⟨20397190407849229813199959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27196253877132306417599945 20397190407849229813199959)
      ·
        refine ⟨30595785611773844719799939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20397190407849229813199959 30595785611773844719799939)
        ·
          refine ⟨45893678417660767079699909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30595785611773844719799939 45893678417660767079699909)
          ·
            refine ⟨8605064703311393827443733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45893678417660767079699909 8605064703311393827443733)
            ·
              refine ⟨403362407967721585661425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8605064703311393827443733 403362407967721585661425)
              ·
                refine ⟨302521805975791189246069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 403362407967721585661425 302521805975791189246069)
                ·
                  refine ⟨28361419310230423991819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 302521805975791189246069 28361419310230423991819)
                  ·
                    rfl

theorem cell23_497103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 2, 5].length) (baseStart_497103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497103 prefixEnd_497103 := by exact prefixLift 497103
  have htrace : WordTrace (prefixWord ++ tailWord_497103) baseStart_497103 baseEnd_497103 := by
    simpa [prefixWord, tailWord_497103, baseEnd_497103] using wordTrace_append hprefix tailTrace_497103
  have hstable : (prefixWord ++ tailWord_497103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497103).length < 2 ^ (prefixWord ++ tailWord_497103).sum := by decide
  have hdescent : baseEnd_497103 < baseStart_497103 := by decide
  rcases family_descends (prefixWord ++ tailWord_497103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497133 : List Nat := [1, 5, 1, 3, 2, 1, 1, 1, 1, 7]
def baseStart_497133 : Nat := 118140960795 + 497133 * 2 ^ 59
def prefixEnd_497133 : Nat := 4983230072969 + 3 ^ 40 * 497133 * 2
def baseEnd_497133 : Nat := 85089392737236232850411

theorem tailTrace_497133 : CollatzResearch.WordTrace tailWord_497133 prefixEnd_497133 85089392737236232850411 := by
  unfold tailWord_497133
  simp only [CollatzResearch.WordTrace]
  refine ⟨18131930107979519401992053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12087953405319679601328035 18131930107979519401992053)
  ·
    refine ⟨1699868447623079943936755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18131930107979519401992053 1699868447623079943936755)
    ·
      refine ⟨2549802671434619915905133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1699868447623079943936755 2549802671434619915905133)
      ·
        refine ⟨956176001787982468464425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2549802671434619915905133 956176001787982468464425)
        ·
          refine ⟨717132001340986851348319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 956176001787982468464425 717132001340986851348319)
          ·
            refine ⟨1075698002011480277022479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717132001340986851348319 1075698002011480277022479)
            ·
              refine ⟨1613547003017220415533719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1075698002011480277022479 1613547003017220415533719)
              ·
                refine ⟨2420320504525830623300579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1613547003017220415533719 2420320504525830623300579)
                ·
                  refine ⟨3630480756788745934950869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2420320504525830623300579 3630480756788745934950869)
                  ·
                    refine ⟨85089392737236232850411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3630480756788745934950869 85089392737236232850411)
                    ·
                      rfl

theorem cell23_497133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_497133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497133 prefixEnd_497133 := by exact prefixLift 497133
  have htrace : WordTrace (prefixWord ++ tailWord_497133) baseStart_497133 baseEnd_497133 := by
    simpa [prefixWord, tailWord_497133, baseEnd_497133] using wordTrace_append hprefix tailTrace_497133
  have hstable : (prefixWord ++ tailWord_497133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497133).length < 2 ^ (prefixWord ++ tailWord_497133).sum := by decide
  have hdescent : baseEnd_497133 < baseStart_497133 := by decide
  rcases family_descends (prefixWord ++ tailWord_497133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497136 : List Nat := [2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 4]
def baseStart_497136 : Nat := 118140960795 + 497136 * 2 ^ 59
def prefixEnd_497136 : Nat := 4983230072969 + 3 ^ 40 * 497136 * 2
def baseEnd_497136 : Nat := 255269718653672186813719

theorem tailTrace_497136 : CollatzResearch.WordTrace tailWord_497136 prefixEnd_497136 255269718653672186813719 := by
  unfold tailWord_497136
  simp only [CollatzResearch.WordTrace]
  refine ⟨9066019763484325457175631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12088026351312433942900841 9066019763484325457175631)
  ·
    refine ⟨13599029645226488185763447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9066019763484325457175631 13599029645226488185763447)
    ·
      refine ⟨20398544467839732278645171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13599029645226488185763447 20398544467839732278645171)
      ·
        refine ⟨30597816701759598417967757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20398544467839732278645171 30597816701759598417967757)
        ·
          refine ⟨11474181263159849406737909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30597816701759598417967757 11474181263159849406737909)
          ·
            refine ⟨1075704493421235881881679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11474181263159849406737909 1075704493421235881881679)
            ·
              refine ⟨1613556740131853822822519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1075704493421235881881679 1613556740131853822822519)
              ·
                refine ⟨2420335110197780734233779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1613556740131853822822519 2420335110197780734233779)
                ·
                  refine ⟨3630502665296671101350669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2420335110197780734233779 3630502665296671101350669)
                  ·
                    refine ⟨1361438499486251663006501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3630502665296671101350669 1361438499486251663006501)
                    ·
                      refine ⟨255269718653672186813719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1361438499486251663006501 255269718653672186813719)
                      ·
                        rfl

theorem cell23_497136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 4].length) (baseStart_497136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497136 prefixEnd_497136 := by exact prefixLift 497136
  have htrace : WordTrace (prefixWord ++ tailWord_497136) baseStart_497136 baseEnd_497136 := by
    simpa [prefixWord, tailWord_497136, baseEnd_497136] using wordTrace_append hprefix tailTrace_497136
  have hstable : (prefixWord ++ tailWord_497136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497136).length < 2 ^ (prefixWord ++ tailWord_497136).sum := by decide
  have hdescent : baseEnd_497136 < baseStart_497136 := by decide
  rcases family_descends (prefixWord ++ tailWord_497136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497139 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 5]
def baseStart_497139 : Nat := 118140960795 + 497139 * 2 ^ 59
def prefixEnd_497139 : Nat := 4983230072969 + 3 ^ 40 * 497139 * 2
def baseEnd_497139 : Nat := 255271259095635675076205

theorem tailTrace_497139 : CollatzResearch.WordTrace tailWord_497139 prefixEnd_497139 255271259095635675076205 := by
  unfold tailWord_497139
  simp only [CollatzResearch.WordTrace]
  refine ⟨18132148945957782426710471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12088099297305188284473647 18132148945957782426710471)
  ·
    refine ⟨27198223418936673640065707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18132148945957782426710471 27198223418936673640065707)
    ·
      refine ⟨40797335128405010460098561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27198223418936673640065707 40797335128405010460098561)
      ·
        refine ⟨30598001346303757845073921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40797335128405010460098561 30598001346303757845073921)
        ·
          refine ⟨22948501009727818383805441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30598001346303757845073921 22948501009727818383805441)
          ·
            refine ⟨17211375757295863787854081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22948501009727818383805441 17211375757295863787854081)
            ·
              refine ⟨12908531817971897840890561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17211375757295863787854081 12908531817971897840890561)
              ·
                refine ⟨9681398863478923380667921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12908531817971897840890561 9681398863478923380667921)
                ·
                  refine ⟨7261049147609192535500941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9681398863478923380667921 7261049147609192535500941)
                  ·
                    refine ⟨2722893430353447200812853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7261049147609192535500941 2722893430353447200812853)
                    ·
                      refine ⟨255271259095635675076205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2722893430353447200812853 255271259095635675076205)
                      ·
                        rfl

theorem cell23_497139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 5].length) (baseStart_497139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497139 prefixEnd_497139 := by exact prefixLift 497139
  have htrace : WordTrace (prefixWord ++ tailWord_497139) baseStart_497139 baseEnd_497139 := by
    simpa [prefixWord, tailWord_497139, baseEnd_497139] using wordTrace_append hprefix tailTrace_497139
  have hstable : (prefixWord ++ tailWord_497139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497139).length < 2 ^ (prefixWord ++ tailWord_497139).sum := by decide
  have hdescent : baseEnd_497139 < baseStart_497139 := by decide
  rcases family_descends (prefixWord ++ tailWord_497139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497146 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 5, 4]
def baseStart_497146 : Nat := 118140960795 + 497146 * 2 ^ 59
def prefixEnd_497146 : Nat := 4983230072969 + 3 ^ 40 * 497146 * 2
def baseEnd_497146 : Nat := 85091617820072382562891

theorem tailTrace_497146 : CollatzResearch.WordTrace tailWord_497146 prefixEnd_497146 85091617820072382562891 := by
  unfold tailWord_497146
  simp only [CollatzResearch.WordTrace]
  refine ⟨4533101064233105655553823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12088269504621615081476861 4533101064233105655553823)
  ·
    refine ⟨6799651596349658483330735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4533101064233105655553823 6799651596349658483330735)
    ·
      refine ⟨10199477394524487724996103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6799651596349658483330735 10199477394524487724996103)
      ·
        refine ⟨15299216091786731587494155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10199477394524487724996103 15299216091786731587494155)
        ·
          refine ⟨22948824137680097381241233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15299216091786731587494155 22948824137680097381241233)
          ·
            refine ⟨17211618103260073035930925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22948824137680097381241233 17211618103260073035930925)
            ·
              refine ⟨6454356788722527388474097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17211618103260073035930925 6454356788722527388474097)
              ·
                refine ⟨4840767591541895541355573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6454356788722527388474097 4840767591541895541355573)
                ·
                  refine ⟨453821961707052707002085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4840767591541895541355573 453821961707052707002085)
                  ·
                    refine ⟨85091617820072382562891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 453821961707052707002085 85091617820072382562891)
                    ·
                      rfl

theorem cell23_497146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 5, 4].length) (baseStart_497146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497146 prefixEnd_497146 := by exact prefixLift 497146
  have htrace : WordTrace (prefixWord ++ tailWord_497146) baseStart_497146 baseEnd_497146 := by
    simpa [prefixWord, tailWord_497146, baseEnd_497146] using wordTrace_append hprefix tailTrace_497146
  have hstable : (prefixWord ++ tailWord_497146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497146).length < 2 ^ (prefixWord ++ tailWord_497146).sum := by decide
  have hdescent : baseEnd_497146 < baseStart_497146 := by decide
  rcases family_descends (prefixWord ++ tailWord_497146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497253 : List Nat := [1, 3, 1, 3, 3, 2, 1, 2, 1, 6]
def baseStart_497253 : Nat := 118140960795 + 497253 * 2 ^ 59
def prefixEnd_497253 : Nat := 4983230072969 + 3 ^ 40 * 497253 * 2
def baseEnd_497253 : Nat := 85109931963416076350227

theorem tailTrace_497253 : CollatzResearch.WordTrace tailWord_497253 prefixEnd_497253 85109931963416076350227 := by
  unfold tailWord_497253
  simp only [CollatzResearch.WordTrace]
  refine ⟨18136306867544779896360413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12090871245029853264240275 18136306867544779896360413)
  ·
    refine ⟨6801115075329292461135155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18136306867544779896360413 6801115075329292461135155)
    ·
      refine ⟨10201672612993938691702733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6801115075329292461135155 10201672612993938691702733)
      ·
        refine ⟨3825627229872727009388525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10201672612993938691702733 3825627229872727009388525)
        ·
          refine ⟨1434610211202272628520697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3825627229872727009388525 1434610211202272628520697)
          ·
            refine ⟨1075957658401704471390523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1434610211202272628520697 1075957658401704471390523)
            ·
              refine ⟨1613936487602556707085785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1075957658401704471390523 1613936487602556707085785)
              ·
                refine ⟨1210452365701917530314339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1613936487602556707085785 1210452365701917530314339)
                ·
                  refine ⟨1815678548552876295471509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1210452365701917530314339 1815678548552876295471509)
                  ·
                    refine ⟨85109931963416076350227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1815678548552876295471509 85109931963416076350227)
                    ·
                      rfl

theorem cell23_497253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 6].length) (baseStart_497253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497253 prefixEnd_497253 := by exact prefixLift 497253
  have htrace : WordTrace (prefixWord ++ tailWord_497253) baseStart_497253 baseEnd_497253 := by
    simpa [prefixWord, tailWord_497253, baseEnd_497253] using wordTrace_append hprefix tailTrace_497253
  have hstable : (prefixWord ++ tailWord_497253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497253).length < 2 ^ (prefixWord ++ tailWord_497253).sum := by decide
  have hdescent : baseEnd_497253 < baseStart_497253 := by decide
  rcases family_descends (prefixWord ++ tailWord_497253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497266 : List Nat := [3, 2, 1, 2, 3, 12]
def baseStart_497266 : Nat := 118140960795 + 497266 * 2 ^ 59
def prefixEnd_497266 : Nat := 4983230072969 + 3 ^ 40 * 497266 * 2
def baseEnd_497266 : Nat := 1050767370941385506947

theorem tailTrace_497266 : CollatzResearch.WordTrace tailWord_497266 prefixEnd_497266 1050767370941385506947 := by
  unfold tailWord_497266
  simp only [CollatzResearch.WordTrace]
  refine ⟨4534195254124420779145913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12091187344331788744389101 4534195254124420779145913)
  ·
    refine ⟨3400646440593315584359435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4534195254124420779145913 3400646440593315584359435)
    ·
      refine ⟨5100969660889973376539153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3400646440593315584359435 5100969660889973376539153)
      ·
        refine ⟨3825727245667480032404365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5100969660889973376539153 3825727245667480032404365)
        ·
          refine ⟨1434647717125305012151637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3825727245667480032404365 1434647717125305012151637)
          ·
            refine ⟨1050767370941385506947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 1434647717125305012151637 1050767370941385506947)
            ·
              rfl

theorem cell23_497266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 12].length) (baseStart_497266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497266 prefixEnd_497266 := by exact prefixLift 497266
  have htrace : WordTrace (prefixWord ++ tailWord_497266) baseStart_497266 baseEnd_497266 := by
    simpa [prefixWord, tailWord_497266, baseEnd_497266] using wordTrace_append hprefix tailTrace_497266
  have hstable : (prefixWord ++ tailWord_497266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497266).length < 2 ^ (prefixWord ++ tailWord_497266).sum := by decide
  have hdescent : baseEnd_497266 < baseStart_497266 := by decide
  rcases family_descends (prefixWord ++ tailWord_497266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497290 : List Nat := [3, 1, 2, 3, 2, 2, 2, 1, 1, 2, 4]
def baseStart_497290 : Nat := 118140960795 + 497290 * 2 ^ 59
def prefixEnd_497290 : Nat := 4983230072969 + 3 ^ 40 * 497290 * 2
def baseEnd_497290 : Nat := 255348794674464584288011

theorem tailTrace_497290 : CollatzResearch.WordTrace tailWord_497290 prefixEnd_497290 255348794674464584288011 := by
  unfold tailWord_497290
  simp only [CollatzResearch.WordTrace]
  refine ⟨4534414092102683803864331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12091770912273823476971549 4534414092102683803864331)
  ·
    refine ⟨6801621138154025705796497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4534414092102683803864331 6801621138154025705796497)
    ·
      refine ⟨5101215853615519279347373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6801621138154025705796497 5101215853615519279347373)
      ·
        refine ⟨1912955945105819729755265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5101215853615519279347373 1912955945105819729755265)
        ·
          refine ⟨1434716958829364797316449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1912955945105819729755265 1434716958829364797316449)
          ·
            refine ⟨1076037719122023597987337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1434716958829364797316449 1076037719122023597987337)
            ·
              refine ⟨807028289341517698490503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1076037719122023597987337 807028289341517698490503)
              ·
                refine ⟨1210542434012276547735755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 807028289341517698490503 1210542434012276547735755)
                ·
                  refine ⟨1815813651018414821603633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1210542434012276547735755 1815813651018414821603633)
                  ·
                    refine ⟨1361860238263811116202725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1815813651018414821603633 1361860238263811116202725)
                    ·
                      refine ⟨255348794674464584288011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1361860238263811116202725 255348794674464584288011)
                      ·
                        rfl

theorem cell23_497290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_497290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497290 prefixEnd_497290 := by exact prefixLift 497290
  have htrace : WordTrace (prefixWord ++ tailWord_497290) baseStart_497290 baseEnd_497290 := by
    simpa [prefixWord, tailWord_497290, baseEnd_497290] using wordTrace_append hprefix tailTrace_497290
  have hstable : (prefixWord ++ tailWord_497290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497290).length < 2 ^ (prefixWord ++ tailWord_497290).sum := by decide
  have hdescent : baseEnd_497290 < baseStart_497290 := by decide
  rcases family_descends (prefixWord ++ tailWord_497290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497311 : List Nat := [1, 1, 2, 7, 2, 1, 2, 1, 1, 1, 4]
def baseStart_497311 : Nat := 118140960795 + 497311 * 2 ^ 59
def prefixEnd_497311 : Nat := 4983230072969 + 3 ^ 40 * 497311 * 2
def baseEnd_497311 : Nat := 255359577768209002125415

theorem tailTrace_497311 : CollatzResearch.WordTrace tailWord_497311 prefixEnd_497311 255359577768209002125415 := by
  unfold tailWord_497311
  simp only [CollatzResearch.WordTrace]
  refine ⟨18138422301334655801971787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12092281534223103867981191 18138422301334655801971787)
  ·
    refine ⟨27207633452001983702957681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18138422301334655801971787 27207633452001983702957681)
    ·
      refine ⟨20405725089001487777218261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27207633452001983702957681 20405725089001487777218261)
      ·
        refine ⟨478259181773472369778553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 20405725089001487777218261 478259181773472369778553)
        ·
          refine ⟨358694386330104277333915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478259181773472369778553 358694386330104277333915)
          ·
            refine ⟨538041579495156416000873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358694386330104277333915 538041579495156416000873)
            ·
              refine ⟨403531184621367312000655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538041579495156416000873 403531184621367312000655)
              ·
                refine ⟨605296776932050968000983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403531184621367312000655 605296776932050968000983)
                ·
                  refine ⟨907945165398076452001475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 605296776932050968000983 907945165398076452001475)
                  ·
                    refine ⟨1361917748097114678002213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 907945165398076452001475 1361917748097114678002213)
                    ·
                      refine ⟨255359577768209002125415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1361917748097114678002213 255359577768209002125415)
                      ·
                        rfl

theorem cell23_497311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_497311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497311 prefixEnd_497311 := by exact prefixLift 497311
  have htrace : WordTrace (prefixWord ++ tailWord_497311) baseStart_497311 baseEnd_497311 := by
    simpa [prefixWord, tailWord_497311, baseEnd_497311] using wordTrace_append hprefix tailTrace_497311
  have hstable : (prefixWord ++ tailWord_497311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497311).length < 2 ^ (prefixWord ++ tailWord_497311).sum := by decide
  have hdescent : baseEnd_497311 < baseStart_497311 := by decide
  rcases family_descends (prefixWord ++ tailWord_497311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497314 : List Nat := [3, 3, 1, 4, 1, 1, 1, 3, 1, 2, 3]
def baseStart_497314 : Nat := 118140960795 + 497314 * 2 ^ 59
def prefixEnd_497314 : Nat := 4983230072969 + 3 ^ 40 * 497314 * 2
def baseEnd_497314 : Nat := 255361118210172490387901

theorem tailTrace_497314 : CollatzResearch.WordTrace tailWord_497314 prefixEnd_497314 255361118210172490387901 := by
  unfold tailWord_497314
  simp only [CollatzResearch.WordTrace]
  refine ⟨4534632930080946828582749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12092354480215858209553997 4534632930080946828582749)
  ·
    refine ⟨1700487348780355060718531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4534632930080946828582749 1700487348780355060718531)
    ·
      refine ⟨2550731023170532591077797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1700487348780355060718531 2550731023170532591077797)
      ·
        refine ⟨478262066844474860827087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2550731023170532591077797 478262066844474860827087)
        ·
          refine ⟨717393100266712291240631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478262066844474860827087 717393100266712291240631)
          ·
            refine ⟨1076089650400068436860947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717393100266712291240631 1076089650400068436860947)
            ·
              refine ⟨1614134475600102655291421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1076089650400068436860947 1614134475600102655291421)
              ·
                refine ⟨605300428350038495734283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1614134475600102655291421 605300428350038495734283)
                ·
                  refine ⟨907950642525057743601425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 605300428350038495734283 907950642525057743601425)
                  ·
                    refine ⟨680962981893793307701069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 907950642525057743601425 680962981893793307701069)
                    ·
                      refine ⟨255361118210172490387901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 680962981893793307701069 255361118210172490387901)
                      ·
                        rfl

theorem cell23_497314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_497314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497314 prefixEnd_497314 := by exact prefixLift 497314
  have htrace : WordTrace (prefixWord ++ tailWord_497314) baseStart_497314 baseEnd_497314 := by
    simpa [prefixWord, tailWord_497314, baseEnd_497314] using wordTrace_append hprefix tailTrace_497314
  have hstable : (prefixWord ++ tailWord_497314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497314).length < 2 ^ (prefixWord ++ tailWord_497314).sum := by decide
  have hdescent : baseEnd_497314 < baseStart_497314 := by decide
  rcases family_descends (prefixWord ++ tailWord_497314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497354 : List Nat := [3, 1, 2, 1, 5, 1, 2, 2, 1, 3, 2]
def baseStart_497354 : Nat := 118140960795 + 497354 * 2 ^ 59
def prefixEnd_497354 : Nat := 4983230072969 + 3 ^ 40 * 497354 * 2
def baseEnd_497354 : Nat := 255381657436352333887717

theorem tailTrace_497354 : CollatzResearch.WordTrace tailWord_497354 prefixEnd_497354 255381657436352333887717 := by
  unfold tailWord_497354
  simp only [CollatzResearch.WordTrace]
  refine ⟨4534997660044718536446779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12093327093452582763858077 4534997660044718536446779)
  ·
    refine ⟨6802496490067077804670169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4534997660044718536446779 6802496490067077804670169)
    ·
      refine ⟨5101872367550308353502627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6802496490067077804670169 5101872367550308353502627)
      ·
        refine ⟨7652808551325462530253941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5101872367550308353502627 7652808551325462530253941)
        ·
          refine ⟨717450801686762112211307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7652808551325462530253941 717450801686762112211307)
          ·
            refine ⟨1076176202530143168316961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717450801686762112211307 1076176202530143168316961)
            ·
              refine ⟨807132151897607376237721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1076176202530143168316961 807132151897607376237721)
              ·
                refine ⟨605349113923205532178291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 807132151897607376237721 605349113923205532178291)
                ·
                  refine ⟨908023670884808298267437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 605349113923205532178291 908023670884808298267437)
                  ·
                    refine ⟨340508876581803111850289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 908023670884808298267437 340508876581803111850289)
                    ·
                      refine ⟨255381657436352333887717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 340508876581803111850289 255381657436352333887717)
                      ·
                        rfl

theorem cell23_497354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 1, 3, 2].length) (baseStart_497354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497354 prefixEnd_497354 := by exact prefixLift 497354
  have htrace : WordTrace (prefixWord ++ tailWord_497354) baseStart_497354 baseEnd_497354 := by
    simpa [prefixWord, tailWord_497354, baseEnd_497354] using wordTrace_append hprefix tailTrace_497354
  have hstable : (prefixWord ++ tailWord_497354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497354).length < 2 ^ (prefixWord ++ tailWord_497354).sum := by decide
  have hdescent : baseEnd_497354 < baseStart_497354 := by decide
  rcases family_descends (prefixWord ++ tailWord_497354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497440 : List Nat := [2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 4]
def baseStart_497440 : Nat := 118140960795 + 497440 * 2 ^ 59
def prefixEnd_497440 : Nat := 4983230072969 + 3 ^ 40 * 497440 * 2
def baseEnd_497440 : Nat := 255425816772638997412321

theorem tailTrace_497440 : CollatzResearch.WordTrace tailWord_497440 prefixEnd_497440 255425816772638997412321 := by
  unfold tailWord_497440
  simp only [CollatzResearch.WordTrace]
  refine ⟨9071563658933655416708887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12095418211911540555611849 9071563658933655416708887)
  ·
    refine ⟨13607345488400483125063331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9071563658933655416708887 13607345488400483125063331)
    ·
      refine ⟨20411018232600724687594997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13607345488400483125063331 20411018232600724687594997)
      ·
        refine ⟨1913532959306317939462031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20411018232600724687594997 1913532959306317939462031)
        ·
          refine ⟨2870299438959476909193047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1913532959306317939462031 2870299438959476909193047)
          ·
            refine ⟨4305449158439215363789571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2870299438959476909193047 4305449158439215363789571)
            ·
              refine ⟨6458173737658823045684357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4305449158439215363789571 6458173737658823045684357)
              ·
                refine ⟨1210907575811029321065817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6458173737658823045684357 1210907575811029321065817)
                ·
                  refine ⟨908180681858271990799363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1210907575811029321065817 908180681858271990799363)
                  ·
                    refine ⟨1362271022787407986199045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 908180681858271990799363 1362271022787407986199045)
                    ·
                      refine ⟨255425816772638997412321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1362271022787407986199045 255425816772638997412321)
                      ·
                        rfl

theorem cell23_497440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_497440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497440 prefixEnd_497440 := by exact prefixLift 497440
  have htrace : WordTrace (prefixWord ++ tailWord_497440) baseStart_497440 baseEnd_497440 := by
    simpa [prefixWord, tailWord_497440, baseEnd_497440] using wordTrace_append hprefix tailTrace_497440
  have hstable : (prefixWord ++ tailWord_497440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497440).length < 2 ^ (prefixWord ++ tailWord_497440).sum := by decide
  have hdescent : baseEnd_497440 < baseStart_497440 := by decide
  rcases family_descends (prefixWord ++ tailWord_497440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497457 : List Nat := [1, 2, 2, 3, 2, 3, 1, 1, 2, 4, 2]
def baseStart_497457 : Nat := 118140960795 + 497457 * 2 ^ 59
def prefixEnd_497457 : Nat := 4983230072969 + 3 ^ 40 * 497457 * 2
def baseEnd_497457 : Nat := 255434545943765430899743

theorem tailTrace_497457 : CollatzResearch.WordTrace tailWord_497457 prefixEnd_497457 255434545943765430899743 := by
  unfold tailWord_497457
  simp only [CollatzResearch.WordTrace]
  refine ⟨18143747358805722736786625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12095831572537148491191083 18143747358805722736786625)
  ·
    refine ⟨13607810519104292052589969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18143747358805722736786625 13607810519104292052589969)
    ·
      refine ⟨10205857889328219039442477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13607810519104292052589969 10205857889328219039442477)
      ·
        refine ⟨3827196708498082139790929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10205857889328219039442477 3827196708498082139790929)
        ·
          refine ⟨2870397531373561604843197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3827196708498082139790929 2870397531373561604843197)
          ·
            refine ⟨1076399074265085601816199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2870397531373561604843197 1076399074265085601816199)
            ·
              refine ⟨1614598611397628402724299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1076399074265085601816199 1614598611397628402724299)
              ·
                refine ⟨2421897917096442604086449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1614598611397628402724299 2421897917096442604086449)
                ·
                  refine ⟨1816423437822331953064837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2421897917096442604086449 1816423437822331953064837)
                  ·
                    refine ⟨340579394591687241199657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1816423437822331953064837 340579394591687241199657)
                    ·
                      refine ⟨255434545943765430899743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 340579394591687241199657 255434545943765430899743)
                      ·
                        rfl

theorem cell23_497457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_497457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497457 prefixEnd_497457 := by exact prefixLift 497457
  have htrace : WordTrace (prefixWord ++ tailWord_497457) baseStart_497457 baseEnd_497457 := by
    simpa [prefixWord, tailWord_497457, baseEnd_497457] using wordTrace_append hprefix tailTrace_497457
  have hstable : (prefixWord ++ tailWord_497457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497457).length < 2 ^ (prefixWord ++ tailWord_497457).sum := by decide
  have hdescent : baseEnd_497457 < baseStart_497457 := by decide
  rcases family_descends (prefixWord ++ tailWord_497457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497517 : List Nat := [1, 5, 1, 1, 1, 1, 3, 2, 1, 5, 2]
def baseStart_497517 : Nat := 118140960795 + 497517 * 2 ^ 59
def prefixEnd_497517 : Nat := 4983230072969 + 3 ^ 40 * 497517 * 2
def baseEnd_497517 : Nat := 255465354783035196149467

theorem tailTrace_497517 : CollatzResearch.WordTrace tailWord_497517 prefixEnd_497517 255465354783035196149467 := by
  unfold tailWord_497517
  simp only [CollatzResearch.WordTrace]
  refine ⟨18145935738588352983970805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12097290492392235322647203 18145935738588352983970805)
  ·
    refine ⟨1701181475492658092247263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18145935738588352983970805 1701181475492658092247263)
    ·
      refine ⟨2551772213238987138370895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1701181475492658092247263 2551772213238987138370895)
      ·
        refine ⟨3827658319858480707556343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2551772213238987138370895 3827658319858480707556343)
        ·
          refine ⟨5741487479787721061334515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3827658319858480707556343 5741487479787721061334515)
          ·
            refine ⟨8612231219681581592001773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5741487479787721061334515 8612231219681581592001773)
            ·
              refine ⟨3229586707380593097000665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8612231219681581592001773 3229586707380593097000665)
              ·
                refine ⟨2422190030535444822750499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3229586707380593097000665 2422190030535444822750499)
                ·
                  refine ⟨3633285045803167234125749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2422190030535444822750499 3633285045803167234125749)
                  ·
                    refine ⟨340620473044046928199289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3633285045803167234125749 340620473044046928199289)
                    ·
                      refine ⟨255465354783035196149467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 340620473044046928199289 255465354783035196149467)
                      ·
                        rfl

theorem cell23_497517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_497517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497517 prefixEnd_497517 := by exact prefixLift 497517
  have htrace : WordTrace (prefixWord ++ tailWord_497517) baseStart_497517 baseEnd_497517 := by
    simpa [prefixWord, tailWord_497517, baseEnd_497517] using wordTrace_append hprefix tailTrace_497517
  have hstable : (prefixWord ++ tailWord_497517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497517).length < 2 ^ (prefixWord ++ tailWord_497517).sum := by decide
  have hdescent : baseEnd_497517 < baseStart_497517 := by decide
  rcases family_descends (prefixWord ++ tailWord_497517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497530 : List Nat := [3, 1, 1, 1, 1, 1, 4, 3, 3, 1, 4]
def baseStart_497530 : Nat := 118140960795 + 497530 * 2 ^ 59
def prefixEnd_497530 : Nat := 4983230072969 + 3 ^ 40 * 497530 * 2
def baseEnd_497530 : Nat := 255472030031543645286907

theorem tailTrace_497530 : CollatzResearch.WordTrace tailWord_497530 prefixEnd_497530 255472030031543645286907 := by
  unfold tailWord_497530
  simp only [CollatzResearch.WordTrace]
  refine ⟨4536602471885314051048511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12097606591694170802796029 4536602471885314051048511)
  ·
    refine ⟨6804903707827971076572767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4536602471885314051048511 6804903707827971076572767)
    ·
      refine ⟨10207355561741956614859151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6804903707827971076572767 10207355561741956614859151)
      ·
        refine ⟨15311033342612934922288727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10207355561741956614859151 15311033342612934922288727)
        ·
          refine ⟨22966550013919402383433091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15311033342612934922288727 22966550013919402383433091)
          ·
            refine ⟨34449825020879103575149637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22966550013919402383433091 34449825020879103575149637)
            ·
              refine ⟨6459342191414831920340557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34449825020879103575149637 6459342191414831920340557)
              ·
                refine ⟨2422253321780561970127709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6459342191414831920340557 2422253321780561970127709)
                ·
                  refine ⟨908344995667710738797891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2422253321780561970127709 908344995667710738797891)
                  ·
                    refine ⟨1362517493501566108196837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 908344995667710738797891 1362517493501566108196837)
                    ·
                      refine ⟨255472030031543645286907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1362517493501566108196837 255472030031543645286907)
                      ·
                        rfl

theorem cell23_497530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_497530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497530 prefixEnd_497530 := by exact prefixLift 497530
  have htrace : WordTrace (prefixWord ++ tailWord_497530) baseStart_497530 baseEnd_497530 := by
    simpa [prefixWord, tailWord_497530, baseEnd_497530] using wordTrace_append hprefix tailTrace_497530
  have hstable : (prefixWord ++ tailWord_497530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497530).length < 2 ^ (prefixWord ++ tailWord_497530).sum := by decide
  have hdescent : baseEnd_497530 < baseStart_497530 := by decide
  rcases family_descends (prefixWord ++ tailWord_497530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497540 : List Nat := [2, 3, 2, 1, 1, 1, 2, 4, 1, 6]
def baseStart_497540 : Nat := 118140960795 + 497540 * 2 ^ 59
def prefixEnd_497540 : Nat := 4983230072969 + 3 ^ 40 * 497540 * 2
def baseEnd_497540 : Nat := 85159054946029535387287

theorem tailTrace_497540 : CollatzResearch.WordTrace tailWord_497540 prefixEnd_497540 85159054946029535387287 := by
  unfold tailWord_497540
  simp only [CollatzResearch.WordTrace]
  refine ⟨9073387308752513956029037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12097849745003351941372049 9073387308752513956029037)
  ·
    refine ⟨3402520240782192733510889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9073387308752513956029037 3402520240782192733510889)
    ·
      refine ⟨2551890180586644550133167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3402520240782192733510889 2551890180586644550133167)
      ·
        refine ⟨3827835270879966825199751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2551890180586644550133167 3827835270879966825199751)
        ·
          refine ⟨5741752906319950237799627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3827835270879966825199751 5741752906319950237799627)
          ·
            refine ⟨8612629359479925356699441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5741752906319950237799627 8612629359479925356699441)
            ·
              refine ⟨6459472019609944017524581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8612629359479925356699441 6459472019609944017524581)
              ·
                refine ⟨1211151003676864503285859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6459472019609944017524581 1211151003676864503285859)
                ·
                  refine ⟨1816726505515296754928789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1211151003676864503285859 1816726505515296754928789)
                  ·
                    refine ⟨85159054946029535387287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1816726505515296754928789 85159054946029535387287)
                    ·
                      rfl

theorem cell23_497540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_497540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497540 prefixEnd_497540 := by exact prefixLift 497540
  have htrace : WordTrace (prefixWord ++ tailWord_497540) baseStart_497540 baseEnd_497540 := by
    simpa [prefixWord, tailWord_497540, baseEnd_497540] using wordTrace_append hprefix tailTrace_497540
  have hstable : (prefixWord ++ tailWord_497540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497540).length < 2 ^ (prefixWord ++ tailWord_497540).sum := by decide
  have hdescent : baseEnd_497540 < baseStart_497540 := by decide
  rcases family_descends (prefixWord ++ tailWord_497540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497553 : List Nat := [1, 2, 2, 1, 1, 1, 15]
def baseStart_497553 : Nat := 118140960795 + 497553 * 2 ^ 59
def prefixEnd_497553 : Nat := 4983230072969 + 3 ^ 40 * 497553 * 2
def baseEnd_497553 : Nat := 3154121482550580929621

theorem tailTrace_497553 : CollatzResearch.WordTrace tailWord_497553 prefixEnd_497553 3154121482550580929621 := by
  unfold tailWord_497553
  simp only [CollatzResearch.WordTrace]
  refine ⟨18147248766457931132281313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12098165844305287421520875 18147248766457931132281313)
  ·
    refine ⟨13610436574843448349210985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18147248766457931132281313 13610436574843448349210985)
    ·
      refine ⟨10207827431132586261908239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13610436574843448349210985 10207827431132586261908239)
      ·
        refine ⟨15311741146698879392862359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10207827431132586261908239 15311741146698879392862359)
        ·
          refine ⟨22967611720048319089293539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15311741146698879392862359 22967611720048319089293539)
          ·
            refine ⟨34451417580072478633940309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22967611720048319089293539 34451417580072478633940309)
            ·
              refine ⟨3154121482550580929621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 15 34451417580072478633940309 3154121482550580929621)
              ·
                rfl

theorem cell23_497553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 15].length) (baseStart_497553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497553 prefixEnd_497553 := by exact prefixLift 497553
  have htrace : WordTrace (prefixWord ++ tailWord_497553) baseStart_497553 baseEnd_497553 := by
    simpa [prefixWord, tailWord_497553, baseEnd_497553] using wordTrace_append hprefix tailTrace_497553
  have hstable : (prefixWord ++ tailWord_497553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497553).length < 2 ^ (prefixWord ++ tailWord_497553).sum := by decide
  have hdescent : baseEnd_497553 < baseStart_497553 := by decide
  rcases family_descends (prefixWord ++ tailWord_497553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497557 : List Nat := [1, 3, 2, 1, 1, 3, 2, 4, 2, 4]
def baseStart_497557 : Nat := 118140960795 + 497557 * 2 ^ 59
def prefixEnd_497557 : Nat := 4983230072969 + 3 ^ 40 * 497557 * 2
def baseEnd_497557 : Nat := 85161964669738346549761

theorem tailTrace_497557 : CollatzResearch.WordTrace tailWord_497557 prefixEnd_497557 85161964669738346549761 := by
  unfold tailWord_497557
  simp only [CollatzResearch.WordTrace]
  refine ⟨18147394658443439815426925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12098263105628959876951283 18147394658443439815426925)
  ·
    refine ⟨6805272996916289930785097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18147394658443439815426925 6805272996916289930785097)
    ·
      refine ⟨5103954747687217448088823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6805272996916289930785097 5103954747687217448088823)
      ·
        refine ⟨7655932121530826172133235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5103954747687217448088823 7655932121530826172133235)
        ·
          refine ⟨11483898182296239258199853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7655932121530826172133235 11483898182296239258199853)
          ·
            refine ⟨4306461818361089721824945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11483898182296239258199853 4306461818361089721824945)
            ·
              refine ⟨3229846363770817291368709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4306461818361089721824945 3229846363770817291368709)
              ·
                refine ⟨605596193207028242131633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3229846363770817291368709 605596193207028242131633)
                ·
                  refine ⟨454197144905271181598725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 605596193207028242131633 454197144905271181598725)
                  ·
                    refine ⟨85161964669738346549761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 454197144905271181598725 85161964669738346549761)
                    ·
                      rfl

theorem cell23_497557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_497557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497557 prefixEnd_497557 := by exact prefixLift 497557
  have htrace : WordTrace (prefixWord ++ tailWord_497557) baseStart_497557 baseEnd_497557 := by
    simpa [prefixWord, tailWord_497557, baseEnd_497557] using wordTrace_append hprefix tailTrace_497557
  have hstable : (prefixWord ++ tailWord_497557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497557).length < 2 ^ (prefixWord ++ tailWord_497557).sum := by decide
  have hdescent : baseEnd_497557 < baseStart_497557 := by decide
  rcases family_descends (prefixWord ++ tailWord_497557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497597 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 3, 3, 3]
def baseStart_497597 : Nat := 118140960795 + 497597 * 2 ^ 59
def prefixEnd_497597 : Nat := 4983230072969 + 3 ^ 40 * 497597 * 2
def baseEnd_497597 : Nat := 255506433235394883149099

theorem tailTrace_497597 : CollatzResearch.WordTrace tailWord_497597 prefixEnd_497597 255506433235394883149099 := by
  unfold tailWord_497597
  simp only [CollatzResearch.WordTrace]
  refine ⟨18148853578298526646883045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12099235718865684431255363 18148853578298526646883045)
  ·
    refine ⟨3402910045930973746290571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18148853578298526646883045 3402910045930973746290571)
    ·
      refine ⟨5104365068896460619435857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3402910045930973746290571 5104365068896460619435857)
      ·
        refine ⟨3828273801672345464576893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5104365068896460619435857 3828273801672345464576893)
        ·
          refine ⟨1435602675627129549216335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3828273801672345464576893 1435602675627129549216335)
          ·
            refine ⟨2153404013440694323824503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1435602675627129549216335 2153404013440694323824503)
            ·
              refine ⟨3230106020161041485736755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2153404013440694323824503 3230106020161041485736755)
              ·
                refine ⟨4845159030241562228605133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3230106020161041485736755 4845159030241562228605133)
                ·
                  refine ⟨1816934636340585835726925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4845159030241562228605133 1816934636340585835726925)
                  ·
                    refine ⟨681350488627719688397597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1816934636340585835726925 681350488627719688397597)
                    ·
                      refine ⟨255506433235394883149099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 681350488627719688397597 255506433235394883149099)
                      ·
                        rfl

theorem cell23_497597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_497597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497597 prefixEnd_497597 := by exact prefixLift 497597
  have htrace : WordTrace (prefixWord ++ tailWord_497597) baseStart_497597 baseEnd_497597 := by
    simpa [prefixWord, tailWord_497597, baseEnd_497597] using wordTrace_append hprefix tailTrace_497597
  have hstable : (prefixWord ++ tailWord_497597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497597).length < 2 ^ (prefixWord ++ tailWord_497597).sum := by decide
  have hdescent : baseEnd_497597 < baseStart_497597 := by decide
  rcases family_descends (prefixWord ++ tailWord_497597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497610 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 2, 2, 5]
def baseStart_497610 : Nat := 118140960795 + 497610 * 2 ^ 59
def prefixEnd_497610 : Nat := 4983230072969 + 3 ^ 40 * 497610 * 2
def baseEnd_497610 : Nat := 255513108483903332286539

theorem tailTrace_497610 : CollatzResearch.WordTrace tailWord_497610 prefixEnd_497610 255513108483903332286539 := by
  unfold tailWord_497610
  simp only [CollatzResearch.WordTrace]
  refine ⟨4537331931812857466776571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12099551818167619911404189 4537331931812857466776571)
  ·
    refine ⟨6805997897719286200164857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4537331931812857466776571 6805997897719286200164857)
    ·
      refine ⟨5104498423289464650123643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6805997897719286200164857 5104498423289464650123643)
      ·
        refine ⟨7656747634934196975185465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5104498423289464650123643 7656747634934196975185465)
        ·
          refine ⟨5742560726200647731389099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7656747634934196975185465 5742560726200647731389099)
          ·
            refine ⟨8613841089300971597083649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5742560726200647731389099 8613841089300971597083649)
            ·
              refine ⟨6460380816975728697812737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8613841089300971597083649 6460380816975728697812737)
              ·
                refine ⟨4845285612731796523359553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6460380816975728697812737 4845285612731796523359553)
                ·
                  refine ⟨3633964209548847392519665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4845285612731796523359553 3633964209548847392519665)
                  ·
                    refine ⟨2725473157161635544389749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3633964209548847392519665 2725473157161635544389749)
                    ·
                      refine ⟨255513108483903332286539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2725473157161635544389749 255513108483903332286539)
                      ·
                        rfl

theorem cell23_497610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_497610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497610 prefixEnd_497610 := by exact prefixLift 497610
  have htrace : WordTrace (prefixWord ++ tailWord_497610) baseStart_497610 baseEnd_497610 := by
    simpa [prefixWord, tailWord_497610, baseEnd_497610] using wordTrace_append hprefix tailTrace_497610
  have hstable : (prefixWord ++ tailWord_497610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497610).length < 2 ^ (prefixWord ++ tailWord_497610).sum := by decide
  have hdescent : baseEnd_497610 < baseStart_497610 := by decide
  rcases family_descends (prefixWord ++ tailWord_497610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497628 : List Nat := [2, 2, 6, 1, 1, 1, 2, 1, 1, 2, 4]
def baseStart_497628 : Nat := 118140960795 + 497628 * 2 ^ 59
def prefixEnd_497628 : Nat := 4983230072969 + 3 ^ 40 * 497628 * 2
def baseEnd_497628 : Nat := 255522351135684261861457

theorem tailTrace_497628 : CollatzResearch.WordTrace tailWord_497628 prefixEnd_497628 255522351135684261861457 := by
  unfold tailWord_497628
  simp only [CollatzResearch.WordTrace]
  refine ⟨9074992120593109470630769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12099989494124145960841025 9074992120593109470630769)
  ·
    refine ⟨6806244090444832102973077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9074992120593109470630769 6806244090444832102973077)
    ·
      refine ⟨319042691739601504826863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6806244090444832102973077 319042691739601504826863)
      ·
        refine ⟨478564037609402257240295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319042691739601504826863 478564037609402257240295)
        ·
          refine ⟨717846056414103385860443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478564037609402257240295 717846056414103385860443)
          ·
            refine ⟨1076769084621155078790665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717846056414103385860443 1076769084621155078790665)
            ·
              refine ⟨807576813465866309092999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1076769084621155078790665 807576813465866309092999)
              ·
                refine ⟨1211365220198799463639499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 807576813465866309092999 1211365220198799463639499)
                ·
                  refine ⟨1817047830298199195459249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1211365220198799463639499 1817047830298199195459249)
                  ·
                    refine ⟨1362785872723649396594437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1817047830298199195459249 1362785872723649396594437)
                    ·
                      refine ⟨255522351135684261861457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1362785872723649396594437 255522351135684261861457)
                      ·
                        rfl

theorem cell23_497628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_497628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497628 prefixEnd_497628 := by exact prefixLift 497628
  have htrace : WordTrace (prefixWord ++ tailWord_497628) baseStart_497628 baseEnd_497628 := by
    simpa [prefixWord, tailWord_497628, baseEnd_497628] using wordTrace_append hprefix tailTrace_497628
  have hstable : (prefixWord ++ tailWord_497628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497628).length < 2 ^ (prefixWord ++ tailWord_497628).sum := by decide
  have hdescent : baseEnd_497628 < baseStart_497628 := by decide
  rcases family_descends (prefixWord ++ tailWord_497628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497660 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 9]
def baseStart_497660 : Nat := 118140960795 + 497660 * 2 ^ 59
def prefixEnd_497660 : Nat := 4983230072969 + 3 ^ 40 * 497660 * 2
def baseEnd_497660 : Nat := 28393198057403126295701

theorem tailTrace_497660 : CollatzResearch.WordTrace tailWord_497660 prefixEnd_497660 28393198057403126295701 := by
  unfold tailWord_497660
  simp only [CollatzResearch.WordTrace]
  refine ⟨9075575688535144203213217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12100767584713525604284289 9075575688535144203213217)
  ·
    refine ⟨6806681766401358152409913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9075575688535144203213217 6806681766401358152409913)
    ·
      refine ⟨5105011324801018614307435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6806681766401358152409913 5105011324801018614307435)
      ·
        refine ⟨7657516987201527921461153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5105011324801018614307435 7657516987201527921461153)
        ·
          refine ⟨5743137740401145941095865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7657516987201527921461153 5743137740401145941095865)
          ·
            refine ⟨4307353305300859455821899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5743137740401145941095865 4307353305300859455821899)
            ·
              refine ⟨6461029957951289183732849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4307353305300859455821899 6461029957951289183732849)
              ·
                refine ⟨4845772468463466887799637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6461029957951289183732849 4845772468463466887799637)
                ·
                  refine ⟨28393198057403126295701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4845772468463466887799637 28393198057403126295701)
                  ·
                    rfl

theorem cell23_497660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 9].length) (baseStart_497660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497660 prefixEnd_497660 := by exact prefixLift 497660
  have htrace : WordTrace (prefixWord ++ tailWord_497660) baseStart_497660 baseEnd_497660 := by
    simpa [prefixWord, tailWord_497660, baseEnd_497660] using wordTrace_append hprefix tailTrace_497660
  have hstable : (prefixWord ++ tailWord_497660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497660).length < 2 ^ (prefixWord ++ tailWord_497660).sum := by decide
  have hdescent : baseEnd_497660 < baseStart_497660 := by decide
  rcases family_descends (prefixWord ++ tailWord_497660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497671 : List Nat := [1, 1, 4, 3, 1, 3, 1, 1, 4, 2, 2]
def baseStart_497671 : Nat := 118140960795 + 497671 * 2 ^ 59
def prefixEnd_497671 : Nat := 4983230072969 + 3 ^ 40 * 497671 * 2
def baseEnd_497671 : Nat := 255544430803827593623759

theorem tailTrace_497671 : CollatzResearch.WordTrace tailWord_497671 prefixEnd_497671 255544430803827593623759 := by
  unfold tailWord_497671
  simp only [CollatzResearch.WordTrace]
  refine ⟨18151552580030437285076867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12101035053353624856717911 18151552580030437285076867)
  ·
    refine ⟨27227328870045655927615301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18151552580030437285076867 27227328870045655927615301)
    ·
      refine ⟨5105124163133560486427869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27227328870045655927615301 5105124163133560486427869)
      ·
        refine ⟨1914421561175085182410451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5105124163133560486427869 1914421561175085182410451)
        ·
          refine ⟨2871632341762627773615677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1914421561175085182410451 2871632341762627773615677)
          ·
            refine ⟨1076862128160985415105879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2871632341762627773615677 1076862128160985415105879)
            ·
              refine ⟨1615293192241478122658819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1076862128160985415105879 1615293192241478122658819)
              ·
                refine ⟨2422939788362217183988229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1615293192241478122658819 2422939788362217183988229)
                ·
                  refine ⟨454301210317915721997793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2422939788362217183988229 454301210317915721997793)
                  ·
                    refine ⟨340725907738436791498345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 454301210317915721997793 340725907738436791498345)
                    ·
                      refine ⟨255544430803827593623759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 340725907738436791498345 255544430803827593623759)
                      ·
                        rfl

theorem cell23_497671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_497671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497671 prefixEnd_497671 := by exact prefixLift 497671
  have htrace : WordTrace (prefixWord ++ tailWord_497671) baseStart_497671 baseEnd_497671 := by
    simpa [prefixWord, tailWord_497671, baseEnd_497671] using wordTrace_append hprefix tailTrace_497671
  have hstable : (prefixWord ++ tailWord_497671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497671).length < 2 ^ (prefixWord ++ tailWord_497671).sum := by decide
  have hdescent : baseEnd_497671 < baseStart_497671 := by decide
  rcases family_descends (prefixWord ++ tailWord_497671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497688 : List Nat := [2, 1, 2, 3, 2, 1, 5, 1, 2, 2, 2]
def baseStart_497688 : Nat := 118140960795 + 497688 * 2 ^ 59
def prefixEnd_497688 : Nat := 4983230072969 + 3 ^ 40 * 497688 * 2
def baseEnd_497688 : Nat := 255553159974954027111181

theorem tailTrace_497688 : CollatzResearch.WordTrace tailWord_497688 prefixEnd_497688 255553159974954027111181 := by
  unfold tailWord_497688
  simp only [CollatzResearch.WordTrace]
  refine ⟨9076086310484424594222859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12101448413979232792297145 9076086310484424594222859)
  ·
    refine ⟨13614129465726636891334289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9076086310484424594222859 13614129465726636891334289)
    ·
      refine ⟨10210597099294977668500717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13614129465726636891334289 10210597099294977668500717)
      ·
        refine ⟨3828973912235616625687769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10210597099294977668500717 3828973912235616625687769)
        ·
          refine ⟨2871730434176712469265827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3828973912235616625687769 2871730434176712469265827)
          ·
            refine ⟨4307595651265068703898741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2871730434176712469265827 4307595651265068703898741)
            ·
              refine ⟨403837092306100190990507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4307595651265068703898741 403837092306100190990507)
              ·
                refine ⟨605755638459150286485761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403837092306100190990507 605755638459150286485761)
                ·
                  refine ⟨454316728844362714864321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 605755638459150286485761 454316728844362714864321)
                  ·
                    refine ⟨340737546633272036148241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 454316728844362714864321 340737546633272036148241)
                    ·
                      refine ⟨255553159974954027111181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 340737546633272036148241 255553159974954027111181)
                      ·
                        rfl

theorem cell23_497688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_497688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497688 prefixEnd_497688 := by exact prefixLift 497688
  have htrace : WordTrace (prefixWord ++ tailWord_497688) baseStart_497688 baseEnd_497688 := by
    simpa [prefixWord, tailWord_497688, baseEnd_497688] using wordTrace_append hprefix tailTrace_497688
  have hstable : (prefixWord ++ tailWord_497688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497688).length < 2 ^ (prefixWord ++ tailWord_497688).sum := by decide
  have hdescent : baseEnd_497688 < baseStart_497688 := by decide
  rcases family_descends (prefixWord ++ tailWord_497688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497727 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 4]
def baseStart_497727 : Nat := 118140960795 + 497727 * 2 ^ 59
def prefixEnd_497727 : Nat := 4983230072969 + 3 ^ 40 * 497727 * 2
def baseEnd_497727 : Nat := 255573185720479374523501

theorem tailTrace_497727 : CollatzResearch.WordTrace tailWord_497727 prefixEnd_497727 255573185720479374523501 := by
  unfold tailWord_497727
  simp only [CollatzResearch.WordTrace]
  refine ⟨18153595067827558849115435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12102396711885039232743623 18153595067827558849115435)
  ·
    refine ⟨27230392601741338273673153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18153595067827558849115435 27230392601741338273673153)
    ·
      refine ⟨20422794451306003705254865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27230392601741338273673153 20422794451306003705254865)
      ·
        refine ⟨15317095838479502778941149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20422794451306003705254865 15317095838479502778941149)
        ·
          refine ⟨5743910939429813542102931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15317095838479502778941149 5743910939429813542102931)
          ·
            refine ⟨8615866409144720313154397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5743910939429813542102931 8615866409144720313154397)
            ·
              refine ⟨3230949903429270117432899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8615866409144720313154397 3230949903429270117432899)
              ·
                refine ⟨4846424855143905176149349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3230949903429270117432899 4846424855143905176149349)
                ·
                  refine ⟨908704660339482220528003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4846424855143905176149349 908704660339482220528003)
                  ·
                    refine ⟨1363056990509223330792005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 908704660339482220528003 1363056990509223330792005)
                    ·
                      refine ⟨255573185720479374523501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1363056990509223330792005 255573185720479374523501)
                      ·
                        rfl

theorem cell23_497727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_497727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497727 prefixEnd_497727 := by exact prefixLift 497727
  have htrace : WordTrace (prefixWord ++ tailWord_497727) baseStart_497727 baseEnd_497727 := by
    simpa [prefixWord, tailWord_497727, baseEnd_497727] using wordTrace_append hprefix tailTrace_497727
  have hstable : (prefixWord ++ tailWord_497727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497727).length < 2 ^ (prefixWord ++ tailWord_497727).sum := by decide
  have hdescent : baseEnd_497727 < baseStart_497727 := by decide
  rcases family_descends (prefixWord ++ tailWord_497727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497764 : List Nat := [2, 3, 1, 1, 2, 1, 3, 3, 2, 2, 3]
def baseStart_497764 : Nat := 118140960795 + 497764 * 2 ^ 59
def prefixEnd_497764 : Nat := 4983230072969 + 3 ^ 40 * 497764 * 2
def baseEnd_497764 : Nat := 255592184504695729760831

theorem tailTrace_497764 : CollatzResearch.WordTrace tailWord_497764 prefixEnd_497764 255592184504695729760831 := by
  unfold tailWord_497764
  simp only [CollatzResearch.WordTrace]
  refine ⟨9077472284346757084106173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12103296379129009445474897 9077472284346757084106173)
  ·
    refine ⟨3404052106630033906539815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9077472284346757084106173 3404052106630033906539815)
    ·
      refine ⟨5106078159945050859809723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3404052106630033906539815 5106078159945050859809723)
      ·
        refine ⟨7659117239917576289714585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5106078159945050859809723 7659117239917576289714585)
        ·
          refine ⟨5744337929938182217285939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7659117239917576289714585 5744337929938182217285939)
          ·
            refine ⟨8616506894907273325928909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5744337929938182217285939 8616506894907273325928909)
            ·
              refine ⟨3231190085590227497223341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8616506894907273325928909 3231190085590227497223341)
              ·
                refine ⟨1211696282096335311458753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3231190085590227497223341 1211696282096335311458753)
                ·
                  refine ⟨908772211572251483594065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1211696282096335311458753 908772211572251483594065)
                  ·
                    refine ⟨681579158679188612695549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 908772211572251483594065 681579158679188612695549)
                    ·
                      refine ⟨255592184504695729760831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 681579158679188612695549 255592184504695729760831)
                      ·
                        rfl

theorem cell23_497764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_497764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497764 prefixEnd_497764 := by exact prefixLift 497764
  have htrace : WordTrace (prefixWord ++ tailWord_497764) baseStart_497764 baseEnd_497764 := by
    simpa [prefixWord, tailWord_497764, baseEnd_497764] using wordTrace_append hprefix tailTrace_497764
  have hstable : (prefixWord ++ tailWord_497764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497764).length < 2 ^ (prefixWord ++ tailWord_497764).sum := by decide
  have hdescent : baseEnd_497764 < baseStart_497764 := by decide
  rcases family_descends (prefixWord ++ tailWord_497764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497788 : List Nat := [2, 2, 2, 1, 1, 4, 4, 2, 1, 4]
def baseStart_497788 : Nat := 118140960795 + 497788 * 2 ^ 59
def prefixEnd_497788 : Nat := 4983230072969 + 3 ^ 40 * 497788 * 2
def baseEnd_497788 : Nat := 85201502680134545286907

theorem tailTrace_497788 : CollatzResearch.WordTrace tailWord_497788 prefixEnd_497788 85201502680134545286907 := by
  unfold tailWord_497788
  simp only [CollatzResearch.WordTrace]
  refine ⟨9077909960303283133543009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12103879947071044178057345 9077909960303283133543009)
  ·
    refine ⟨6808432470227462350157257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9077909960303283133543009 6808432470227462350157257)
    ·
      refine ⟨5106324352670596762617943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6808432470227462350157257 5106324352670596762617943)
      ·
        refine ⟨7659486529005895143926915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5106324352670596762617943 7659486529005895143926915)
        ·
          refine ⟨11489229793508842715890373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7659486529005895143926915 11489229793508842715890373)
          ·
            refine ⟨2154230586282908009229445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11489229793508842715890373 2154230586282908009229445)
            ·
              refine ⟨403918234928045251730521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2154230586282908009229445 403918234928045251730521)
              ·
                refine ⟨302938676196033938797891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 403918234928045251730521 302938676196033938797891)
                ·
                  refine ⟨454408014294050908196837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 302938676196033938797891 454408014294050908196837)
                  ·
                    refine ⟨85201502680134545286907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 454408014294050908196837 85201502680134545286907)
                    ·
                      rfl

theorem cell23_497788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_497788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497788 prefixEnd_497788 := by exact prefixLift 497788
  have htrace : WordTrace (prefixWord ++ tailWord_497788) baseStart_497788 baseEnd_497788 := by
    simpa [prefixWord, tailWord_497788, baseEnd_497788] using wordTrace_append hprefix tailTrace_497788
  have hstable : (prefixWord ++ tailWord_497788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497788).length < 2 ^ (prefixWord ++ tailWord_497788).sum := by decide
  have hdescent : baseEnd_497788 < baseStart_497788 := by decide
  rcases family_descends (prefixWord ++ tailWord_497788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497821 : List Nat := [1, 4, 2, 1, 1, 4, 1, 1, 1, 5, 2]
def baseStart_497821 : Nat := 118140960795 + 497821 * 2 ^ 59
def prefixEnd_497821 : Nat := 4983230072969 + 3 ^ 40 * 497821 * 2
def baseEnd_497821 : Nat := 255621452902002006748069

theorem tailTrace_497821 : CollatzResearch.WordTrace tailWord_497821 prefixEnd_497821 255621452902002006748069 := by
  unfold tailWord_497821
  simp only [CollatzResearch.WordTrace]
  refine ⟨18157023529487012903037317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12104682352991341935358211 18157023529487012903037317)
  ·
    refine ⟨3404441911778814919319497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18157023529487012903037317 3404441911778814919319497)
    ·
      refine ⟨2553331433834111189489623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3404441911778814919319497 2553331433834111189489623)
      ·
        refine ⟨3829997150751166784234435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2553331433834111189489623 3829997150751166784234435)
        ·
          refine ⟨5744995726126750176351653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3829997150751166784234435 5744995726126750176351653)
          ·
            refine ⟨1077186698648765658065935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5744995726126750176351653 1077186698648765658065935)
            ·
              refine ⟨1615780047973148487098903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1077186698648765658065935 1615780047973148487098903)
              ·
                refine ⟨2423670071959722730648355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1615780047973148487098903 2423670071959722730648355)
                ·
                  refine ⟨3635505107939584095972533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2423670071959722730648355 3635505107939584095972533)
                  ·
                    refine ⟨340828603869336008997425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3635505107939584095972533 340828603869336008997425)
                    ·
                      refine ⟨255621452902002006748069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 340828603869336008997425 255621452902002006748069)
                      ·
                        rfl

theorem cell23_497821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_497821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497821 prefixEnd_497821 := by exact prefixLift 497821
  have htrace : WordTrace (prefixWord ++ tailWord_497821) baseStart_497821 baseEnd_497821 := by
    simpa [prefixWord, tailWord_497821, baseEnd_497821] using wordTrace_append hprefix tailTrace_497821
  have hstable : (prefixWord ++ tailWord_497821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497821).length < 2 ^ (prefixWord ++ tailWord_497821).sum := by decide
  have hdescent : baseEnd_497821 < baseStart_497821 := by decide
  rcases family_descends (prefixWord ++ tailWord_497821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497845 : List Nat := [1, 3, 3, 4, 1, 1, 2, 1, 3, 1, 3]
def baseStart_497845 : Nat := 118140960795 + 497845 * 2 ^ 59
def prefixEnd_497845 : Nat := 4983230072969 + 3 ^ 40 * 497845 * 2
def baseEnd_497845 : Nat := 255633776437709912847959

theorem tailTrace_497845 : CollatzResearch.WordTrace tailWord_497845 prefixEnd_497845 255633776437709912847959 := by
  unfold tailWord_497845
  simp only [CollatzResearch.WordTrace]
  refine ⟨18157898881400065001910989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12105265920933376667940659 18157898881400065001910989)
  ·
    refine ⟨6809212080525024375716621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18157898881400065001910989 6809212080525024375716621)
    ·
      refine ⟨2553454530196884140893733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6809212080525024375716621 2553454530196884140893733)
      ·
        refine ⟨478772724411915776417575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2553454530196884140893733 478772724411915776417575)
        ·
          refine ⟨718159086617873664626363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478772724411915776417575 718159086617873664626363)
          ·
            refine ⟨1077238629926810496939545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718159086617873664626363 1077238629926810496939545)
            ·
              refine ⟨807928972445107872704659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1077238629926810496939545 807928972445107872704659)
              ·
                refine ⟨1211893458667661809056989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 807928972445107872704659 1211893458667661809056989)
                ·
                  refine ⟨454460047000373178396371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1211893458667661809056989 454460047000373178396371)
                  ·
                    refine ⟨681690070500559767594557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 454460047000373178396371 681690070500559767594557)
                    ·
                      refine ⟨255633776437709912847959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 681690070500559767594557 255633776437709912847959)
                      ·
                        rfl

theorem cell23_497845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_497845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497845 prefixEnd_497845 := by exact prefixLift 497845
  have htrace : WordTrace (prefixWord ++ tailWord_497845) baseStart_497845 baseEnd_497845 := by
    simpa [prefixWord, tailWord_497845, baseEnd_497845] using wordTrace_append hprefix tailTrace_497845
  have hstable : (prefixWord ++ tailWord_497845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497845).length < 2 ^ (prefixWord ++ tailWord_497845).sum := by decide
  have hdescent : baseEnd_497845 < baseStart_497845 := by decide
  rcases family_descends (prefixWord ++ tailWord_497845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497871 : List Nat := [1, 1, 2, 1, 1, 3, 6, 2, 1, 2, 3]
def baseStart_497871 : Nat := 118140960795 + 497871 * 2 ^ 59
def prefixEnd_497871 : Nat := 4983230072969 + 3 ^ 40 * 497871 * 2
def baseEnd_497871 : Nat := 255647126934726811122839

theorem tailTrace_497871 : CollatzResearch.WordTrace tailWord_497871 prefixEnd_497871 255647126934726811122839 := by
  unfold tailWord_497871
  simp only [CollatzResearch.WordTrace]
  refine ⟨18158847179305871442357467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12105898119537247628238311 18158847179305871442357467)
  ·
    refine ⟨27238270768958807163536201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18158847179305871442357467 27238270768958807163536201)
    ·
      refine ⟨20428703076719105372652151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27238270768958807163536201 20428703076719105372652151)
      ·
        refine ⟨30643054615078658058978227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20428703076719105372652151 30643054615078658058978227)
        ·
          refine ⟨45964581922617987088467341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30643054615078658058978227 45964581922617987088467341)
          ·
            refine ⟨17236718220981745158175253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45964581922617987088467341 17236718220981745158175253)
            ·
              refine ⟨807971166608519304289465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17236718220981745158175253 807971166608519304289465)
              ·
                refine ⟨605978374956389478217099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 807971166608519304289465 605978374956389478217099)
                ·
                  refine ⟨908967562434584217325649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 605978374956389478217099 908967562434584217325649)
                  ·
                    refine ⟨681725671825938162994237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 908967562434584217325649 681725671825938162994237)
                    ·
                      refine ⟨255647126934726811122839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 681725671825938162994237 255647126934726811122839)
                      ·
                        rfl

theorem cell23_497871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 2, 3].length) (baseStart_497871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497871 prefixEnd_497871 := by exact prefixLift 497871
  have htrace : WordTrace (prefixWord ++ tailWord_497871) baseStart_497871 baseEnd_497871 := by
    simpa [prefixWord, tailWord_497871, baseEnd_497871] using wordTrace_append hprefix tailTrace_497871
  have hstable : (prefixWord ++ tailWord_497871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497871).length < 2 ^ (prefixWord ++ tailWord_497871).sum := by decide
  have hdescent : baseEnd_497871 < baseStart_497871 := by decide
  rcases family_descends (prefixWord ++ tailWord_497871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497874 : List Nat := [3, 2, 2, 2, 1, 3, 1, 9]
def baseStart_497874 : Nat := 118140960795 + 497874 * 2 ^ 59
def prefixEnd_497874 : Nat := 4983230072969 + 3 ^ 40 * 497874 * 2
def baseEnd_497874 : Nat := 9468469162099640717975

theorem tailTrace_497874 : CollatzResearch.WordTrace tailWord_497874 prefixEnd_497874 9468469162099640717975 := by
  unfold tailWord_497874
  simp only [CollatzResearch.WordTrace]
  refine ⟨4539739149573750738679169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12105971065530001969811117 4539739149573750738679169)
  ·
    refine ⟨3404804362180313054009377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4539739149573750738679169 3404804362180313054009377)
    ·
      refine ⟨2553603271635234790507033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3404804362180313054009377 2553603271635234790507033)
      ·
        refine ⟨1915202453726426092880275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2553603271635234790507033 1915202453726426092880275)
        ·
          refine ⟨2872803680589639139320413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1915202453726426092880275 2872803680589639139320413)
          ·
            refine ⟨1077301380221114677245155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2872803680589639139320413 1077301380221114677245155)
            ·
              refine ⟨1615952070331672015867733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1077301380221114677245155 1615952070331672015867733)
              ·
                refine ⟨9468469162099640717975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1615952070331672015867733 9468469162099640717975)
                ·
                  rfl

theorem cell23_497874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 9].length) (baseStart_497874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497874 prefixEnd_497874 := by exact prefixLift 497874
  have htrace : WordTrace (prefixWord ++ tailWord_497874) baseStart_497874 baseEnd_497874 := by
    simpa [prefixWord, tailWord_497874, baseEnd_497874] using wordTrace_append hprefix tailTrace_497874
  have hstable : (prefixWord ++ tailWord_497874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497874).length < 2 ^ (prefixWord ++ tailWord_497874).sum := by decide
  have hdescent : baseEnd_497874 < baseStart_497874 := by decide
  rcases family_descends (prefixWord ++ tailWord_497874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497878 : List Nat := [5, 2, 1, 2, 1, 1, 1, 2, 4, 4]
def baseStart_497878 : Nat := 118140960795 + 497878 * 2 ^ 59
def prefixEnd_497878 : Nat := 4983230072969 + 3 ^ 40 * 497878 * 2
def baseEnd_497878 : Nat := 85216907099769427911769

theorem tailTrace_497878 : CollatzResearch.WordTrace tailWord_497878 prefixEnd_497878 85216907099769427911769 := by
  unfold tailWord_497878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1134943905642531977366393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12106068326853674425241525 1134943905642531977366393)
  ·
    refine ⟨851207929231898983024795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1134943905642531977366393 851207929231898983024795)
    ·
      refine ⟨1276811893847848474537193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 851207929231898983024795 1276811893847848474537193)
      ·
        refine ⟨957608920385886355902895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1276811893847848474537193 957608920385886355902895)
        ·
          refine ⟨1436413380578829533854343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 957608920385886355902895 1436413380578829533854343)
          ·
            refine ⟨2154620070868244300781515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1436413380578829533854343 2154620070868244300781515)
            ·
              refine ⟨3231930106302366451172273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2154620070868244300781515 3231930106302366451172273)
              ·
                refine ⟨2423947579726774838379205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3231930106302366451172273 2423947579726774838379205)
                ·
                  refine ⟨454490171198770282196101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2423947579726774838379205 454490171198770282196101)
                  ·
                    refine ⟨85216907099769427911769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 454490171198770282196101 85216907099769427911769)
                    ·
                      rfl

theorem cell23_497878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_497878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497878 prefixEnd_497878 := by exact prefixLift 497878
  have htrace : WordTrace (prefixWord ++ tailWord_497878) baseStart_497878 baseEnd_497878 := by
    simpa [prefixWord, tailWord_497878, baseEnd_497878] using wordTrace_append hprefix tailTrace_497878
  have hstable : (prefixWord ++ tailWord_497878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497878).length < 2 ^ (prefixWord ++ tailWord_497878).sum := by decide
  have hdescent : baseEnd_497878 < baseStart_497878 := by decide
  rcases family_descends (prefixWord ++ tailWord_497878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497887 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 1, 9]
def baseStart_497887 : Nat := 118140960795 + 497887 * 2 ^ 59
def prefixEnd_497887 : Nat := 4983230072969 + 3 ^ 40 * 497887 * 2
def baseEnd_497887 : Nat := 85218447541732916174255

theorem tailTrace_497887 : CollatzResearch.WordTrace tailWord_497887 prefixEnd_497887 85218447541732916174255 := by
  unfold tailWord_497887
  simp only [CollatzResearch.WordTrace]
  refine ⟨18159430747247906174939915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12106287164831937449959943 18159430747247906174939915)
  ·
    refine ⟨27239146120871859262409873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18159430747247906174939915 27239146120871859262409873)
    ·
      refine ⟨20429359590653894446807405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27239146120871859262409873 20429359590653894446807405)
      ·
        refine ⟨7661009846495210417552777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20429359590653894446807405 7661009846495210417552777)
        ·
          refine ⟨5745757384871407813164583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7661009846495210417552777 5745757384871407813164583)
          ·
            refine ⟨8618636077307111719746875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5745757384871407813164583 8618636077307111719746875)
            ·
              refine ⟨12927954115960667579620313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8618636077307111719746875 12927954115960667579620313)
              ·
                refine ⟨9695965586970500684715235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12927954115960667579620313 9695965586970500684715235)
                ·
                  refine ⟨14543948380455751027072853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9695965586970500684715235 14543948380455751027072853)
                  ·
                    refine ⟨85218447541732916174255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 14543948380455751027072853 85218447541732916174255)
                    ·
                      rfl

theorem cell23_497887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 9].length) (baseStart_497887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497887 prefixEnd_497887 := by exact prefixLift 497887
  have htrace : WordTrace (prefixWord ++ tailWord_497887) baseStart_497887 baseEnd_497887 := by
    simpa [prefixWord, tailWord_497887, baseEnd_497887] using wordTrace_append hprefix tailTrace_497887
  have hstable : (prefixWord ++ tailWord_497887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497887).length < 2 ^ (prefixWord ++ tailWord_497887).sum := by decide
  have hdescent : baseEnd_497887 < baseStart_497887 := by decide
  rcases family_descends (prefixWord ++ tailWord_497887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497891 : List Nat := [1, 1, 1, 8, 1, 2, 9]
def baseStart_497891 : Nat := 118140960795 + 497891 * 2 ^ 59
def prefixEnd_497891 : Nat := 4983230072969 + 3 ^ 40 * 497891 * 2
def baseEnd_497891 : Nat := 3156264154911317689787

theorem tailTrace_497891 : CollatzResearch.WordTrace tailWord_497891 prefixEnd_497891 3156264154911317689787 := by
  unfold tailWord_497891
  simp only [CollatzResearch.WordTrace]
  refine ⟨18159576639233414858085527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12106384426155609905390351 18159576639233414858085527)
  ·
    refine ⟨27239364958850122287128291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18159576639233414858085527 27239364958850122287128291)
    ·
      refine ⟨40859047438275183430692437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27239364958850122287128291 40859047438275183430692437)
      ·
        refine ⟨478816962167287305828427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 40859047438275183430692437 478816962167287305828427)
        ·
          refine ⟨718225443250930958742641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478816962167287305828427 718225443250930958742641)
          ·
            refine ⟨538669082438198219056981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 718225443250930958742641 538669082438198219056981)
            ·
              refine ⟨3156264154911317689787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 538669082438198219056981 3156264154911317689787)
              ·
                rfl

theorem cell23_497891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 9].length) (baseStart_497891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497891 prefixEnd_497891 := by exact prefixLift 497891
  have htrace : WordTrace (prefixWord ++ tailWord_497891) baseStart_497891 baseEnd_497891 := by
    simpa [prefixWord, tailWord_497891, baseEnd_497891] using wordTrace_append hprefix tailTrace_497891
  have hstable : (prefixWord ++ tailWord_497891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497891).length < 2 ^ (prefixWord ++ tailWord_497891).sum := by decide
  have hdescent : baseEnd_497891 < baseStart_497891 := by decide
  rcases family_descends (prefixWord ++ tailWord_497891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497928 : List Nat := [2, 1, 3, 2, 3, 2, 1, 1, 3, 3, 2]
def baseStart_497928 : Nat := 118140960795 + 497928 * 2 ^ 59
def prefixEnd_497928 : Nat := 4983230072969 + 3 ^ 40 * 497928 * 2
def baseEnd_497928 : Nat := 255676395332033088110077

theorem tailTrace_497928 : CollatzResearch.WordTrace tailWord_497928 prefixEnd_497928 255676395332033088110077 := by
  unfold tailWord_497928
  simp only [CollatzResearch.WordTrace]
  refine ⟨9080463070049685088591219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12107284093399580118121625 9080463070049685088591219)
  ·
    refine ⟨13620694605074527632886829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9080463070049685088591219 13620694605074527632886829)
    ·
      refine ⟨5107760476902947862332561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13620694605074527632886829 5107760476902947862332561)
      ·
        refine ⟨3830820357677210896749421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5107760476902947862332561 3830820357677210896749421)
        ·
          refine ⟨1436557634128954086281033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3830820357677210896749421 1436557634128954086281033)
          ·
            refine ⟨1077418225596715564710775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1436557634128954086281033 1077418225596715564710775)
            ·
              refine ⟨1616127338395073347066163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1077418225596715564710775 1616127338395073347066163)
              ·
                refine ⟨2424191007592610020599245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1616127338395073347066163 2424191007592610020599245)
                ·
                  refine ⟨909071627847228757724717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2424191007592610020599245 909071627847228757724717)
                  ·
                    refine ⟨340901860442710784146769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 909071627847228757724717 340901860442710784146769)
                    ·
                      refine ⟨255676395332033088110077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 340901860442710784146769 255676395332033088110077)
                      ·
                        rfl

theorem cell23_497928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_497928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497928 prefixEnd_497928 := by exact prefixLift 497928
  have htrace : WordTrace (prefixWord ++ tailWord_497928) baseStart_497928 baseEnd_497928 := by
    simpa [prefixWord, tailWord_497928, baseEnd_497928] using wordTrace_append hprefix tailTrace_497928
  have hstable : (prefixWord ++ tailWord_497928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497928).length < 2 ^ (prefixWord ++ tailWord_497928).sum := by decide
  have hdescent : baseEnd_497928 < baseStart_497928 := by decide
  rcases family_descends (prefixWord ++ tailWord_497928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497941 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 3, 4, 2]
def baseStart_497941 : Nat := 118140960795 + 497941 * 2 ^ 59
def prefixEnd_497941 : Nat := 4983230072969 + 3 ^ 40 * 497941 * 2
def baseEnd_497941 : Nat := 255683070580541537247517

theorem tailTrace_497941 : CollatzResearch.WordTrace tailWord_497941 prefixEnd_497941 255683070580541537247517 := by
  unfold tailWord_497941
  simp only [CollatzResearch.WordTrace]
  refine ⟨18161400289052273397405677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12107600192701515598270451 18161400289052273397405677)
  ·
    refine ⟨6810525108394602524027129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18161400289052273397405677 6810525108394602524027129)
    ·
      refine ⟨5107893831295951893020347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6810525108394602524027129 5107893831295951893020347)
      ·
        refine ⟨7661840746943927839530521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5107893831295951893020347 7661840746943927839530521)
        ·
          refine ⟨5746380560207945879647891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7661840746943927839530521 5746380560207945879647891)
          ·
            refine ⟨8619570840311918819471837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5746380560207945879647891 8619570840311918819471837)
            ·
              refine ⟨3232339065116969557301939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8619570840311918819471837 3232339065116969557301939)
              ·
                refine ⟨4848508597675454335952909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3232339065116969557301939 4848508597675454335952909)
                ·
                  refine ⟨1818190724128295375982341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4848508597675454335952909 1818190724128295375982341)
                  ·
                    refine ⟨340910760774055382996689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1818190724128295375982341 340910760774055382996689)
                    ·
                      refine ⟨255683070580541537247517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 340910760774055382996689 255683070580541537247517)
                      ·
                        rfl

theorem cell23_497941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 4, 2].length) (baseStart_497941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497941 prefixEnd_497941 := by exact prefixLift 497941
  have htrace : WordTrace (prefixWord ++ tailWord_497941) baseStart_497941 baseEnd_497941 := by
    simpa [prefixWord, tailWord_497941, baseEnd_497941] using wordTrace_append hprefix tailTrace_497941
  have hstable : (prefixWord ++ tailWord_497941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497941).length < 2 ^ (prefixWord ++ tailWord_497941).sum := by decide
  have hdescent : baseEnd_497941 < baseStart_497941 := by decide
  rcases family_descends (prefixWord ++ tailWord_497941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497944 : List Nat := [2, 1, 2, 3, 1, 2, 1, 3, 2, 1, 5]
def baseStart_497944 : Nat := 118140960795 + 497944 * 2 ^ 59
def prefixEnd_497944 : Nat := 4983230072969 + 3 ^ 40 * 497944 * 2
def baseEnd_497944 : Nat := 255684611022505025510003

theorem tailTrace_497944 : CollatzResearch.WordTrace tailWord_497944 prefixEnd_497944 255684611022505025510003 := by
  unfold tailWord_497944
  simp only [CollatzResearch.WordTrace]
  refine ⟨9080754854020702454882443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12107673138694269939843257 9080754854020702454882443)
  ·
    refine ⟨13621132281031053682323665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9080754854020702454882443 13621132281031053682323665)
    ·
      refine ⟨10215849210773290261742749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13621132281031053682323665 10215849210773290261742749)
      ·
        refine ⟨3830943454039983848153531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10215849210773290261742749 3830943454039983848153531)
        ·
          refine ⟨5746415181059975772230297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3830943454039983848153531 5746415181059975772230297)
          ·
            refine ⟨4309811385794981829172723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5746415181059975772230297 4309811385794981829172723)
            ·
              refine ⟨6464717078692472743759085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4309811385794981829172723 6464717078692472743759085)
              ·
                refine ⟨2424268904509677278909657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6464717078692472743759085 2424268904509677278909657)
                ·
                  refine ⟨1818201678382257959182243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2424268904509677278909657 1818201678382257959182243)
                  ·
                    refine ⟨2727302517573386938773365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1818201678382257959182243 2727302517573386938773365)
                    ·
                      refine ⟨255684611022505025510003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2727302517573386938773365 255684611022505025510003)
                      ·
                        rfl

theorem cell23_497944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_497944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_497944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_497944 prefixEnd_497944 := by exact prefixLift 497944
  have htrace : WordTrace (prefixWord ++ tailWord_497944) baseStart_497944 baseEnd_497944 := by
    simpa [prefixWord, tailWord_497944, baseEnd_497944] using wordTrace_append hprefix tailTrace_497944
  have hstable : (prefixWord ++ tailWord_497944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497944).length < 2 ^ (prefixWord ++ tailWord_497944).sum := by decide
  have hdescent : baseEnd_497944 < baseStart_497944 := by decide
  rcases family_descends (prefixWord ++ tailWord_497944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498031 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 1, 6, 2]
def baseStart_498031 : Nat := 118140960795 + 498031 * 2 ^ 59
def prefixEnd_498031 : Nat := 4983230072969 + 3 ^ 40 * 498031 * 2
def baseEnd_498031 : Nat := 255729283839446185122103

theorem tailTrace_498031 : CollatzResearch.WordTrace tailWord_498031 prefixEnd_498031 255729283839446185122103 := by
  unfold tailWord_498031
  simp only [CollatzResearch.WordTrace]
  refine ⟨18164682858726218768181947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12109788572484145845454631 18164682858726218768181947)
  ·
    refine ⟨27247024288089328152272921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18164682858726218768181947 27247024288089328152272921)
    ·
      refine ⟨20435268216066996114204691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27247024288089328152272921 20435268216066996114204691)
      ·
        refine ⟨30652902324100494171307037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20435268216066996114204691 30652902324100494171307037)
        ·
          refine ⟨11494838371537685314240139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30652902324100494171307037 11494838371537685314240139)
          ·
            refine ⟨17242257557306527971360209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11494838371537685314240139 17242257557306527971360209)
            ·
              refine ⟨12931693167979895978520157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17242257557306527971360209 12931693167979895978520157)
              ·
                refine ⟨4849384937992460991945059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12931693167979895978520157 4849384937992460991945059)
                ·
                  refine ⟨7274077406988691487917589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4849384937992460991945059 7274077406988691487917589)
                  ·
                    refine ⟨340972378452594913496137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7274077406988691487917589 340972378452594913496137)
                    ·
                      refine ⟨255729283839446185122103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 340972378452594913496137 255729283839446185122103)
                      ·
                        rfl

theorem cell23_498031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 6, 2].length) (baseStart_498031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498031 prefixEnd_498031 := by exact prefixLift 498031
  have htrace : WordTrace (prefixWord ++ tailWord_498031) baseStart_498031 baseEnd_498031 := by
    simpa [prefixWord, tailWord_498031, baseEnd_498031] using wordTrace_append hprefix tailTrace_498031
  have hstable : (prefixWord ++ tailWord_498031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498031).length < 2 ^ (prefixWord ++ tailWord_498031).sum := by decide
  have hdescent : baseEnd_498031 < baseStart_498031 := by decide
  rcases family_descends (prefixWord ++ tailWord_498031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498044 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 1, 3, 6]
def baseStart_498044 : Nat := 118140960795 + 498044 * 2 ^ 59
def prefixEnd_498044 : Nat := 4983230072969 + 3 ^ 40 * 498044 * 2
def baseEnd_498044 : Nat := 255735959087954634259543

theorem tailTrace_498044 : CollatzResearch.WordTrace tailWord_498044 prefixEnd_498044 255735959087954634259543 := by
  unfold tailWord_498044
  simp only [CollatzResearch.WordTrace]
  refine ⟨9082578503839560994202593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12110104671786081325603457 9082578503839560994202593)
  ·
    refine ⟨6811933877879670745651945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9082578503839560994202593 6811933877879670745651945)
    ·
      refine ⟨5108950408409753059238959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6811933877879670745651945 5108950408409753059238959)
      ·
        refine ⟨7663425612614629588858439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5108950408409753059238959 7663425612614629588858439)
        ·
          refine ⟨11495138418921944383287659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7663425612614629588858439 11495138418921944383287659)
          ·
            refine ⟨17242707628382916574931489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11495138418921944383287659 17242707628382916574931489)
            ·
              refine ⟨12932030721287187431198617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17242707628382916574931489 12932030721287187431198617)
              ·
                refine ⟨9699023040965390573398963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12932030721287187431198617 9699023040965390573398963)
                ·
                  refine ⟨14548534561448085860098445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9699023040965390573398963 14548534561448085860098445)
                  ·
                    refine ⟨5455700460543032197536917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14548534561448085860098445 5455700460543032197536917)
                    ·
                      refine ⟨255735959087954634259543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5455700460543032197536917 255735959087954634259543)
                      ·
                        rfl

theorem cell23_498044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_498044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498044 prefixEnd_498044 := by exact prefixLift 498044
  have htrace : WordTrace (prefixWord ++ tailWord_498044) baseStart_498044 baseEnd_498044 := by
    simpa [prefixWord, tailWord_498044, baseEnd_498044] using wordTrace_append hprefix tailTrace_498044
  have hstable : (prefixWord ++ tailWord_498044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498044).length < 2 ^ (prefixWord ++ tailWord_498044).sum := by decide
  have hdescent : baseEnd_498044 < baseStart_498044 := by decide
  rcases family_descends (prefixWord ++ tailWord_498044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498098 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3]
def baseStart_498098 : Nat := 118140960795 + 498098 * 2 ^ 59
def prefixEnd_498098 : Nat := 4983230072969 + 3 ^ 40 * 498098 * 2
def baseEnd_498098 : Nat := 255763687043297422984295

theorem tailTrace_498098 : CollatzResearch.WordTrace tailWord_498098 prefixEnd_498098 255763687043297422984295 := by
  unfold tailWord_498098
  simp only [CollatzResearch.WordTrace]
  refine ⟨4541781637370872302717737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12111417699655659473913965 4541781637370872302717737)
  ·
    refine ⟨3406336228028154227038303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4541781637370872302717737 3406336228028154227038303)
    ·
      refine ⟨5109504342042231340557455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3406336228028154227038303 5109504342042231340557455)
      ·
        refine ⟨7664256513063347010836183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5109504342042231340557455 7664256513063347010836183)
        ·
          refine ⟨11496384769595020516254275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7664256513063347010836183 11496384769595020516254275)
          ·
            refine ⟨17244577154392530774381413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11496384769595020516254275 17244577154392530774381413)
            ·
              refine ⟨3233358216448599520196515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17244577154392530774381413 3233358216448599520196515)
              ·
                refine ⟨4850037324672899280294773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3233358216448599520196515 4850037324672899280294773)
                ·
                  refine ⟨454690999188084307527635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4850037324672899280294773 454690999188084307527635)
                  ·
                    refine ⟨682036498782126461291453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 454690999188084307527635 682036498782126461291453)
                    ·
                      refine ⟨255763687043297422984295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 682036498782126461291453 255763687043297422984295)
                      ·
                        rfl

theorem cell23_498098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_498098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498098 prefixEnd_498098 := by exact prefixLift 498098
  have htrace : WordTrace (prefixWord ++ tailWord_498098) baseStart_498098 baseEnd_498098 := by
    simpa [prefixWord, tailWord_498098, baseEnd_498098] using wordTrace_append hprefix tailTrace_498098
  have hstable : (prefixWord ++ tailWord_498098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498098).length < 2 ^ (prefixWord ++ tailWord_498098).sum := by decide
  have hdescent : baseEnd_498098 < baseStart_498098 := by decide
  rcases family_descends (prefixWord ++ tailWord_498098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498115 : List Nat := [1, 1, 1, 3, 1, 1, 3, 7, 1, 1, 3]
def baseStart_498115 : Nat := 118140960795 + 498115 * 2 ^ 59
def prefixEnd_498115 : Nat := 4983230072969 + 3 ^ 40 * 498115 * 2
def baseEnd_498115 : Nat := 255772416214423856471717

theorem tailTrace_498115 : CollatzResearch.WordTrace tailWord_498115 prefixEnd_498115 255772416214423856471717 := by
  unfold tailWord_498115
  simp only [CollatzResearch.WordTrace]
  refine ⟨18167746590421901114239799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12111831060281267409493199 18167746590421901114239799)
  ·
    refine ⟨27251619885632851671359699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18167746590421901114239799 27251619885632851671359699)
    ·
      refine ⟨40877429828449277507039549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27251619885632851671359699 40877429828449277507039549)
      ·
        refine ⟨15329036185668479065139831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40877429828449277507039549 15329036185668479065139831)
        ·
          refine ⟨22993554278502718597709747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15329036185668479065139831 22993554278502718597709747)
          ·
            refine ⟨34490331417754077896564621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22993554278502718597709747 34490331417754077896564621)
            ·
              refine ⟨12933874281657779211211733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34490331417754077896564621 12933874281657779211211733)
              ·
                refine ⟨303137678476354200262775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 12933874281657779211211733 303137678476354200262775)
                ·
                  refine ⟨454706517714531300394163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 303137678476354200262775 454706517714531300394163)
                  ·
                    refine ⟨682059776571796950591245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 454706517714531300394163 682059776571796950591245)
                    ·
                      refine ⟨255772416214423856471717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 682059776571796950591245 255772416214423856471717)
                      ·
                        rfl

theorem cell23_498115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 7, 1, 1, 3].length) (baseStart_498115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498115 prefixEnd_498115 := by exact prefixLift 498115
  have htrace : WordTrace (prefixWord ++ tailWord_498115) baseStart_498115 baseEnd_498115 := by
    simpa [prefixWord, tailWord_498115, baseEnd_498115] using wordTrace_append hprefix tailTrace_498115
  have hstable : (prefixWord ++ tailWord_498115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498115).length < 2 ^ (prefixWord ++ tailWord_498115).sum := by decide
  have hdescent : baseEnd_498115 < baseStart_498115 := by decide
  rcases family_descends (prefixWord ++ tailWord_498115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498131 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 10, 4]
def baseStart_498131 : Nat := 118140960795 + 498131 * 2 ^ 59
def prefixEnd_498131 : Nat := 4983230072969 + 3 ^ 40 * 498131 * 2
def baseEnd_498131 : Nat := 85260210634965264623881

theorem tailTrace_498131 : CollatzResearch.WordTrace tailWord_498131 prefixEnd_498131 85260210634965264623881 := by
  unfold tailWord_498131
  simp only [CollatzResearch.WordTrace]
  refine ⟨18168330158363935846822247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12112220105575957231214831 18168330158363935846822247)
  ·
    refine ⟨27252495237545903770233371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18168330158363935846822247 27252495237545903770233371)
    ·
      refine ⟨40878742856318855655350057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27252495237545903770233371 40878742856318855655350057)
      ·
        refine ⟨30659057142239141741512543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40878742856318855655350057 30659057142239141741512543)
        ·
          refine ⟨45988585713358712612268815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30659057142239141741512543 45988585713358712612268815)
          ·
            refine ⟨68982878570038068918403223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45988585713358712612268815 68982878570038068918403223)
            ·
              refine ⟨103474317855057103377604835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68982878570038068918403223 103474317855057103377604835)
              ·
                refine ⟨155211476782585655066407253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103474317855057103377604835 155211476782585655066407253)
                ·
                  refine ⟨454721123386481411327365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 155211476782585655066407253 454721123386481411327365)
                  ·
                    refine ⟨85260210634965264623881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 454721123386481411327365 85260210634965264623881)
                    ·
                      rfl

theorem cell23_498131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 10, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 10, 4].length) (baseStart_498131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498131 prefixEnd_498131 := by exact prefixLift 498131
  have htrace : WordTrace (prefixWord ++ tailWord_498131) baseStart_498131 baseEnd_498131 := by
    simpa [prefixWord, tailWord_498131, baseEnd_498131] using wordTrace_append hprefix tailTrace_498131
  have hstable : (prefixWord ++ tailWord_498131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498131).length < 2 ^ (prefixWord ++ tailWord_498131).sum := by decide
  have hdescent : baseEnd_498131 < baseStart_498131 := by decide
  rcases family_descends (prefixWord ++ tailWord_498131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498155 : List Nat := [1, 1, 1, 1, 2, 3, 5, 2, 3, 2, 2]
def baseStart_498155 : Nat := 118140960795 + 498155 * 2 ^ 59
def prefixEnd_498155 : Nat := 4983230072969 + 3 ^ 40 * 498155 * 2
def baseEnd_498155 : Nat := 255792955440603699971533

theorem tailTrace_498155 : CollatzResearch.WordTrace tailWord_498155 prefixEnd_498155 255792955440603699971533 := by
  unfold tailWord_498155
  simp only [CollatzResearch.WordTrace]
  refine ⟨18169205510276987945695919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12112803673517991963797279 18169205510276987945695919)
  ·
    refine ⟨27253808265415481918543879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18169205510276987945695919 27253808265415481918543879)
    ·
      refine ⟨40880712398123222877815819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27253808265415481918543879 40880712398123222877815819)
      ·
        refine ⟨61321068597184834316723729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40880712398123222877815819 61321068597184834316723729)
        ·
          refine ⟨45990801447888625737542797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61321068597184834316723729 45990801447888625737542797)
          ·
            refine ⟨17246550542958234651578549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45990801447888625737542797 17246550542958234651578549)
            ·
              refine ⟨1616864113402334498585489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17246550542958234651578549 1616864113402334498585489)
              ·
                refine ⟨1212648085051750873939117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1616864113402334498585489 1212648085051750873939117)
                ·
                  refine ⟨454743031894406577727169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1212648085051750873939117 454743031894406577727169)
                  ·
                    refine ⟨341057273920804933295377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 454743031894406577727169 341057273920804933295377)
                    ·
                      refine ⟨255792955440603699971533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 341057273920804933295377 255792955440603699971533)
                      ·
                        rfl

theorem cell23_498155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 3, 2, 2].length) (baseStart_498155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498155 prefixEnd_498155 := by exact prefixLift 498155
  have htrace : WordTrace (prefixWord ++ tailWord_498155) baseStart_498155 baseEnd_498155 := by
    simpa [prefixWord, tailWord_498155, baseEnd_498155] using wordTrace_append hprefix tailTrace_498155
  have hstable : (prefixWord ++ tailWord_498155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498155).length < 2 ^ (prefixWord ++ tailWord_498155).sum := by decide
  have hdescent : baseEnd_498155 < baseStart_498155 := by decide
  rcases family_descends (prefixWord ++ tailWord_498155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498199 : List Nat := [1, 1, 3, 6, 1, 1, 3, 1, 2, 4]
def baseStart_498199 : Nat := 118140960795 + 498199 * 2 ^ 59
def prefixEnd_498199 : Nat := 4983230072969 + 3 ^ 40 * 498199 * 2
def baseEnd_498199 : Nat := 85271849529800509273777

theorem tailTrace_498199 : CollatzResearch.WordTrace tailWord_498199 prefixEnd_498199 85271849529800509273777 := by
  unfold tailWord_498199
  simp only [CollatzResearch.WordTrace]
  refine ⟨18170810322117583460297651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12113873548078388973531767 18170810322117583460297651)
  ·
    refine ⟨27256215483176375190446477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18170810322117583460297651 27256215483176375190446477)
    ·
      refine ⟨10221080806191140696417429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27256215483176375190446477 10221080806191140696417429)
      ·
        refine ⟨479113162790209720144567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10221080806191140696417429 479113162790209720144567)
        ·
          refine ⟨718669744185314580216851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479113162790209720144567 718669744185314580216851)
          ·
            refine ⟨1078004616277971870325277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718669744185314580216851 1078004616277971870325277)
            ·
              refine ⟨404251731104239451371979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1078004616277971870325277 404251731104239451371979)
              ·
                refine ⟨606377596656359177057969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 404251731104239451371979 606377596656359177057969)
                ·
                  refine ⟨454783197492269382793477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 606377596656359177057969 454783197492269382793477)
                  ·
                    refine ⟨85271849529800509273777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 454783197492269382793477 85271849529800509273777)
                    ·
                      rfl

theorem cell23_498199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 1, 2, 4].length) (baseStart_498199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498199 prefixEnd_498199 := by exact prefixLift 498199
  have htrace : WordTrace (prefixWord ++ tailWord_498199) baseStart_498199 baseEnd_498199 := by
    simpa [prefixWord, tailWord_498199, baseEnd_498199] using wordTrace_append hprefix tailTrace_498199
  have hstable : (prefixWord ++ tailWord_498199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498199).length < 2 ^ (prefixWord ++ tailWord_498199).sum := by decide
  have hdescent : baseEnd_498199 < baseStart_498199 := by decide
  rcases family_descends (prefixWord ++ tailWord_498199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498205 : List Nat := [1, 4, 2, 2, 1, 2, 3, 1, 1, 3, 3]
def baseStart_498205 : Nat := 118140960795 + 498205 * 2 ^ 59
def prefixEnd_498205 : Nat := 4983230072969 + 3 ^ 40 * 498205 * 2
def baseEnd_498205 : Nat := 255818629473328504346303

theorem tailTrace_498205 : CollatzResearch.WordTrace tailWord_498205 prefixEnd_498205 255818629473328504346303 := by
  unfold tailWord_498205
  simp only [CollatzResearch.WordTrace]
  refine ⟨18171029160095846485016069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12114019440063897656677379 18171029160095846485016069)
  ·
    refine ⟨3407067967517971215940513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18171029160095846485016069 3407067967517971215940513)
    ·
      refine ⟨2555300975638478411955385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3407067967517971215940513 2555300975638478411955385)
      ·
        refine ⟨1916475731728858808966539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2555300975638478411955385 1916475731728858808966539)
        ·
          refine ⟨2874713597593288213449809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1916475731728858808966539 2874713597593288213449809)
          ·
            refine ⟨2156035198194966160087357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2874713597593288213449809 2156035198194966160087357)
            ·
              refine ⟨808513199323112310032759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2156035198194966160087357 808513199323112310032759)
              ·
                refine ⟨1212769798984668465049139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808513199323112310032759 1212769798984668465049139)
                ·
                  refine ⟨1819154698477002697573709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1212769798984668465049139 1819154698477002697573709)
                  ·
                    refine ⟨682183011928876011590141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1819154698477002697573709 682183011928876011590141)
                    ·
                      refine ⟨255818629473328504346303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 682183011928876011590141 255818629473328504346303)
                      ·
                        rfl

theorem cell23_498205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_498205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498205 prefixEnd_498205 := by exact prefixLift 498205
  have htrace : WordTrace (prefixWord ++ tailWord_498205) baseStart_498205 baseEnd_498205 := by
    simpa [prefixWord, tailWord_498205, baseEnd_498205] using wordTrace_append hprefix tailTrace_498205
  have hstable : (prefixWord ++ tailWord_498205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498205).length < 2 ^ (prefixWord ++ tailWord_498205).sum := by decide
  have hdescent : baseEnd_498205 < baseStart_498205 := by decide
  rcases family_descends (prefixWord ++ tailWord_498205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498212 : List Nat := [2, 3, 1, 5, 1, 2, 2, 7]
def baseStart_498212 : Nat := 118140960795 + 498212 * 2 ^ 59
def prefixEnd_498212 : Nat := 4983230072969 + 3 ^ 40 * 498212 * 2
def baseEnd_498212 : Nat := 9474897179181850998473

theorem tailTrace_498212 : CollatzResearch.WordTrace tailWord_498212 prefixEnd_498212 9474897179181850998473 := by
  unfold tailWord_498212
  simp only [CollatzResearch.WordTrace]
  refine ⟨9085642235535243340260445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12114189647380324453680593 9085642235535243340260445)
  ·
    refine ⟨3407115838325716252597667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9085642235535243340260445 3407115838325716252597667)
    ·
      refine ⟨5110673757488574378896501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3407115838325716252597667 5110673757488574378896501)
      ·
        refine ⟨479125664764553848021547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5110673757488574378896501 479125664764553848021547)
        ·
          refine ⟨718688497146830772032321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479125664764553848021547 718688497146830772032321)
          ·
            refine ⟨539016372860123079024241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 718688497146830772032321 539016372860123079024241)
            ·
              refine ⟨404262279645092309268181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 539016372860123079024241 404262279645092309268181)
              ·
                refine ⟨9474897179181850998473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 404262279645092309268181 9474897179181850998473)
                ·
                  rfl

theorem cell23_498212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 7].length) (baseStart_498212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498212 prefixEnd_498212 := by exact prefixLift 498212
  have htrace : WordTrace (prefixWord ++ tailWord_498212) baseStart_498212 baseEnd_498212 := by
    simpa [prefixWord, tailWord_498212, baseEnd_498212] using wordTrace_append hprefix tailTrace_498212
  have hstable : (prefixWord ++ tailWord_498212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498212).length < 2 ^ (prefixWord ++ tailWord_498212).sum := by decide
  have hdescent : baseEnd_498212 < baseStart_498212 := by decide
  rcases family_descends (prefixWord ++ tailWord_498212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498218 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_498218 : Nat := 118140960795 + 498218 * 2 ^ 59
def prefixEnd_498218 : Nat := 4983230072969 + 3 ^ 40 * 498218 * 2
def baseEnd_498218 : Nat := 255825304721836953483743

theorem tailTrace_498218 : CollatzResearch.WordTrace tailWord_498218 prefixEnd_498218 255825304721836953483743 := by
  unfold tailWord_498218
  simp only [CollatzResearch.WordTrace]
  refine ⟨4542875827262187426309827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12114335539365833136826205 4542875827262187426309827)
  ·
    refine ⟨6814313740893281139464741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4542875827262187426309827 6814313740893281139464741)
    ·
      refine ⟨1277683826417490213649639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6814313740893281139464741 1277683826417490213649639)
      ·
        refine ⟨1916525739626235320474459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1277683826417490213649639 1916525739626235320474459)
        ·
          refine ⟨2874788609439352980711689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1916525739626235320474459 2874788609439352980711689)
          ·
            refine ⟨2156091457079514735533767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2874788609439352980711689 2156091457079514735533767)
            ·
              refine ⟨3234137185619272103300651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2156091457079514735533767 3234137185619272103300651)
              ·
                refine ⟨4851205778428908154950977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3234137185619272103300651 4851205778428908154950977)
                ·
                  refine ⟨3638404333821681116213233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4851205778428908154950977 3638404333821681116213233)
                  ·
                    refine ⟨2728803250366260837159925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3638404333821681116213233 2728803250366260837159925)
                    ·
                      refine ⟨255825304721836953483743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2728803250366260837159925 255825304721836953483743)
                      ·
                        rfl

theorem cell23_498218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_498218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498218 prefixEnd_498218 := by exact prefixLift 498218
  have htrace : WordTrace (prefixWord ++ tailWord_498218) baseStart_498218 baseEnd_498218 := by
    simpa [prefixWord, tailWord_498218, baseEnd_498218] using wordTrace_append hprefix tailTrace_498218
  have hstable : (prefixWord ++ tailWord_498218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498218).length < 2 ^ (prefixWord ++ tailWord_498218).sum := by decide
  have hdescent : baseEnd_498218 < baseStart_498218 := by decide
  rcases family_descends (prefixWord ++ tailWord_498218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498258 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 1, 4, 4]
def baseStart_498258 : Nat := 118140960795 + 498258 * 2 ^ 59
def prefixEnd_498258 : Nat := 4983230072969 + 3 ^ 40 * 498258 * 2
def baseEnd_498258 : Nat := 255845843948016796983559

theorem tailTrace_498258 : CollatzResearch.WordTrace tailWord_498258 prefixEnd_498258 255845843948016796983559 := by
  unfold tailWord_498258
  simp only [CollatzResearch.WordTrace]
  refine ⟨4543240557225959134173857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12115308152602557691130285 4543240557225959134173857)
  ·
    refine ⟨3407430417919469350630393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4543240557225959134173857 3407430417919469350630393)
    ·
      refine ⟨2555572813439602012972795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3407430417919469350630393 2555572813439602012972795)
      ·
        refine ⟨3833359220159403019459193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2555572813439602012972795 3833359220159403019459193)
        ·
          refine ⟨2875019415119552264594395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3833359220159403019459193 2875019415119552264594395)
          ·
            refine ⟨4312529122679328396891593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2875019415119552264594395 4312529122679328396891593)
            ·
              refine ⟨3234396842009496297668695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4312529122679328396891593 3234396842009496297668695)
              ·
                refine ⟨4851595263014244446503043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3234396842009496297668695 4851595263014244446503043)
                ·
                  refine ⟨7277392894521366669754565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4851595263014244446503043 7277392894521366669754565)
                  ·
                    refine ⟨1364511167722756250578981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7277392894521366669754565 1364511167722756250578981)
                    ·
                      refine ⟨255845843948016796983559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1364511167722756250578981 255845843948016796983559)
                      ·
                        rfl

theorem cell23_498258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_498258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498258 prefixEnd_498258 := by exact prefixLift 498258
  have htrace : WordTrace (prefixWord ++ tailWord_498258) baseStart_498258 baseEnd_498258 := by
    simpa [prefixWord, tailWord_498258, baseEnd_498258] using wordTrace_append hprefix tailTrace_498258
  have hstable : (prefixWord ++ tailWord_498258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498258).length < 2 ^ (prefixWord ++ tailWord_498258).sum := by decide
  have hdescent : baseEnd_498258 < baseStart_498258 := by decide
  rcases family_descends (prefixWord ++ tailWord_498258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498271 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 8]
def baseStart_498271 : Nat := 118140960795 + 498271 * 2 ^ 59
def prefixEnd_498271 : Nat := 4983230072969 + 3 ^ 40 * 498271 * 2
def baseEnd_498271 : Nat := 255852519196525246120999

theorem tailTrace_498271 : CollatzResearch.WordTrace tailWord_498271 prefixEnd_498271 255852519196525246120999 := by
  unfold tailWord_498271
  simp only [CollatzResearch.WordTrace]
  refine ⟨18173436377856739756918667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12115624251904493171279111 18173436377856739756918667)
  ·
    refine ⟨27260154566785109635378001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18173436377856739756918667 27260154566785109635378001)
    ·
      refine ⟨20445115925088832226533501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27260154566785109635378001 20445115925088832226533501)
      ·
        refine ⟨7666918471908312084950063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20445115925088832226533501 7666918471908312084950063)
        ·
          refine ⟨11500377707862468127425095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7666918471908312084950063 11500377707862468127425095)
          ·
            refine ⟨17250566561793702191137643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11500377707862468127425095 17250566561793702191137643)
            ·
              refine ⟨25875849842690553286706465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17250566561793702191137643 25875849842690553286706465)
              ·
                refine ⟨19406887382017914965029849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25875849842690553286706465 19406887382017914965029849)
                ·
                  refine ⟨14555165536513436223772387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19406887382017914965029849 14555165536513436223772387)
                  ·
                    refine ⟨21832748304770154335658581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14555165536513436223772387 21832748304770154335658581)
                    ·
                      refine ⟨255852519196525246120999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 21832748304770154335658581 255852519196525246120999)
                      ·
                        rfl

theorem cell23_498271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_498271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498271 prefixEnd_498271 := by exact prefixLift 498271
  have htrace : WordTrace (prefixWord ++ tailWord_498271) baseStart_498271 baseEnd_498271 := by
    simpa [prefixWord, tailWord_498271, baseEnd_498271] using wordTrace_append hprefix tailTrace_498271
  have hstable : (prefixWord ++ tailWord_498271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498271).length < 2 ^ (prefixWord ++ tailWord_498271).sum := by decide
  have hdescent : baseEnd_498271 < baseStart_498271 := by decide
  rcases family_descends (prefixWord ++ tailWord_498271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498305 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 1, 7, 2]
def baseStart_498305 : Nat := 118140960795 + 498305 * 2 ^ 59
def prefixEnd_498305 : Nat := 4983230072969 + 3 ^ 40 * 498305 * 2
def baseEnd_498305 : Nat := 255869977538778113095843

theorem tailTrace_498305 : CollatzResearch.WordTrace tailWord_498305 prefixEnd_498305 255869977538778113095843 := by
  unfold tailWord_498305
  simp only [CollatzResearch.WordTrace]
  refine ⟨18174676459733563563656369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12116450973155709042437579 18174676459733563563656369)
  ·
    refine ⟨13631007344800172672742277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18174676459733563563656369 13631007344800172672742277)
    ·
      refine ⟨2555813877150032376139177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13631007344800172672742277 2555813877150032376139177)
      ·
        refine ⟨1916860407862524282104383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2555813877150032376139177 1916860407862524282104383)
        ·
          refine ⟨2875290611793786423156575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1916860407862524282104383 2875290611793786423156575)
          ·
            refine ⟨4312935917690679634734863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2875290611793786423156575 4312935917690679634734863)
            ·
              refine ⟨6469403876536019452102295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4312935917690679634734863 6469403876536019452102295)
              ·
                refine ⟨9704105814804029178153443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6469403876536019452102295 9704105814804029178153443)
                ·
                  refine ⟨14556158722206043767230165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9704105814804029178153443 14556158722206043767230165)
                  ·
                    refine ⟨341159970051704150794457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14556158722206043767230165 341159970051704150794457)
                    ·
                      refine ⟨255869977538778113095843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 341159970051704150794457 255869977538778113095843)
                      ·
                        rfl

theorem cell23_498305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_498305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498305 prefixEnd_498305 := by exact prefixLift 498305
  have htrace : WordTrace (prefixWord ++ tailWord_498305) baseStart_498305 baseEnd_498305 := by
    simpa [prefixWord, tailWord_498305, baseEnd_498305] using wordTrace_append hprefix tailTrace_498305
  have hstable : (prefixWord ++ tailWord_498305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498305).length < 2 ^ (prefixWord ++ tailWord_498305).sum := by decide
  have hdescent : baseEnd_498305 < baseStart_498305 := by decide
  rcases family_descends (prefixWord ++ tailWord_498305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498332 : List Nat := [2, 2, 3, 2, 2, 3, 1, 1, 2, 5]
def baseStart_498332 : Nat := 118140960795 + 498332 * 2 ^ 59
def prefixEnd_498332 : Nat := 4983230072969 + 3 ^ 40 * 498332 * 2
def baseEnd_498332 : Nat := 85294613838816502486073

theorem tailTrace_498332 : CollatzResearch.WordTrace tailWord_498332 prefixEnd_498332 85294613838816502486073 := by
  unfold tailWord_498332
  simp only [CollatzResearch.WordTrace]
  refine ⟨9087830615317873587444625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12117107487090498116592833 9087830615317873587444625)
  ·
    refine ⟨6815872961488405190583469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9087830615317873587444625 6815872961488405190583469)
    ·
      refine ⟨2555952360558151946468801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6815872961488405190583469 2555952360558151946468801)
      ·
        refine ⟨1916964270418613959851601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2555952360558151946468801 1916964270418613959851601)
        ·
          refine ⟨1437723202813960469888701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1916964270418613959851601 1437723202813960469888701)
          ·
            refine ⟨539146201055235176208263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1437723202813960469888701 539146201055235176208263)
            ·
              refine ⟨808719301582852764312395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539146201055235176208263 808719301582852764312395)
              ·
                refine ⟨1213078952374279146468593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808719301582852764312395 1213078952374279146468593)
                ·
                  refine ⟨909809214280709359851445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1213078952374279146468593 909809214280709359851445)
                  ·
                    refine ⟨85294613838816502486073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 909809214280709359851445 85294613838816502486073)
                    ·
                      rfl

theorem cell23_498332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_498332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498332 prefixEnd_498332 := by exact prefixLift 498332
  have htrace : WordTrace (prefixWord ++ tailWord_498332) baseStart_498332 baseEnd_498332 := by
    simpa [prefixWord, tailWord_498332, baseEnd_498332] using wordTrace_append hprefix tailTrace_498332
  have hstable : (prefixWord ++ tailWord_498332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498332).length < 2 ^ (prefixWord ++ tailWord_498332).sum := by decide
  have hdescent : baseEnd_498332 < baseStart_498332 := by decide
  rcases family_descends (prefixWord ++ tailWord_498332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498362 : List Nat := [3, 1, 1, 1, 2, 3, 1, 6, 1, 4]
def baseStart_498362 : Nat := 118140960795 + 498362 * 2 ^ 59
def prefixEnd_498362 : Nat := 4983230072969 + 3 ^ 40 * 498362 * 2
def baseEnd_498362 : Nat := 85299748645361463361027

theorem tailTrace_498362 : CollatzResearch.WordTrace tailWord_498362 prefixEnd_498362 85299748645361463361027 := by
  unfold tailWord_498362
  simp only [CollatzResearch.WordTrace]
  refine ⟨4544188855131765574620335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12117836947018041532320893 4544188855131765574620335)
  ·
    refine ⟨6816283282697648361930503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4544188855131765574620335 6816283282697648361930503)
    ·
      refine ⟨10224424924046472542895755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6816283282697648361930503 10224424924046472542895755)
      ·
        refine ⟨15336637386069708814343633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10224424924046472542895755 15336637386069708814343633)
        ·
          refine ⟨11502478039552281610757725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15336637386069708814343633 11502478039552281610757725)
          ·
            refine ⟨4313429264832105604034147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11502478039552281610757725 4313429264832105604034147)
            ·
              refine ⟨6470143897248158406051221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4313429264832105604034147 6470143897248158406051221)
              ·
                refine ⟨303287995183507425283651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6470143897248158406051221 303287995183507425283651)
                ·
                  refine ⟨454931992775261137925477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 303287995183507425283651 454931992775261137925477)
                  ·
                    refine ⟨85299748645361463361027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 454931992775261137925477 85299748645361463361027)
                    ·
                      rfl

theorem cell23_498362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 6, 1, 4].length) (baseStart_498362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498362 prefixEnd_498362 := by exact prefixLift 498362
  have htrace : WordTrace (prefixWord ++ tailWord_498362) baseStart_498362 baseEnd_498362 := by
    simpa [prefixWord, tailWord_498362, baseEnd_498362] using wordTrace_append hprefix tailTrace_498362
  have hstable : (prefixWord ++ tailWord_498362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498362).length < 2 ^ (prefixWord ++ tailWord_498362).sum := by decide
  have hdescent : baseEnd_498362 < baseStart_498362 := by decide
  rcases family_descends (prefixWord ++ tailWord_498362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498396 : List Nat := [2, 2, 5, 1, 1, 1, 3, 3, 1, 4]
def baseStart_498396 : Nat := 118140960795 + 498396 * 2 ^ 59
def prefixEnd_498396 : Nat := 4983230072969 + 3 ^ 40 * 498396 * 2
def baseEnd_498396 : Nat := 85305568092779085685975

theorem tailTrace_498396 : CollatzResearch.WordTrace tailWord_498396 prefixEnd_498396 85305568092779085685975 := by
  unfold tailWord_498396
  simp only [CollatzResearch.WordTrace]
  refine ⟨9088997751201943052609521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12118663668269257403479361 9088997751201943052609521)
  ·
    refine ⟨6816748313401457289457141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9088997751201943052609521 6816748313401457289457141)
    ·
      refine ⟨639070154381386620886607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6816748313401457289457141 639070154381386620886607)
      ·
        refine ⟨958605231572079931329911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 639070154381386620886607 958605231572079931329911)
        ·
          refine ⟨1437907847358119896994867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 958605231572079931329911 1437907847358119896994867)
          ·
            refine ⟨2156861771037179845492301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1437907847358119896994867 2156861771037179845492301)
            ·
              refine ⟨808823164138942442059613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2156861771037179845492301 808823164138942442059613)
              ·
                refine ⟨303308686552103415772355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 808823164138942442059613 303308686552103415772355)
                ·
                  refine ⟨454963029828155123658533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 303308686552103415772355 454963029828155123658533)
                  ·
                    refine ⟨85305568092779085685975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 454963029828155123658533 85305568092779085685975)
                    ·
                      rfl

theorem cell23_498396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_498396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498396 prefixEnd_498396 := by exact prefixLift 498396
  have htrace : WordTrace (prefixWord ++ tailWord_498396) baseStart_498396 baseEnd_498396 := by
    simpa [prefixWord, tailWord_498396, baseEnd_498396] using wordTrace_append hprefix tailTrace_498396
  have hstable : (prefixWord ++ tailWord_498396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498396).length < 2 ^ (prefixWord ++ tailWord_498396).sum := by decide
  have hdescent : baseEnd_498396 < baseStart_498396 := by decide
  rcases family_descends (prefixWord ++ tailWord_498396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498439 : List Nat := [1, 1, 4, 4, 1, 3, 1, 2, 1, 5]
def baseStart_498439 : Nat := 118140960795 + 498439 * 2 ^ 59
def prefixEnd_498439 : Nat := 4983230072969 + 3 ^ 40 * 498439 * 2
def baseEnd_498439 : Nat := 85312927982160196273409

theorem tailTrace_498439 : CollatzResearch.WordTrace tailWord_498439 prefixEnd_498439 85312927982160196273409 := by
  unfold tailWord_498439
  simp only [CollatzResearch.WordTrace]
  refine ⟨18179563841248104449034371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12119709227498736299356247 18179563841248104449034371)
  ·
    refine ⟨27269345761872156673551557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18179563841248104449034371 27269345761872156673551557)
    ·
      refine ⟨5113002330351029376290917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27269345761872156673551557 5113002330351029376290917)
      ·
        refine ⟨958687936940818008054547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5113002330351029376290917 958687936940818008054547)
        ·
          refine ⟨1438031905411227012081821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 958687936940818008054547 1438031905411227012081821)
          ·
            refine ⟨539261964529210129530683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1438031905411227012081821 539261964529210129530683)
            ·
              refine ⟨808892946793815194296025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539261964529210129530683 808892946793815194296025)
              ·
                refine ⟨606669710095361395722019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 808892946793815194296025 606669710095361395722019)
                ·
                  refine ⟨910004565143042093583029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 606669710095361395722019 910004565143042093583029)
                  ·
                    refine ⟨85312927982160196273409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 910004565143042093583029 85312927982160196273409)
                    ·
                      rfl

theorem cell23_498439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_498439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498439 prefixEnd_498439 := by exact prefixLift 498439
  have htrace : WordTrace (prefixWord ++ tailWord_498439) baseStart_498439 baseEnd_498439 := by
    simpa [prefixWord, tailWord_498439, baseEnd_498439] using wordTrace_append hprefix tailTrace_498439
  have hstable : (prefixWord ++ tailWord_498439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498439).length < 2 ^ (prefixWord ++ tailWord_498439).sum := by decide
  have hdescent : baseEnd_498439 < baseStart_498439 := by decide
  rcases family_descends (prefixWord ++ tailWord_498439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498476 : List Nat := [2, 2, 1, 1, 1, 4, 3, 4, 1, 2, 2]
def baseStart_498476 : Nat := 118140960795 + 498476 * 2 ^ 59
def prefixEnd_498476 : Nat := 4983230072969 + 3 ^ 40 * 498476 * 2
def baseEnd_498476 : Nat := 255957782730696944057557

theorem tailTrace_498476 : CollatzResearch.WordTrace tailWord_498476 prefixEnd_498476 255957782730696944057557 := by
  unfold tailWord_498476
  simp only [CollatzResearch.WordTrace]
  refine ⟨9090456671057029884065641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12120608894742706512087521 9090456671057029884065641)
  ·
    refine ⟨6817842503292772413049231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9090456671057029884065641 6817842503292772413049231)
    ·
      refine ⟨10226763754939158619573847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6817842503292772413049231 10226763754939158619573847)
      ·
        refine ⟨15340145632408737929360771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10226763754939158619573847 15340145632408737929360771)
        ·
          refine ⟨23010218448613106894041157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15340145632408737929360771 23010218448613106894041157)
          ·
            refine ⟨4314415959114957542632717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23010218448613106894041157 4314415959114957542632717)
            ·
              refine ⟨1617905984668109078487269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4314415959114957542632717 1617905984668109078487269)
              ·
                refine ⟨303357372125270452216363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1617905984668109078487269 303357372125270452216363)
                ·
                  refine ⟨455036058187905678324545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 303357372125270452216363 455036058187905678324545)
                  ·
                    refine ⟨341277043640929258743409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 455036058187905678324545 341277043640929258743409)
                    ·
                      refine ⟨255957782730696944057557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 341277043640929258743409 255957782730696944057557)
                      ·
                        rfl

theorem cell23_498476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4, 1, 2, 2].length) (baseStart_498476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498476 prefixEnd_498476 := by exact prefixLift 498476
  have htrace : WordTrace (prefixWord ++ tailWord_498476) baseStart_498476 baseEnd_498476 := by
    simpa [prefixWord, tailWord_498476, baseEnd_498476] using wordTrace_append hprefix tailTrace_498476
  have hstable : (prefixWord ++ tailWord_498476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498476).length < 2 ^ (prefixWord ++ tailWord_498476).sum := by decide
  have hdescent : baseEnd_498476 < baseStart_498476 := by decide
  rcases family_descends (prefixWord ++ tailWord_498476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498492 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 6, 1, 3]
def baseStart_498492 : Nat := 118140960795 + 498492 * 2 ^ 59
def prefixEnd_498492 : Nat := 4983230072969 + 3 ^ 40 * 498492 * 2
def baseEnd_498492 : Nat := 255965998421168881457483

theorem tailTrace_498492 : CollatzResearch.WordTrace tailWord_498492 prefixEnd_498492 255965998421168881457483 := by
  unfold tailWord_498492
  simp only [CollatzResearch.WordTrace]
  refine ⟨9090748455028047250356865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12120997940037396333809153 9090748455028047250356865)
  ·
    refine ⟨6818061341271035437767649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9090748455028047250356865 6818061341271035437767649)
    ·
      refine ⟨5113546005953276578325737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6818061341271035437767649 5113546005953276578325737)
      ·
        refine ⟨3835159504464957433744303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5113546005953276578325737 3835159504464957433744303)
        ·
          refine ⟨5752739256697436150616455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3835159504464957433744303 5752739256697436150616455)
          ·
            refine ⟨8629108885046154225924683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5752739256697436150616455 8629108885046154225924683)
            ·
              refine ⟨12943663327569231338887025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8629108885046154225924683 12943663327569231338887025)
              ·
                refine ⟨9707747495676923504165269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12943663327569231338887025 9707747495676923504165269)
                ·
                  refine ⟨455050663859855789257747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9707747495676923504165269 455050663859855789257747)
                  ·
                    refine ⟨682575995789783683886621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 455050663859855789257747 682575995789783683886621)
                    ·
                      refine ⟨255965998421168881457483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 682575995789783683886621 255965998421168881457483)
                      ·
                        rfl

theorem cell23_498492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_498492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498492 prefixEnd_498492 := by exact prefixLift 498492
  have htrace : WordTrace (prefixWord ++ tailWord_498492) baseStart_498492 baseEnd_498492 := by
    simpa [prefixWord, tailWord_498492, baseEnd_498492] using wordTrace_append hprefix tailTrace_498492
  have hstable : (prefixWord ++ tailWord_498492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498492).length < 2 ^ (prefixWord ++ tailWord_498492).sum := by decide
  have hdescent : baseEnd_498492 < baseStart_498492 := by decide
  rcases family_descends (prefixWord ++ tailWord_498492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498513 : List Nat := [1, 2, 2, 1, 7, 1, 2, 1, 1, 2, 3]
def baseStart_498513 : Nat := 118140960795 + 498513 * 2 ^ 59
def prefixEnd_498513 : Nat := 4983230072969 + 3 ^ 40 * 498513 * 2
def baseEnd_498513 : Nat := 255976781514913299294887

theorem tailTrace_498513 : CollatzResearch.WordTrace tailWord_498513 prefixEnd_498513 255976781514913299294887 := by
  unfold tailWord_498513
  simp only [CollatzResearch.WordTrace]
  refine ⟨18182262842980015087228193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12121508561986676724818795 18182262842980015087228193)
  ·
    refine ⟨13636697132235011315421145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18182262842980015087228193 13636697132235011315421145)
    ·
      refine ⟨10227522849176258486565859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13636697132235011315421145 10227522849176258486565859)
      ·
        refine ⟨15341284273764387729848789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10227522849176258486565859 15341284273764387729848789)
        ·
          refine ⟨359561350166352837418331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 15341284273764387729848789 359561350166352837418331)
          ·
            refine ⟨539342025249529256127497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359561350166352837418331 539342025249529256127497)
            ·
              refine ⟨404506518937146942095623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 539342025249529256127497 404506518937146942095623)
              ·
                refine ⟨606759778405720413143435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 404506518937146942095623 606759778405720413143435)
                ·
                  refine ⟨910139667608580619715153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 606759778405720413143435 910139667608580619715153)
                  ·
                    refine ⟨682604750706435464786365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 910139667608580619715153 682604750706435464786365)
                    ·
                      refine ⟨255976781514913299294887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 682604750706435464786365 255976781514913299294887)
                      ·
                        rfl

theorem cell23_498513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 1, 2, 3].length) (baseStart_498513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498513 prefixEnd_498513 := by exact prefixLift 498513
  have htrace : WordTrace (prefixWord ++ tailWord_498513) baseStart_498513 baseEnd_498513 := by
    simpa [prefixWord, tailWord_498513, baseEnd_498513] using wordTrace_append hprefix tailTrace_498513
  have hstable : (prefixWord ++ tailWord_498513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498513).length < 2 ^ (prefixWord ++ tailWord_498513).sum := by decide
  have hdescent : baseEnd_498513 < baseStart_498513 := by decide
  rcases family_descends (prefixWord ++ tailWord_498513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498555 : List Nat := [1, 1, 1, 1, 1, 5, 4, 2, 7]
def baseStart_498555 : Nat := 118140960795 + 498555 * 2 ^ 59
def prefixEnd_498555 : Nat := 4983230072969 + 3 ^ 40 * 498555 * 2
def baseEnd_498555 : Nat := 28444260855822459441077

theorem tailTrace_498555 : CollatzResearch.WordTrace tailWord_498555 prefixEnd_498555 28444260855822459441077 := by
  unfold tailWord_498555
  simp only [CollatzResearch.WordTrace]
  refine ⟨18183794708827856260257119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12122529805885237506838079 18183794708827856260257119)
  ·
    refine ⟨27275692063241784390385679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18183794708827856260257119 27275692063241784390385679)
    ·
      refine ⟨40913538094862676585578519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27275692063241784390385679 40913538094862676585578519)
      ·
        refine ⟨61370307142294014878367779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40913538094862676585578519 61370307142294014878367779)
        ·
          refine ⟨92055460713441022317551669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61370307142294014878367779 92055460713441022317551669)
          ·
            refine ⟨8630199441885095842270469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92055460713441022317551669 8630199441885095842270469)
            ·
              refine ⟨1618162395353455470425713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8630199441885095842270469 1618162395353455470425713)
              ·
                refine ⟨1213621796515091602819285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1618162395353455470425713 1213621796515091602819285)
                ·
                  refine ⟨28444260855822459441077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1213621796515091602819285 28444260855822459441077)
                  ·
                    rfl

theorem cell23_498555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 7].length) (baseStart_498555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498555 prefixEnd_498555 := by exact prefixLift 498555
  have htrace : WordTrace (prefixWord ++ tailWord_498555) baseStart_498555 baseEnd_498555 := by
    simpa [prefixWord, tailWord_498555, baseEnd_498555] using wordTrace_append hprefix tailTrace_498555
  have hstable : (prefixWord ++ tailWord_498555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498555).length < 2 ^ (prefixWord ++ tailWord_498555).sum := by decide
  have hdescent : baseEnd_498555 < baseStart_498555 := by decide
  rcases family_descends (prefixWord ++ tailWord_498555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498595 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 7]
def baseStart_498595 : Nat := 118140960795 + 498595 * 2 ^ 59
def prefixEnd_498595 : Nat := 4983230072969 + 3 ^ 40 * 498595 * 2
def baseEnd_498595 : Nat := 256018886928581978469509

theorem tailTrace_498595 : CollatzResearch.WordTrace tailWord_498595 prefixEnd_498595 256018886928581978469509 := by
  unfold tailWord_498595
  simp only [CollatzResearch.WordTrace]
  refine ⟨18185253628682943091713239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12123502419121962061142159 18185253628682943091713239)
  ·
    refine ⟨27277880443024414637569859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18185253628682943091713239 27277880443024414637569859)
    ·
      refine ⟨40916820664536621956354789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27277880443024414637569859 40916820664536621956354789)
      ·
        refine ⟨7671903874600616616816523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40916820664536621956354789 7671903874600616616816523)
        ·
          refine ⟨11507855811900924925224785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7671903874600616616816523 11507855811900924925224785)
          ·
            refine ⟨8630891858925693693918589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11507855811900924925224785 8630891858925693693918589)
            ·
              refine ⟨3236584447097135135219471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8630891858925693693918589 3236584447097135135219471)
              ·
                refine ⟨4854876670645702702829207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3236584447097135135219471 4854876670645702702829207)
                ·
                  refine ⟨7282315005968554054243811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4854876670645702702829207 7282315005968554054243811)
                  ·
                    refine ⟨10923472508952831081365717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7282315005968554054243811 10923472508952831081365717)
                    ·
                      refine ⟨256018886928581978469509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 10923472508952831081365717 256018886928581978469509)
                      ·
                        rfl

theorem cell23_498595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_498595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498595 prefixEnd_498595 := by exact prefixLift 498595
  have htrace : WordTrace (prefixWord ++ tailWord_498595) baseStart_498595 baseEnd_498595 := by
    simpa [prefixWord, tailWord_498595, baseEnd_498595] using wordTrace_append hprefix tailTrace_498595
  have hstable : (prefixWord ++ tailWord_498595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498595).length < 2 ^ (prefixWord ++ tailWord_498595).sum := by decide
  have hdescent : baseEnd_498595 < baseStart_498595 := by decide
  rcases family_descends (prefixWord ++ tailWord_498595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498615 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 2, 8]
def baseStart_498615 : Nat := 118140960795 + 498615 * 2 ^ 59
def prefixEnd_498615 : Nat := 4983230072969 + 3 ^ 40 * 498615 * 2
def baseEnd_498615 : Nat := 85343052180557300073139

theorem tailTrace_498615 : CollatzResearch.WordTrace tailWord_498615 prefixEnd_498615 85343052180557300073139 := by
  unfold tailWord_498615
  simp only [CollatzResearch.WordTrace]
  refine ⟨18185983088610486507441299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12123988725740324338294199 18185983088610486507441299)
  ·
    refine ⟨27278974632915729761161949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18185983088610486507441299 27278974632915729761161949)
    ·
      refine ⟨10229615487343398660435731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27278974632915729761161949 10229615487343398660435731)
      ·
        refine ⟨15344423231015097990653597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10229615487343398660435731 15344423231015097990653597)
        ·
          refine ⟨5754158711630661746495099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15344423231015097990653597 5754158711630661746495099)
          ·
            refine ⟨8631238067445992619742649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5754158711630661746495099 8631238067445992619742649)
            ·
              refine ⟨6473428550584494464806987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8631238067445992619742649 6473428550584494464806987)
              ·
                refine ⟨9710142825876741697210481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6473428550584494464806987 9710142825876741697210481)
                ·
                  refine ⟨7282607119407556272907861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9710142825876741697210481 7282607119407556272907861)
                  ·
                    refine ⟨85343052180557300073139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7282607119407556272907861 85343052180557300073139)
                    ·
                      rfl

theorem cell23_498615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 8].length) (baseStart_498615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498615 prefixEnd_498615 := by exact prefixLift 498615
  have htrace : WordTrace (prefixWord ++ tailWord_498615) baseStart_498615 baseEnd_498615 := by
    simpa [prefixWord, tailWord_498615, baseEnd_498615] using wordTrace_append hprefix tailTrace_498615
  have hstable : (prefixWord ++ tailWord_498615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498615).length < 2 ^ (prefixWord ++ tailWord_498615).sum := by decide
  have hdescent : baseEnd_498615 < baseStart_498615 := by decide
  rcases family_descends (prefixWord ++ tailWord_498615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498732 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 5]
def baseStart_498732 : Nat := 118140960795 + 498732 * 2 ^ 59
def prefixEnd_498732 : Nat := 4983230072969 + 3 ^ 40 * 498732 * 2
def baseEnd_498732 : Nat := 256089233778247942456379

theorem tailTrace_498732 : CollatzResearch.WordTrace tailWord_498732 prefixEnd_498732 256089233778247942456379 := by
  unfold tailWord_498732
  simp only [CollatzResearch.WordTrace]
  refine ⟨9095125214593307744725225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12126833619457743659633633 9095125214593307744725225)
  ·
    refine ⟨6821343910944980808543919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9095125214593307744725225 6821343910944980808543919)
    ·
      refine ⟨10232015866417471212815879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6821343910944980808543919 10232015866417471212815879)
      ·
        refine ⟨15348023799626206819223819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10232015866417471212815879 15348023799626206819223819)
        ·
          refine ⟨23022035699439310228835729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15348023799626206819223819 23022035699439310228835729)
          ·
            refine ⟨17266526774579482671626797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23022035699439310228835729 17266526774579482671626797)
            ·
              refine ⟨6474947540467306001860049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17266526774579482671626797 6474947540467306001860049)
              ·
                refine ⟨4856210655350479501395037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6474947540467306001860049 4856210655350479501395037)
                ·
                  refine ⟨1821078995756429813023139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4856210655350479501395037 1821078995756429813023139)
                  ·
                    refine ⟨2731618493634644719534709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1821078995756429813023139 2731618493634644719534709)
                    ·
                      refine ⟨256089233778247942456379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2731618493634644719534709 256089233778247942456379)
                      ·
                        rfl

theorem cell23_498732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_498732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498732 prefixEnd_498732 := by exact prefixLift 498732
  have htrace : WordTrace (prefixWord ++ tailWord_498732) baseStart_498732 baseEnd_498732 := by
    simpa [prefixWord, tailWord_498732, baseEnd_498732] using wordTrace_append hprefix tailTrace_498732
  have hstable : (prefixWord ++ tailWord_498732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498732).length < 2 ^ (prefixWord ++ tailWord_498732).sum := by decide
  have hdescent : baseEnd_498732 < baseStart_498732 := by decide
  rcases family_descends (prefixWord ++ tailWord_498732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498746 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 5, 2, 2]
def baseStart_498746 : Nat := 118140960795 + 498746 * 2 ^ 59
def prefixEnd_498746 : Nat := 4983230072969 + 3 ^ 40 * 498746 * 2
def baseEnd_498746 : Nat := 256096422507410887681315

theorem tailTrace_498746 : CollatzResearch.WordTrace tailWord_498746 prefixEnd_498746 256096422507410887681315 := by
  unfold tailWord_498746
  simp only [CollatzResearch.WordTrace]
  refine ⟨4547690262783973970115023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12127174034090597253640061 4547690262783973970115023)
  ·
    refine ⟨6821535394175960955172535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4547690262783973970115023 6821535394175960955172535)
    ·
      refine ⟨10232303091263941432758803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6821535394175960955172535 10232303091263941432758803)
      ·
        refine ⟨15348454636895912149138205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10232303091263941432758803 15348454636895912149138205)
        ·
          refine ⟨5755670488835967055926827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15348454636895912149138205 5755670488835967055926827)
          ·
            refine ⟨8633505733253950583890241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5755670488835967055926827 8633505733253950583890241)
            ·
              refine ⟨6475129299940462937917681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8633505733253950583890241 6475129299940462937917681)
              ·
                refine ⟨4856346974955347203438261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6475129299940462937917681 4856346974955347203438261)
                ·
                  refine ⟨455282528902063800322337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4856346974955347203438261 455282528902063800322337)
                  ·
                    refine ⟨341461896676547850241753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 455282528902063800322337 341461896676547850241753)
                    ·
                      refine ⟨256096422507410887681315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 341461896676547850241753 256096422507410887681315)
                      ·
                        rfl

theorem cell23_498746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 5, 2, 2].length) (baseStart_498746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498746 prefixEnd_498746 := by exact prefixLift 498746
  have htrace : WordTrace (prefixWord ++ tailWord_498746) baseStart_498746 baseEnd_498746 := by
    simpa [prefixWord, tailWord_498746, baseEnd_498746] using wordTrace_append hprefix tailTrace_498746
  have hstable : (prefixWord ++ tailWord_498746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498746).length < 2 ^ (prefixWord ++ tailWord_498746).sum := by decide
  have hdescent : baseEnd_498746 < baseStart_498746 := by decide
  rcases family_descends (prefixWord ++ tailWord_498746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498749 : List Nat := [1, 4, 1, 3, 1, 2, 1, 3, 1, 1, 5]
def baseStart_498749 : Nat := 118140960795 + 498749 * 2 ^ 59
def prefixEnd_498749 : Nat := 4983230072969 + 3 ^ 40 * 498749 * 2
def baseEnd_498749 : Nat := 256097962949374375943801

theorem tailTrace_498749 : CollatzResearch.WordTrace tailWord_498749 prefixEnd_498749 256097962949374375943801 := by
  unfold tailWord_498749
  simp only [CollatzResearch.WordTrace]
  refine ⟨18190870470125027392819301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12127246980083351595212867 18190870470125027392819301)
  ·
    refine ⟨3410788213148442636153619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18190870470125027392819301 3410788213148442636153619)
    ·
      refine ⟨5116182319722663954230429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3410788213148442636153619 5116182319722663954230429)
      ·
        refine ⟨1918568369895998982836411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5116182319722663954230429 1918568369895998982836411)
        ·
          refine ⟨2877852554843998474254617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1918568369895998982836411 2877852554843998474254617)
          ·
            refine ⟨2158389416132998855690963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2877852554843998474254617 2158389416132998855690963)
            ·
              refine ⟨3237584124199498283536445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2158389416132998855690963 3237584124199498283536445)
              ·
                refine ⟨1214094046574811856326167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3237584124199498283536445 1214094046574811856326167)
                ·
                  refine ⟨1821141069862217784489251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1214094046574811856326167 1821141069862217784489251)
                  ·
                    refine ⟨2731711604793326676733877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1821141069862217784489251 2731711604793326676733877)
                    ·
                      refine ⟨256097962949374375943801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2731711604793326676733877 256097962949374375943801)
                      ·
                        rfl

theorem cell23_498749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_498749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498749 prefixEnd_498749 := by exact prefixLift 498749
  have htrace : WordTrace (prefixWord ++ tailWord_498749) baseStart_498749 baseEnd_498749 := by
    simpa [prefixWord, tailWord_498749, baseEnd_498749] using wordTrace_append hprefix tailTrace_498749
  have hstable : (prefixWord ++ tailWord_498749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498749).length < 2 ^ (prefixWord ++ tailWord_498749).sum := by decide
  have hdescent : baseEnd_498749 < baseStart_498749 := by decide
  rcases family_descends (prefixWord ++ tailWord_498749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498813 : List Nat := [1, 4, 1, 1, 3, 1, 4, 2, 2, 1, 3]
def baseStart_498813 : Nat := 118140960795 + 498813 * 2 ^ 59
def prefixEnd_498813 : Nat := 4983230072969 + 3 ^ 40 * 498813 * 2
def baseEnd_498813 : Nat := 256130825711262125543507

theorem tailTrace_498813 : CollatzResearch.WordTrace tailWord_498813 prefixEnd_498813 256130825711262125543507 := by
  unfold tailWord_498813
  simp only [CollatzResearch.WordTrace]
  refine ⟨18193204741893166323149093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12128803161262110882099395 18193204741893166323149093)
  ·
    refine ⟨3411225889104968685590455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18193204741893166323149093 3411225889104968685590455)
    ·
      refine ⟨5116838833657453028385683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3411225889104968685590455 5116838833657453028385683)
      ·
        refine ⟨7675258250486179542578525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5116838833657453028385683 7675258250486179542578525)
        ·
          refine ⟨2878221843932317328466947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7675258250486179542578525 2878221843932317328466947)
          ·
            refine ⟨4317332765898475992700421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2878221843932317328466947 4317332765898475992700421)
            ·
              refine ⟨809499893605964248631329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4317332765898475992700421 809499893605964248631329)
              ·
                refine ⟨607124920204473186473497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 809499893605964248631329 607124920204473186473497)
                ·
                  refine ⟨455343690153354889855123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 607124920204473186473497 455343690153354889855123)
                  ·
                    refine ⟨683015535230032334782685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 455343690153354889855123 683015535230032334782685)
                    ·
                      refine ⟨256130825711262125543507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 683015535230032334782685 256130825711262125543507)
                      ·
                        rfl

theorem cell23_498813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_498813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498813 prefixEnd_498813 := by exact prefixLift 498813
  have htrace : WordTrace (prefixWord ++ tailWord_498813) baseStart_498813 baseEnd_498813 := by
    simpa [prefixWord, tailWord_498813, baseEnd_498813] using wordTrace_append hprefix tailTrace_498813
  have hstable : (prefixWord ++ tailWord_498813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498813).length < 2 ^ (prefixWord ++ tailWord_498813).sum := by decide
  have hdescent : baseEnd_498813 < baseStart_498813 := by decide
  rcases family_descends (prefixWord ++ tailWord_498813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498849 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 1, 4, 4]
def baseStart_498849 : Nat := 118140960795 + 498849 * 2 ^ 59
def prefixEnd_498849 : Nat := 4983230072969 + 3 ^ 40 * 498849 * 2
def baseEnd_498849 : Nat := 256149311014823984693341

theorem tailTrace_498849 : CollatzResearch.WordTrace tailWord_498849 prefixEnd_498849 256149311014823984693341 := by
  unfold tailWord_498849
  simp only [CollatzResearch.WordTrace]
  refine ⟨18194517769762744471459601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12129678513175162980973067 18194517769762744471459601)
  ·
    refine ⟨13645888327322058353594701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18194517769762744471459601 13645888327322058353594701)
    ·
      refine ⟨5117208122745771882598013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13645888327322058353594701 5117208122745771882598013)
      ·
        refine ⟨1918953046029664455974255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5117208122745771882598013 1918953046029664455974255)
        ·
          refine ⟨2878429569044496683961383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1918953046029664455974255 2878429569044496683961383)
          ·
            refine ⟨4317644353566745025942075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2878429569044496683961383 4317644353566745025942075)
            ·
              refine ⟨6476466530350117538913113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4317644353566745025942075 6476466530350117538913113)
              ·
                refine ⟨4857349897762588154184835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6476466530350117538913113 4857349897762588154184835)
                ·
                  refine ⟨7286024846643882231277253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4857349897762588154184835 7286024846643882231277253)
                  ·
                    refine ⟨1366129658745727918364485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7286024846643882231277253 1366129658745727918364485)
                    ·
                      refine ⟨256149311014823984693341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1366129658745727918364485 256149311014823984693341)
                      ·
                        rfl

theorem cell23_498849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_498849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498849 prefixEnd_498849 := by exact prefixLift 498849
  have htrace : WordTrace (prefixWord ++ tailWord_498849) baseStart_498849 baseEnd_498849 := by
    simpa [prefixWord, tailWord_498849, baseEnd_498849] using wordTrace_append hprefix tailTrace_498849
  have hstable : (prefixWord ++ tailWord_498849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498849).length < 2 ^ (prefixWord ++ tailWord_498849).sum := by decide
  have hdescent : baseEnd_498849 < baseStart_498849 := by decide
  rcases family_descends (prefixWord ++ tailWord_498849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498876 : List Nat := [2, 2, 2, 3, 2, 2, 2, 1, 7]
def baseStart_498876 : Nat := 118140960795 + 498876 * 2 ^ 59
def prefixEnd_498876 : Nat := 4983230072969 + 3 ^ 40 * 498876 * 2
def baseEnd_498876 : Nat := 28462574999166153228413

theorem tailTrace_498876 : CollatzResearch.WordTrace tailWord_498876 prefixEnd_498876 28462574999166153228413 := by
  unfold tailWord_498876
  simp only [CollatzResearch.WordTrace]
  refine ⟨9097751270332464041346241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12130335027109952055128321 9097751270332464041346241)
  ·
    refine ⟨6823313452749348031009681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9097751270332464041346241 6823313452749348031009681)
    ·
      refine ⟨5117485089562011023257261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6823313452749348031009681 5117485089562011023257261)
      ·
        refine ⟨1919056908585754133721473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5117485089562011023257261 1919056908585754133721473)
        ·
          refine ⟨1439292681439315600291105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1919056908585754133721473 1439292681439315600291105)
          ·
            refine ⟨1079469511079486700218329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1439292681439315600291105 1079469511079486700218329)
            ·
              refine ⟨809602133309615025163747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1079469511079486700218329 809602133309615025163747)
              ·
                refine ⟨1214403199964422537745621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 809602133309615025163747 1214403199964422537745621)
                ·
                  refine ⟨28462574999166153228413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1214403199964422537745621 28462574999166153228413)
                  ·
                    rfl

theorem cell23_498876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 7].length) (baseStart_498876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498876 prefixEnd_498876 := by exact prefixLift 498876
  have htrace : WordTrace (prefixWord ++ tailWord_498876) baseStart_498876 baseEnd_498876 := by
    simpa [prefixWord, tailWord_498876, baseEnd_498876] using wordTrace_append hprefix tailTrace_498876
  have hstable : (prefixWord ++ tailWord_498876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498876).length < 2 ^ (prefixWord ++ tailWord_498876).sum := by decide
  have hdescent : baseEnd_498876 < baseStart_498876 := by decide
  rcases family_descends (prefixWord ++ tailWord_498876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498926 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 4, 1, 4]
def baseStart_498926 : Nat := 118140960795 + 498926 * 2 ^ 59
def prefixEnd_498926 : Nat := 4983230072969 + 3 ^ 40 * 498926 * 2
def baseEnd_498926 : Nat := 256188849025220183430487

theorem tailTrace_498926 : CollatzResearch.WordTrace tailWord_498926 prefixEnd_498926 256188849025220183430487 := by
  unfold tailWord_498926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2274665773810473327751579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12131550793655857748008421 2274665773810473327751579)
  ·
    refine ⟨3411998660715709991627369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2274665773810473327751579 3411998660715709991627369)
    ·
      refine ⟨2558998995536782493720527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3411998660715709991627369 2558998995536782493720527)
      ·
        refine ⟨3838498493305173740580791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2558998995536782493720527 3838498493305173740580791)
        ·
          refine ⟨5757747739957760610871187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3838498493305173740580791 5757747739957760610871187)
          ·
            refine ⟨8636621609936640916306781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5757747739957760610871187 8636621609936640916306781)
            ·
              refine ⟨3238733103726240343615043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8636621609936640916306781 3238733103726240343615043)
              ·
                refine ⟨4858099655589360515422565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3238733103726240343615043 4858099655589360515422565)
                ·
                  refine ⟨910893685423005096641731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4858099655589360515422565 910893685423005096641731)
                  ·
                    refine ⟨1366340528134507644962597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 910893685423005096641731 1366340528134507644962597)
                    ·
                      refine ⟨256188849025220183430487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1366340528134507644962597 256188849025220183430487)
                      ·
                        rfl

theorem cell23_498926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_498926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_498926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_498926 prefixEnd_498926 := by exact prefixLift 498926
  have htrace : WordTrace (prefixWord ++ tailWord_498926) baseStart_498926 baseEnd_498926 := by
    simpa [prefixWord, tailWord_498926, baseEnd_498926] using wordTrace_append hprefix tailTrace_498926
  have hstable : (prefixWord ++ tailWord_498926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498926).length < 2 ^ (prefixWord ++ tailWord_498926).sum := by decide
  have hdescent : baseEnd_498926 < baseStart_498926 := by decide
  rcases family_descends (prefixWord ++ tailWord_498926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499006 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 2, 1, 7]
def baseStart_499006 : Nat := 118140960795 + 499006 * 2 ^ 59
def prefixEnd_499006 : Nat := 4983230072969 + 3 ^ 40 * 499006 * 2
def baseEnd_499006 : Nat := 256229927477579870430119

theorem tailTrace_499006 : CollatzResearch.WordTrace tailWord_499006 prefixEnd_499006 256229927477579870430119 := by
  unfold tailWord_499006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2275030503774245035615609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12133496020129306856616581 2275030503774245035615609)
  ·
    refine ⟨1706272877830683776711707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2275030503774245035615609 1706272877830683776711707)
    ·
      refine ⟨2559409316746025665067561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1706272877830683776711707 2559409316746025665067561)
      ·
        refine ⟨1919556987559519248800671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2559409316746025665067561 1919556987559519248800671)
        ·
          refine ⟨2879335481339278873201007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1919556987559519248800671 2879335481339278873201007)
          ·
            refine ⟨4319003222008918309801511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2879335481339278873201007 4319003222008918309801511)
            ·
              refine ⟨6478504833013377464702267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4319003222008918309801511 6478504833013377464702267)
              ·
                refine ⟨9717757249520066197053401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6478504833013377464702267 9717757249520066197053401)
                ·
                  refine ⟨7288317937140049647790051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9717757249520066197053401 7288317937140049647790051)
                  ·
                    refine ⟨10932476905710074471685077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7288317937140049647790051 10932476905710074471685077)
                    ·
                      refine ⟨256229927477579870430119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 10932476905710074471685077 256229927477579870430119)
                      ·
                        rfl

theorem cell23_499006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_499006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499006 prefixEnd_499006 := by exact prefixLift 499006
  have htrace : WordTrace (prefixWord ++ tailWord_499006) baseStart_499006 baseEnd_499006 := by
    simpa [prefixWord, tailWord_499006, baseEnd_499006] using wordTrace_append hprefix tailTrace_499006
  have hstable : (prefixWord ++ tailWord_499006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499006).length < 2 ^ (prefixWord ++ tailWord_499006).sum := by decide
  have hdescent : baseEnd_499006 < baseStart_499006 := by decide
  rcases family_descends (prefixWord ++ tailWord_499006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499020 : List Nat := [2, 2, 1, 3, 2, 2, 3, 1, 2, 3, 2]
def baseStart_499020 : Nat := 118140960795 + 499020 * 2 ^ 59
def prefixEnd_499020 : Nat := 4983230072969 + 3 ^ 40 * 499020 * 2
def baseEnd_499020 : Nat := 256237116206742815655055

theorem tailTrace_499020 : CollatzResearch.WordTrace tailWord_499020 prefixEnd_499020 256237116206742815655055 := by
  unfold tailWord_499020
  simp only [CollatzResearch.WordTrace]
  refine ⟨9100377326071620337967257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12133836434762160450623009 9100377326071620337967257)
  ·
    refine ⟨6825282994553715253475443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9100377326071620337967257 6825282994553715253475443)
    ·
      refine ⟨10237924491830572880213165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6825282994553715253475443 10237924491830572880213165)
      ·
        refine ⟨3839221684436464830079937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10237924491830572880213165 3839221684436464830079937)
        ·
          refine ⟨2879416263327348622559953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3839221684436464830079937 2879416263327348622559953)
          ·
            refine ⟨2159562197495511466919965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2879416263327348622559953 2159562197495511466919965)
            ·
              refine ⟨809835824060816800094987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2159562197495511466919965 809835824060816800094987)
              ·
                refine ⟨1214753736091225200142481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 809835824060816800094987 1214753736091225200142481)
                ·
                  refine ⟨911065302068418900106861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1214753736091225200142481 911065302068418900106861)
                  ·
                    refine ⟨341649488275657087540073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 911065302068418900106861 341649488275657087540073)
                    ·
                      refine ⟨256237116206742815655055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 341649488275657087540073 256237116206742815655055)
                      ·
                        rfl

theorem cell23_499020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_499020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499020 prefixEnd_499020 := by exact prefixLift 499020
  have htrace : WordTrace (prefixWord ++ tailWord_499020) baseStart_499020 baseEnd_499020 := by
    simpa [prefixWord, tailWord_499020, baseEnd_499020] using wordTrace_append hprefix tailTrace_499020
  have hstable : (prefixWord ++ tailWord_499020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499020).length < 2 ^ (prefixWord ++ tailWord_499020).sum := by decide
  have hdescent : baseEnd_499020 < baseStart_499020 := by decide
  rcases family_descends (prefixWord ++ tailWord_499020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499043 : List Nat := [1, 1, 1, 5, 2, 3, 1, 1, 4, 4]
def baseStart_499043 : Nat := 118140960795 + 499043 * 2 ^ 59
def prefixEnd_499043 : Nat := 4983230072969 + 3 ^ 40 * 499043 * 2
def baseEnd_499043 : Nat := 85416308753932075222483

theorem tailTrace_499043 : CollatzResearch.WordTrace tailWord_499043 prefixEnd_499043 85416308753932075222483 := by
  unfold tailWord_499043
  simp only [CollatzResearch.WordTrace]
  refine ⟨18201593531059915604021783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12134395687373277069347855 18201593531059915604021783)
  ·
    refine ⟨27302390296589873406032675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18201593531059915604021783 27302390296589873406032675)
    ·
      refine ⟨40953585444884810109049013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27302390296589873406032675 40953585444884810109049013)
      ·
        refine ⟨3839398635457950947723345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40953585444884810109049013 3839398635457950947723345)
        ·
          refine ⟨2879548976593463210792509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3839398635457950947723345 2879548976593463210792509)
          ·
            refine ⟨1079830866222548704047191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2879548976593463210792509 1079830866222548704047191)
            ·
              refine ⟨1619746299333823056070787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1079830866222548704047191 1619746299333823056070787)
              ·
                refine ⟨2429619449000734584106181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1619746299333823056070787 2429619449000734584106181)
                ·
                  refine ⟨455553646687637734519909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2429619449000734584106181 455553646687637734519909)
                  ·
                    refine ⟨85416308753932075222483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 455553646687637734519909 85416308753932075222483)
                    ·
                      rfl

theorem cell23_499043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 4, 4].length) (baseStart_499043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499043 prefixEnd_499043 := by exact prefixLift 499043
  have htrace : WordTrace (prefixWord ++ tailWord_499043) baseStart_499043 baseEnd_499043 := by
    simpa [prefixWord, tailWord_499043, baseEnd_499043] using wordTrace_append hprefix tailTrace_499043
  have hstable : (prefixWord ++ tailWord_499043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499043).length < 2 ^ (prefixWord ++ tailWord_499043).sum := by decide
  have hdescent : baseEnd_499043 < baseStart_499043 := by decide
  rcases family_descends (prefixWord ++ tailWord_499043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
