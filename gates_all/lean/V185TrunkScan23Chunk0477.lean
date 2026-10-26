import V185TrunkScan23Chunk0476

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2821118 : List Nat := [4, 2, 2, 2, 2, 2, 2, 1, 1, 5]
def baseStart_2821118 : Nat := 118140960795 + 2821118 * 2 ^ 59
def prefixEnd_2821118 : Nat := 4983230072969 + 3 ^ 40 * 2821118 * 2
def baseEnd_2821118 : Nat := 482863172350266198850307

theorem tailTrace_2821118 : CollatzResearch.WordTrace tailWord_2821118 prefixEnd_2821118 482863172350266198850307 := by
  unfold tailWord_2821118
  simp only [CollatzResearch.WordTrace]
  refine ⟨12861828324197346180096001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68596417729052512960512005 12861828324197346180096001)
  ·
    refine ⟨9646371243148009635072001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12861828324197346180096001 9646371243148009635072001)
    ·
      refine ⟨7234778432361007226304001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9646371243148009635072001 7234778432361007226304001)
      ·
        refine ⟨5426083824270755419728001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7234778432361007226304001 5426083824270755419728001)
        ·
          refine ⟨4069562868203066564796001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5426083824270755419728001 4069562868203066564796001)
          ·
            refine ⟨3052172151152299923597001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4069562868203066564796001 3052172151152299923597001)
            ·
              refine ⟨2289129113364224942697751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3052172151152299923597001 2289129113364224942697751)
              ·
                refine ⟨3433693670046337414046627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2289129113364224942697751 3433693670046337414046627)
                ·
                  refine ⟨5150540505069506121069941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3433693670046337414046627 5150540505069506121069941)
                  ·
                    refine ⟨482863172350266198850307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5150540505069506121069941 482863172350266198850307)
                    ·
                      rfl

theorem cell23_2821118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_2821118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821118 prefixEnd_2821118 := by exact prefixLift 2821118
  have htrace : WordTrace (prefixWord ++ tailWord_2821118) baseStart_2821118 baseEnd_2821118 := by
    simpa [prefixWord, tailWord_2821118, baseEnd_2821118] using wordTrace_append hprefix tailTrace_2821118
  have hstable : (prefixWord ++ tailWord_2821118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821118).length < 2 ^ (prefixWord ++ tailWord_2821118).sum := by decide
  have hdescent : baseEnd_2821118 < baseStart_2821118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821120 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 3]
def baseStart_2821120 : Nat := 118140960795 + 2821120 * 2 ^ 59
def prefixEnd_2821120 : Nat := 4983230072969 + 3 ^ 40 * 2821120 * 2
def baseEnd_2821120 : Nat := 1448590544012107588725911

theorem tailTrace_2821120 : CollatzResearch.WordTrace tailWord_2821120 prefixEnd_2821120 1448590544012107588725911 := by
  unfold tailWord_2821120
  simp only [CollatzResearch.WordTrace]
  refine ⟨51447349769785761891170407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68596466359714349188227209 51447349769785761891170407)
  ·
    refine ⟨77171024654678642836755611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51447349769785761891170407 77171024654678642836755611)
    ·
      refine ⟨115756536982017964255133417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77171024654678642836755611 115756536982017964255133417)
      ·
        refine ⟨86817402736513473191350063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115756536982017964255133417 86817402736513473191350063)
        ·
          refine ⟨130226104104770209787025095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86817402736513473191350063 130226104104770209787025095)
          ·
            refine ⟨195339156157155314680537643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130226104104770209787025095 195339156157155314680537643)
            ·
              refine ⟨293008734235732972020806465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195339156157155314680537643 293008734235732972020806465)
              ·
                refine ⟨219756550676799729015604849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 293008734235732972020806465 219756550676799729015604849)
                ·
                  refine ⟨164817413007599796761703637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219756550676799729015604849 164817413007599796761703637)
                  ·
                    refine ⟨3862908117365620236602429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 164817413007599796761703637 3862908117365620236602429)
                    ·
                      refine ⟨1448590544012107588725911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3862908117365620236602429 1448590544012107588725911)
                      ·
                        rfl

theorem cell23_2821120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 3].length) (baseStart_2821120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821120 prefixEnd_2821120 := by exact prefixLift 2821120
  have htrace : WordTrace (prefixWord ++ tailWord_2821120) baseStart_2821120 baseEnd_2821120 := by
    simpa [prefixWord, tailWord_2821120, baseEnd_2821120] using wordTrace_append hprefix tailTrace_2821120
  have hstable : (prefixWord ++ tailWord_2821120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821120).length < 2 ^ (prefixWord ++ tailWord_2821120).sum := by decide
  have hdescent : baseEnd_2821120 < baseStart_2821120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821121 : List Nat := [1, 2, 4, 1, 2, 4, 2, 1, 1, 1, 4]
def baseStart_2821121 : Nat := 118140960795 + 2821121 * 2 ^ 59
def prefixEnd_2821121 : Nat := 4983230072969 + 3 ^ 40 * 2821121 * 2
def baseEnd_2821121 : Nat := 1448591057492762084813407

theorem tailTrace_2821121 : CollatzResearch.WordTrace tailWord_2821121 prefixEnd_2821121 1448591057492762084813407 := by
  unfold tailWord_2821121
  simp only [CollatzResearch.WordTrace]
  refine ⟨102894736012567900953127217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68596490675045267302084811 102894736012567900953127217)
  ·
    refine ⟨77171052009425925714845413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102894736012567900953127217 77171052009425925714845413)
    ·
      refine ⟨14469572251767361071533515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77171052009425925714845413 14469572251767361071533515)
      ·
        refine ⟨21704358377651041607300273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14469572251767361071533515 21704358377651041607300273)
        ·
          refine ⟨16278268783238281205475205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21704358377651041607300273 16278268783238281205475205)
          ·
            refine ⟨3052175396857177726026601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16278268783238281205475205 3052175396857177726026601)
            ·
              refine ⟨2289131547642883294519951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3052175396857177726026601 2289131547642883294519951)
              ·
                refine ⟨3433697321464324941779927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2289131547642883294519951 3433697321464324941779927)
                ·
                  refine ⟨5150545982196487412669891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3433697321464324941779927 5150545982196487412669891)
                  ·
                    refine ⟨7725818973294731119004837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5150545982196487412669891 7725818973294731119004837)
                    ·
                      refine ⟨1448591057492762084813407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7725818973294731119004837 1448591057492762084813407)
                      ·
                        rfl

theorem cell23_2821121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_2821121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821121 prefixEnd_2821121 := by exact prefixLift 2821121
  have htrace : WordTrace (prefixWord ++ tailWord_2821121) baseStart_2821121 baseEnd_2821121 := by
    simpa [prefixWord, tailWord_2821121, baseEnd_2821121] using wordTrace_append hprefix tailTrace_2821121
  have hstable : (prefixWord ++ tailWord_2821121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821121).length < 2 ^ (prefixWord ++ tailWord_2821121).sum := by decide
  have hdescent : baseEnd_2821121 < baseStart_2821121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821154 : List Nat := [3, 3, 1, 1, 1, 3, 3, 1, 1, 3, 3]
def baseStart_2821154 : Nat := 118140960795 + 2821154 * 2 ^ 59
def prefixEnd_2821154 : Nat := 4983230072969 + 3 ^ 40 * 2821154 * 2
def baseEnd_2821154 : Nat := 1448608002354360455700755

theorem tailTrace_2821154 : CollatzResearch.WordTrace tailWord_2821154 prefixEnd_2821154 1448608002354360455700755 := by
  unfold tailWord_2821154
  simp only [CollatzResearch.WordTrace]
  refine ⟨25723984905362086897269629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68597293080965565059385677 25723984905362086897269629)
  ·
    refine ⟨9646494339510782586476111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25723984905362086897269629 9646494339510782586476111)
    ·
      refine ⟨14469741509266173879714167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9646494339510782586476111 14469741509266173879714167)
      ·
        refine ⟨21704612263899260819571251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14469741509266173879714167 21704612263899260819571251)
        ·
          refine ⟨32556918395848891229356877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21704612263899260819571251 32556918395848891229356877)
          ·
            refine ⟨12208844398443334211008829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32556918395848891229356877 12208844398443334211008829)
            ·
              refine ⟨4578316649416250329128311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12208844398443334211008829 4578316649416250329128311)
              ·
                refine ⟨6867474974124375493692467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4578316649416250329128311 6867474974124375493692467)
                ·
                  refine ⟨10301212461186563240538701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6867474974124375493692467 10301212461186563240538701)
                  ·
                    refine ⟨3862954672944961215202013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10301212461186563240538701 3862954672944961215202013)
                    ·
                      refine ⟨1448608002354360455700755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3862954672944961215202013 1448608002354360455700755)
                      ·
                        rfl

theorem cell23_2821154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_2821154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821154 prefixEnd_2821154 := by exact prefixLift 2821154
  have htrace : WordTrace (prefixWord ++ tailWord_2821154) baseStart_2821154 baseEnd_2821154 := by
    simpa [prefixWord, tailWord_2821154, baseEnd_2821154] using wordTrace_append hprefix tailTrace_2821154
  have hstable : (prefixWord ++ tailWord_2821154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821154).length < 2 ^ (prefixWord ++ tailWord_2821154).sum := by decide
  have hdescent : baseEnd_2821154 < baseStart_2821154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821172 : List Nat := [2, 5, 1, 2, 1, 3, 1, 3, 1, 2, 2]
def baseStart_2821172 : Nat := 118140960795 + 2821172 * 2 ^ 59
def prefixEnd_2821172 : Nat := 4983230072969 + 3 ^ 40 * 2821172 * 2
def baseEnd_2821172 : Nat := 1448617245006141385275673

theorem tailTrace_2821172 : CollatzResearch.WordTrace tailWord_2821172 prefixEnd_2821172 1448617245006141385275673 := by
  unfold tailWord_2821172
  simp only [CollatzResearch.WordTrace]
  refine ⟨51448298067691568331616885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68597730756922091108822513 51448298067691568331616885)
  ·
    refine ⟨4823277943846084531089083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51448298067691568331616885 4823277943846084531089083)
    ·
      refine ⟨7234916915769126796633625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4823277943846084531089083 7234916915769126796633625)
      ·
        refine ⟨5426187686826845097475219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7234916915769126796633625 5426187686826845097475219)
        ·
          refine ⟨8139281530240267646212829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5426187686826845097475219 8139281530240267646212829)
          ·
            refine ⟨3052230573840100367329811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8139281530240267646212829 3052230573840100367329811)
            ·
              refine ⟨4578345860760150550994717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3052230573840100367329811 4578345860760150550994717)
              ·
                refine ⟨1716879697785056456623019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4578345860760150550994717 1716879697785056456623019)
                ·
                  refine ⟨2575319546677584684934529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1716879697785056456623019 2575319546677584684934529)
                  ·
                    refine ⟨1931489660008188513700897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2575319546677584684934529 1931489660008188513700897)
                    ·
                      refine ⟨1448617245006141385275673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1931489660008188513700897 1448617245006141385275673)
                      ·
                        rfl

theorem cell23_2821172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_2821172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821172 prefixEnd_2821172 := by exact prefixLift 2821172
  have htrace : WordTrace (prefixWord ++ tailWord_2821172) baseStart_2821172 baseEnd_2821172 := by
    simpa [prefixWord, tailWord_2821172, baseEnd_2821172] using wordTrace_append hprefix tailTrace_2821172
  have hstable : (prefixWord ++ tailWord_2821172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821172).length < 2 ^ (prefixWord ++ tailWord_2821172).sum := by decide
  have hdescent : baseEnd_2821172 < baseStart_2821172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821181 : List Nat := [1, 4, 1, 3, 1, 2, 2, 3, 1, 3, 2]
def baseStart_2821181 : Nat := 118140960795 + 2821181 * 2 ^ 59
def prefixEnd_2821181 : Nat := 4983230072969 + 3 ^ 40 * 2821181 * 2
def baseEnd_2821181 : Nat := 1448621866332031850063131

theorem tailTrace_2821181 : CollatzResearch.WordTrace tailWord_2821181 prefixEnd_2821181 1448621866332031850063131 := by
  unfold tailWord_2821181
  simp only [CollatzResearch.WordTrace]
  refine ⟨102896924392350531200311397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68597949594900354133540931 102896924392350531200311397)
  ·
    refine ⟨19293173323565724600058387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102896924392350531200311397 19293173323565724600058387)
    ·
      refine ⟨28939759985348586900087581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19293173323565724600058387 28939759985348586900087581)
      ·
        refine ⟨10852409994505720087532843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28939759985348586900087581 10852409994505720087532843)
        ·
          refine ⟨16278614991758580131299265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10852409994505720087532843 16278614991758580131299265)
          ·
            refine ⟨12208961243818935098474449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16278614991758580131299265 12208961243818935098474449)
            ·
              refine ⟨9156720932864201323855837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12208961243818935098474449 9156720932864201323855837)
              ·
                refine ⟨3433770349824075496445939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9156720932864201323855837 3433770349824075496445939)
                ·
                  refine ⟨5150655524736113244668909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3433770349824075496445939 5150655524736113244668909)
                  ·
                    refine ⟨1931495821776042466750841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5150655524736113244668909 1931495821776042466750841)
                    ·
                      refine ⟨1448621866332031850063131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1931495821776042466750841 1448621866332031850063131)
                      ·
                        rfl

theorem cell23_2821181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_2821181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821181 prefixEnd_2821181 := by exact prefixLift 2821181
  have htrace : WordTrace (prefixWord ++ tailWord_2821181) baseStart_2821181 baseEnd_2821181 := by
    simpa [prefixWord, tailWord_2821181, baseEnd_2821181] using wordTrace_append hprefix tailTrace_2821181
  have hstable : (prefixWord ++ tailWord_2821181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821181).length < 2 ^ (prefixWord ++ tailWord_2821181).sum := by decide
  have hdescent : baseEnd_2821181 < baseStart_2821181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821234 : List Nat := [3, 2, 1, 2, 2, 1, 2, 5, 5]
def baseStart_2821234 : Nat := 118140960795 + 2821234 * 2 ^ 59
def prefixEnd_2821234 : Nat := 4983230072969 + 3 ^ 40 * 2821234 * 2
def baseEnd_2821234 : Nat := 160961008978524460300043

theorem tailTrace_2821234 : CollatzResearch.WordTrace tailWord_2821234 prefixEnd_2821234 160961008978524460300043 := by
  unfold tailWord_2821234
  simp only [CollatzResearch.WordTrace]
  refine ⟨25724714365289630312997689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68599238307439014167993837 25724714365289630312997689)
  ·
    refine ⟨19293535773967222734748267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25724714365289630312997689 19293535773967222734748267)
    ·
      refine ⟨28940303660950834102122401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19293535773967222734748267 28940303660950834102122401)
      ·
        refine ⟨21705227745713125576591801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28940303660950834102122401 21705227745713125576591801)
        ·
          refine ⟨16278920809284844182443851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21705227745713125576591801 16278920809284844182443851)
          ·
            refine ⟨24418381213927266273665777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16278920809284844182443851 24418381213927266273665777)
            ·
              refine ⟨18313785910445449705249333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24418381213927266273665777 18313785910445449705249333)
              ·
                refine ⟨1716917429104260909867125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18313785910445449705249333 1716917429104260909867125)
                ·
                  refine ⟨160961008978524460300043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1716917429104260909867125 160961008978524460300043)
                  ·
                    rfl

theorem cell23_2821234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 5, 5].length) (baseStart_2821234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821234 prefixEnd_2821234 := by exact prefixLift 2821234
  have htrace : WordTrace (prefixWord ++ tailWord_2821234) baseStart_2821234 baseEnd_2821234 := by
    simpa [prefixWord, tailWord_2821234, baseEnd_2821234] using wordTrace_append hprefix tailTrace_2821234
  have hstable : (prefixWord ++ tailWord_2821234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821234).length < 2 ^ (prefixWord ++ tailWord_2821234).sum := by decide
  have hdescent : baseEnd_2821234 < baseStart_2821234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821257 : List Nat := [1, 2, 1, 1, 4, 3, 2, 1, 1, 2, 5]
def baseStart_2821257 : Nat := 118140960795 + 2821257 * 2 ^ 59
def prefixEnd_2821257 : Nat := 4983230072969 + 3 ^ 40 * 2821257 * 2
def baseEnd_2821257 : Nat := 1448660890861773552712781

theorem tailTrace_2821257 : CollatzResearch.WordTrace tailWord_2821257 prefixEnd_2821257 1448660890861773552712781 := by
  unfold tailWord_2821257
  simp only [CollatzResearch.WordTrace]
  refine ⟨102899696340075196180078025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68599797560050130786718683 102899696340075196180078025)
  ·
    refine ⟨77174772255056397135058519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102899696340075196180078025 77174772255056397135058519)
    ·
      refine ⟨115762158382584595702587779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77174772255056397135058519 115762158382584595702587779)
      ·
        refine ⟨173643237573876893553881669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115762158382584595702587779 173643237573876893553881669)
        ·
          refine ⟨32558107045101917541352813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173643237573876893553881669 32558107045101917541352813)
          ·
            refine ⟨12209290141913219078007305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32558107045101917541352813 12209290141913219078007305)
            ·
              refine ⟨9156967606434914308505479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12209290141913219078007305 9156967606434914308505479)
              ·
                refine ⟨13735451409652371462758219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9156967606434914308505479 13735451409652371462758219)
                ·
                  refine ⟨20603177114478557194137329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13735451409652371462758219 20603177114478557194137329)
                  ·
                    refine ⟨15452382835858917895602997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20603177114478557194137329 15452382835858917895602997)
                    ·
                      refine ⟨1448660890861773552712781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15452382835858917895602997 1448660890861773552712781)
                      ·
                        rfl

theorem cell23_2821257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 2, 5].length) (baseStart_2821257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821257 prefixEnd_2821257 := by exact prefixLift 2821257
  have htrace : WordTrace (prefixWord ++ tailWord_2821257) baseStart_2821257 baseEnd_2821257 := by
    simpa [prefixWord, tailWord_2821257, baseEnd_2821257] using wordTrace_append hprefix tailTrace_2821257
  have hstable : (prefixWord ++ tailWord_2821257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821257).length < 2 ^ (prefixWord ++ tailWord_2821257).sum := by decide
  have hdescent : baseEnd_2821257 < baseStart_2821257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821267 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 4]
def baseStart_2821267 : Nat := 118140960795 + 2821267 * 2 ^ 59
def prefixEnd_2821267 : Nat := 4983230072969 + 3 ^ 40 * 2821267 * 2
def baseEnd_2821267 : Nat := 1448666025668318513587735

theorem tailTrace_2821267 : CollatzResearch.WordTrace tailWord_2821267 prefixEnd_2821267 1448666025668318513587735 := by
  unfold tailWord_2821267
  simp only [CollatzResearch.WordTrace]
  refine ⟨102900061070038967887942055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68600040713359311925294703 102900061070038967887942055)
  ·
    refine ⟨154350091605058451831913083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102900061070038967887942055 154350091605058451831913083)
    ·
      refine ⟨231525137407587677747869625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154350091605058451831913083 231525137407587677747869625)
      ·
        refine ⟨173643853055690758310902219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231525137407587677747869625 173643853055690758310902219)
        ·
          refine ⟨260465779583536137466353329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173643853055690758310902219 260465779583536137466353329)
          ·
            refine ⟨195349334687652103099764997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260465779583536137466353329 195349334687652103099764997)
            ·
              refine ⟨36628000253934769331205937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 195349334687652103099764997 36628000253934769331205937)
              ·
                refine ⟨27471000190451076998404453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36628000253934769331205937 27471000190451076998404453)
                ·
                  refine ⟨5150812535709576937200835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27471000190451076998404453 5150812535709576937200835)
                  ·
                    refine ⟨7726218803564365405801253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5150812535709576937200835 7726218803564365405801253)
                    ·
                      refine ⟨1448666025668318513587735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7726218803564365405801253 1448666025668318513587735)
                      ·
                        rfl

theorem cell23_2821267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 4].length) (baseStart_2821267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821267 prefixEnd_2821267 := by exact prefixLift 2821267
  have htrace : WordTrace (prefixWord ++ tailWord_2821267) baseStart_2821267 baseEnd_2821267 := by
    simpa [prefixWord, tailWord_2821267, baseEnd_2821267] using wordTrace_append hprefix tailTrace_2821267
  have hstable : (prefixWord ++ tailWord_2821267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821267).length < 2 ^ (prefixWord ++ tailWord_2821267).sum := by decide
  have hdescent : baseEnd_2821267 < baseStart_2821267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821284 : List Nat := [2, 3, 1, 2, 3, 2, 1, 1, 1, 3, 4]
def baseStart_2821284 : Nat := 118140960795 + 2821284 * 2 ^ 59
def prefixEnd_2821284 : Nat := 4983230072969 + 3 ^ 40 * 2821284 * 2
def baseEnd_2821284 : Nat := 1448674754839444947075157

theorem tailTrace_2821284 : CollatzResearch.WordTrace tailWord_2821284 prefixEnd_2821284 1448674754839444947075157 := by
  unfold tailWord_2821284
  simp only [CollatzResearch.WordTrace]
  refine ⟨51450340555488689895655453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68600454073984919860873937 51450340555488689895655453)
  ·
    refine ⟨19293877708308258710870795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51450340555488689895655453 19293877708308258710870795)
    ·
      refine ⟨28940816562462388066306193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19293877708308258710870795 28940816562462388066306193)
      ·
        refine ⟨21705612421846791049729645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28940816562462388066306193 21705612421846791049729645)
        ·
          refine ⟨8139604658192546643648617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21705612421846791049729645 8139604658192546643648617)
          ·
            refine ⟨6104703493644409982736463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8139604658192546643648617 6104703493644409982736463)
            ·
              refine ⟨9157055240466614974104695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6104703493644409982736463 9157055240466614974104695)
              ·
                refine ⟨13735582860699922461157043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9157055240466614974104695 13735582860699922461157043)
                ·
                  refine ⟨20603374291049883691735565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13735582860699922461157043 20603374291049883691735565)
                  ·
                    refine ⟨7726265359143706384400837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20603374291049883691735565 7726265359143706384400837)
                    ·
                      refine ⟨1448674754839444947075157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7726265359143706384400837 1448674754839444947075157)
                      ·
                        rfl

theorem cell23_2821284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_2821284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821284 prefixEnd_2821284 := by exact prefixLift 2821284
  have htrace : WordTrace (prefixWord ++ tailWord_2821284) baseStart_2821284 baseEnd_2821284 := by
    simpa [prefixWord, tailWord_2821284, baseEnd_2821284] using wordTrace_append hprefix tailTrace_2821284
  have hstable : (prefixWord ++ tailWord_2821284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821284).length < 2 ^ (prefixWord ++ tailWord_2821284).sum := by decide
  have hdescent : baseEnd_2821284 < baseStart_2821284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821307 : List Nat := [1, 1, 1, 1, 1, 2, 4, 6, 6]
def baseStart_2821307 : Nat := 118140960795 + 2821307 * 2 ^ 59
def prefixEnd_2821307 : Nat := 4983230072969 + 3 ^ 40 * 2821307 * 2
def baseEnd_2821307 : Nat := 160965173877166484120839

theorem tailTrace_2821307 : CollatzResearch.WordTrace tailWord_2821307 prefixEnd_2821307 160965173877166484120839 := by
  unfold tailWord_2821307
  simp only [CollatzResearch.WordTrace]
  refine ⟨102901519989894054719398175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68601013326596036479598783 102901519989894054719398175)
  ·
    refine ⟨154352279984841082079097263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102901519989894054719398175 154352279984841082079097263)
    ·
      refine ⟨231528419977261623118645895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154352279984841082079097263 231528419977261623118645895)
      ·
        refine ⟨347292629965892434677968843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231528419977261623118645895 347292629965892434677968843)
        ·
          refine ⟨520938944948838652016953265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347292629965892434677968843 520938944948838652016953265)
          ·
            refine ⟨390704208711628989012714949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 520938944948838652016953265 390704208711628989012714949)
            ·
              refine ⟨73257039133430435439884053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 390704208711628989012714949 73257039133430435439884053)
              ·
                refine ⟨3433923709379551661244565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73257039133430435439884053 3433923709379551661244565)
                ·
                  refine ⟨160965173877166484120839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3433923709379551661244565 160965173877166484120839)
                  ·
                    rfl

theorem cell23_2821307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 6, 6].length) (baseStart_2821307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821307 prefixEnd_2821307 := by exact prefixLift 2821307
  have htrace : WordTrace (prefixWord ++ tailWord_2821307) baseStart_2821307 baseEnd_2821307 := by
    simpa [prefixWord, tailWord_2821307, baseEnd_2821307] using wordTrace_append hprefix tailTrace_2821307
  have hstable : (prefixWord ++ tailWord_2821307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821307).length < 2 ^ (prefixWord ++ tailWord_2821307).sum := by decide
  have hdescent : baseEnd_2821307 < baseStart_2821307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821311 : List Nat := [1, 1, 2, 2, 2, 2, 4, 4, 1, 4]
def baseStart_2821311 : Nat := 118140960795 + 2821311 * 2 ^ 59
def prefixEnd_2821311 : Nat := 4983230072969 + 3 ^ 40 * 2821311 * 2
def baseEnd_2821311 : Nat := 482896206272372113812511

theorem tailTrace_2821311 : CollatzResearch.WordTrace tailWord_2821311 prefixEnd_2821311 482896206272372113812511 := by
  unfold tailWord_2821311
  simp only [CollatzResearch.WordTrace]
  refine ⟨102901665881879563402543787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68601110587919708935029191 102901665881879563402543787)
  ·
    refine ⟨154352498822819345103815681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102901665881879563402543787 154352498822819345103815681)
    ·
      refine ⟨115764374117114508827861761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154352498822819345103815681 115764374117114508827861761)
      ·
        refine ⟨86823280587835881620896321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115764374117114508827861761 86823280587835881620896321)
        ·
          refine ⟨65117460440876911215672241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86823280587835881620896321 65117460440876911215672241)
          ·
            refine ⟨48838095330657683411754181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65117460440876911215672241 48838095330657683411754181)
            ·
              refine ⟨9157142874498315639703909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48838095330657683411754181 9157142874498315639703909)
              ·
                refine ⟨1716964288968434182444483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9157142874498315639703909 1716964288968434182444483)
                ·
                  refine ⟨2575446433452651273666725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1716964288968434182444483 2575446433452651273666725)
                  ·
                    refine ⟨482896206272372113812511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2575446433452651273666725 482896206272372113812511)
                    ·
                      rfl

theorem cell23_2821311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 1, 4].length) (baseStart_2821311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821311 prefixEnd_2821311 := by exact prefixLift 2821311
  have htrace : WordTrace (prefixWord ++ tailWord_2821311) baseStart_2821311 baseEnd_2821311 := by
    simpa [prefixWord, tailWord_2821311, baseEnd_2821311] using wordTrace_append hprefix tailTrace_2821311
  have hstable : (prefixWord ++ tailWord_2821311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821311).length < 2 ^ (prefixWord ++ tailWord_2821311).sum := by decide
  have hdescent : baseEnd_2821311 < baseStart_2821311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821367 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 3, 6]
def baseStart_2821367 : Nat := 118140960795 + 2821367 * 2 ^ 59
def prefixEnd_2821367 : Nat := 4983230072969 + 3 ^ 40 * 2821367 * 2
def baseEnd_2821367 : Nat := 482905791244589374112425

theorem tailTrace_2821367 : CollatzResearch.WordTrace tailWord_2821367 prefixEnd_2821367 482905791244589374112425 := by
  unfold tailWord_2821367
  simp only [CollatzResearch.WordTrace]
  refine ⟨102903708369676684966582355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68602472246451123311054903 102903708369676684966582355)
  ·
    refine ⟨154355562554515027449873533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102903708369676684966582355 154355562554515027449873533)
    ·
      refine ⟨57883335957943135293702575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154355562554515027449873533 57883335957943135293702575)
      ·
        refine ⟨86825003936914702940553863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57883335957943135293702575 86825003936914702940553863)
        ·
          refine ⟨130237505905372054410830795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86825003936914702940553863 130237505905372054410830795)
          ·
            refine ⟨195356258858058081616246193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130237505905372054410830795 195356258858058081616246193)
            ·
              refine ⟨146517194143543561212184645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195356258858058081616246193 146517194143543561212184645)
              ·
                refine ⟨27471973901914417727284621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146517194143543561212184645 27471973901914417727284621)
                ·
                  refine ⟨10301990213217906647731733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27471973901914417727284621 10301990213217906647731733)
                  ·
                    refine ⟨482905791244589374112425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10301990213217906647731733 482905791244589374112425)
                    ·
                      rfl

theorem cell23_2821367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 6].length) (baseStart_2821367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821367 prefixEnd_2821367 := by exact prefixLift 2821367
  have htrace : WordTrace (prefixWord ++ tailWord_2821367) baseStart_2821367 baseEnd_2821367 := by
    simpa [prefixWord, tailWord_2821367, baseEnd_2821367] using wordTrace_append hprefix tailTrace_2821367
  have hstable : (prefixWord ++ tailWord_2821367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821367).length < 2 ^ (prefixWord ++ tailWord_2821367).sum := by decide
  have hdescent : baseEnd_2821367 < baseStart_2821367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821404 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 3, 2, 4]
def baseStart_2821404 : Nat := 118140960795 + 2821404 * 2 ^ 59
def prefixEnd_2821404 : Nat := 4983230072969 + 3 ^ 40 * 2821404 * 2
def baseEnd_2821404 : Nat := 1448736372517984477574605

theorem tailTrace_2821404 : CollatzResearch.WordTrace tailWord_2821404 prefixEnd_2821404 1448736372517984477574605 := by
  unfold tailWord_2821404
  simp only [CollatzResearch.WordTrace]
  refine ⟨51452528935271320142839633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68603371913695093523786177 51452528935271320142839633)
  ·
    refine ⟨38589396701453490107129725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51452528935271320142839633 38589396701453490107129725)
    ·
      refine ⟨14471023763045058790173647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38589396701453490107129725 14471023763045058790173647)
      ·
        refine ⟨21706535644567588185260471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14471023763045058790173647 21706535644567588185260471)
        ·
          refine ⟨32559803466851382277890707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21706535644567588185260471 32559803466851382277890707)
          ·
            refine ⟨48839705200277073416836061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32559803466851382277890707 48839705200277073416836061)
            ·
              refine ⟨18314889450103902531313523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48839705200277073416836061 18314889450103902531313523)
              ·
                refine ⟨27472334175155853796970285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18314889450103902531313523 27472334175155853796970285)
                ·
                  refine ⟨10302125315683445173863857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27472334175155853796970285 10302125315683445173863857)
                  ·
                    refine ⟨7726593986762583880397893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10302125315683445173863857 7726593986762583880397893)
                    ·
                      refine ⟨1448736372517984477574605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7726593986762583880397893 1448736372517984477574605)
                      ·
                        rfl

theorem cell23_2821404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_2821404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821404 prefixEnd_2821404 := by exact prefixLift 2821404
  have htrace : WordTrace (prefixWord ++ tailWord_2821404) baseStart_2821404 baseEnd_2821404 := by
    simpa [prefixWord, tailWord_2821404, baseEnd_2821404] using wordTrace_append hprefix tailTrace_2821404
  have hstable : (prefixWord ++ tailWord_2821404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821404).length < 2 ^ (prefixWord ++ tailWord_2821404).sum := by decide
  have hdescent : baseEnd_2821404 < baseStart_2821404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821411 : List Nat := [1, 1, 1, 4, 2, 5, 1, 1, 1, 1, 5]
def baseStart_2821411 : Nat := 118140960795 + 2821411 * 2 ^ 59
def prefixEnd_2821411 : Nat := 4983230072969 + 3 ^ 40 * 2821411 * 2
def baseEnd_2821411 : Nat := 1448739966882565950187073

theorem tailTrace_2821411 : CollatzResearch.WordTrace tailWord_2821411 prefixEnd_2821411 1448739966882565950187073 := by
  unfold tailWord_2821411
  simp only [CollatzResearch.WordTrace]
  refine ⟨102905313181517280481184087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68603542121011520320789391 102905313181517280481184087)
  ·
    refine ⟨154357969772275920721776131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102905313181517280481184087 154357969772275920721776131)
    ·
      refine ⟨231536954658413881082664197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154357969772275920721776131 231536954658413881082664197)
      ·
        refine ⟨43413178998452602702999537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 231536954658413881082664197 43413178998452602702999537)
        ·
          refine ⟨32559884248839452027249653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43413178998452602702999537 32559884248839452027249653)
          ·
            refine ⟨3052489148328698627554655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32559884248839452027249653 3052489148328698627554655)
            ·
              refine ⟨4578733722493047941331983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3052489148328698627554655 4578733722493047941331983)
              ·
                refine ⟨6868100583739571911997975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4578733722493047941331983 6868100583739571911997975)
                ·
                  refine ⟨10302150875609357867996963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6868100583739571911997975 10302150875609357867996963)
                  ·
                    refine ⟨15453226313414036801995445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10302150875609357867996963 15453226313414036801995445)
                    ·
                      refine ⟨1448739966882565950187073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15453226313414036801995445 1448739966882565950187073)
                      ·
                        rfl

theorem cell23_2821411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_2821411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821411 prefixEnd_2821411 := by exact prefixLift 2821411
  have htrace : WordTrace (prefixWord ++ tailWord_2821411) baseStart_2821411 baseEnd_2821411 := by
    simpa [prefixWord, tailWord_2821411, baseEnd_2821411] using wordTrace_append hprefix tailTrace_2821411
  have hstable : (prefixWord ++ tailWord_2821411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821411).length < 2 ^ (prefixWord ++ tailWord_2821411).sum := by decide
  have hdescent : baseEnd_2821411 < baseStart_2821411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821417 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 3, 4, 6]
def baseStart_2821417 : Nat := 118140960795 + 2821417 * 2 ^ 59
def prefixEnd_2821417 : Nat := 4983230072969 + 3 ^ 40 * 2821417 * 2
def baseEnd_2821417 : Nat := 1448743047766492926712045

theorem tailTrace_2821417 : CollatzResearch.WordTrace tailWord_2821417 prefixEnd_2821417 1448743047766492926712045 := by
  unfold tailWord_2821417
  simp only [CollatzResearch.WordTrace]
  refine ⟨102905532019495543505902505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68603688012997029003935003 102905532019495543505902505)
  ·
    refine ⟨77179149014621657629426879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102905532019495543505902505 77179149014621657629426879)
    ·
      refine ⟨115768723521932486444140319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77179149014621657629426879 115768723521932486444140319)
      ·
        refine ⟨173653085282898729666210479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115768723521932486444140319 173653085282898729666210479)
        ·
          refine ⟨260479627924348094499315719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173653085282898729666210479 260479627924348094499315719)
          ·
            refine ⟨390719441886522141748973579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260479627924348094499315719 390719441886522141748973579)
            ·
              refine ⟨586079162829783212623460369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 390719441886522141748973579 586079162829783212623460369)
              ·
                refine ⟨439559372122337409467595277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 586079162829783212623460369 439559372122337409467595277)
                ·
                  refine ⟨164834764545876528550348229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 439559372122337409467595277 164834764545876528550348229)
                  ·
                    refine ⟨30906518352351849103190293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 164834764545876528550348229 30906518352351849103190293)
                    ·
                      refine ⟨1448743047766492926712045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30906518352351849103190293 1448743047766492926712045)
                      ·
                        rfl

theorem cell23_2821417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 4, 6].length) (baseStart_2821417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821417 prefixEnd_2821417 := by exact prefixLift 2821417
  have htrace : WordTrace (prefixWord ++ tailWord_2821417) baseStart_2821417 baseEnd_2821417 := by
    simpa [prefixWord, tailWord_2821417, baseEnd_2821417] using wordTrace_append hprefix tailTrace_2821417
  have hstable : (prefixWord ++ tailWord_2821417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821417).length < 2 ^ (prefixWord ++ tailWord_2821417).sum := by decide
  have hdescent : baseEnd_2821417 < baseStart_2821417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821418 : List Nat := [3, 1, 4, 2, 1, 1, 1, 4, 2, 4]
def baseStart_2821418 : Nat := 118140960795 + 2821418 * 2 ^ 59
def prefixEnd_2821418 : Nat := 4983230072969 + 3 ^ 40 * 2821418 * 2
def baseEnd_2821418 : Nat := 482914520415715807599847

theorem tailTrace_2821418 : CollatzResearch.WordTrace tailWord_2821418 prefixEnd_2821418 482914520415715807599847 := by
  unfold tailWord_2821418
  simp only [CollatzResearch.WordTrace]
  refine ⟨25726392123122980169172227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68603712328327947117792605 25726392123122980169172227)
  ·
    refine ⟨38589588184684470253758341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25726392123122980169172227 38589588184684470253758341)
    ·
      refine ⟨7235547784628338172579689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38589588184684470253758341 7235547784628338172579689)
      ·
        refine ⟨5426660838471253629434767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7235547784628338172579689 5426660838471253629434767)
        ·
          refine ⟨8139991257706880444152151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5426660838471253629434767 8139991257706880444152151)
          ·
            refine ⟨12209986886560320666228227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8139991257706880444152151 12209986886560320666228227)
            ·
              refine ⟨18314980329840480999342341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12209986886560320666228227 18314980329840480999342341)
              ·
                refine ⟨3434058811845090187376689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18314980329840480999342341 3434058811845090187376689)
                ·
                  refine ⟨2575544108883817640532517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3434058811845090187376689 2575544108883817640532517)
                  ·
                    refine ⟨482914520415715807599847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2575544108883817640532517 482914520415715807599847)
                    ·
                      rfl

theorem cell23_2821418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_2821418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821418 prefixEnd_2821418 := by exact prefixLift 2821418
  have htrace : WordTrace (prefixWord ++ tailWord_2821418) baseStart_2821418 baseEnd_2821418 := by
    simpa [prefixWord, tailWord_2821418, baseEnd_2821418] using wordTrace_append hprefix tailTrace_2821418
  have hstable : (prefixWord ++ tailWord_2821418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821418).length < 2 ^ (prefixWord ++ tailWord_2821418).sum := by decide
  have hdescent : baseEnd_2821418 < baseStart_2821418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821424 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 3]
def baseStart_2821424 : Nat := 118140960795 + 2821424 * 2 ^ 59
def prefixEnd_2821424 : Nat := 4983230072969 + 3 ^ 40 * 2821424 * 2
def baseEnd_2821424 : Nat := 1448746642131074399324513

theorem tailTrace_2821424 : CollatzResearch.WordTrace tailWord_2821424 prefixEnd_2821424 1448746642131074399324513 := by
  unfold tailWord_2821424
  simp only [CollatzResearch.WordTrace]
  refine ⟨51452893665235091850703663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68603858220313455800938217 51452893665235091850703663)
  ·
    refine ⟨77179340497852637776055495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51452893665235091850703663 77179340497852637776055495)
    ·
      refine ⟨115769010746778956664083243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77179340497852637776055495 115769010746778956664083243)
      ·
        refine ⟨173653516120168434996124865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115769010746778956664083243 173653516120168434996124865)
        ·
          refine ⟨130240137090126326247093649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173653516120168434996124865 130240137090126326247093649)
          ·
            refine ⟨97680102817594744685320237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130240137090126326247093649 97680102817594744685320237)
            ·
              refine ⟨36630038556598029256995089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97680102817594744685320237 36630038556598029256995089)
              ·
                refine ⟨27472528917448521942746317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36630038556598029256995089 27472528917448521942746317)
                ·
                  refine ⟨10302198344043195728529869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27472528917448521942746317 10302198344043195728529869)
                  ·
                    refine ⟨3863324379016198398198701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10302198344043195728529869 3863324379016198398198701)
                    ·
                      refine ⟨1448746642131074399324513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3863324379016198398198701 1448746642131074399324513)
                      ·
                        rfl

theorem cell23_2821424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 3].length) (baseStart_2821424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821424 prefixEnd_2821424 := by exact prefixLift 2821424
  have htrace : WordTrace (prefixWord ++ tailWord_2821424) baseStart_2821424 baseEnd_2821424 := by
    simpa [prefixWord, tailWord_2821424, baseEnd_2821424] using wordTrace_append hprefix tailTrace_2821424
  have hstable : (prefixWord ++ tailWord_2821424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821424).length < 2 ^ (prefixWord ++ tailWord_2821424).sum := by decide
  have hdescent : baseEnd_2821424 < baseStart_2821424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821446 : List Nat := [6, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2]
def baseStart_2821446 : Nat := 118140960795 + 2821446 * 2 ^ 59
def prefixEnd_2821446 : Nat := 4983230072969 + 3 ^ 40 * 2821446 * 2
def baseEnd_2821446 : Nat := 1448757938705473313249413

theorem tailTrace_2821446 : CollatzResearch.WordTrace tailWord_2821446 prefixEnd_2821446 1448757938705473313249413 := by
  unfold tailWord_2821446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3215830929262202545584631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 68604393157593654305805461 3215830929262202545584631)
  ·
    refine ⟨4823746393893303818376947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3215830929262202545584631 4823746393893303818376947)
    ·
      refine ⟨7235619590839955727565421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4823746393893303818376947 7235619590839955727565421)
      ·
        refine ⟨2713357346564983397837033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7235619590839955727565421 2713357346564983397837033)
        ·
          refine ⟨2035018009923737548377775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2713357346564983397837033 2035018009923737548377775)
          ·
            refine ⟨3052527014885606322566663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2035018009923737548377775 3052527014885606322566663)
            ·
              refine ⟨4578790522328409483849995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3052527014885606322566663 4578790522328409483849995)
              ·
                refine ⟨6868185783492614225774993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4578790522328409483849995 6868185783492614225774993)
                ·
                  refine ⟨5151139337619460669331245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6868185783492614225774993 5151139337619460669331245)
                  ·
                    refine ⟨1931677251607297750999217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5151139337619460669331245 1931677251607297750999217)
                    ·
                      refine ⟨1448757938705473313249413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1931677251607297750999217 1448757938705473313249413)
                      ·
                        rfl

theorem cell23_2821446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_2821446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821446 prefixEnd_2821446 := by exact prefixLift 2821446
  have htrace : WordTrace (prefixWord ++ tailWord_2821446) baseStart_2821446 baseEnd_2821446 := by
    simpa [prefixWord, tailWord_2821446, baseEnd_2821446] using wordTrace_append hprefix tailTrace_2821446
  have hstable : (prefixWord ++ tailWord_2821446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821446).length < 2 ^ (prefixWord ++ tailWord_2821446).sum := by decide
  have hdescent : baseEnd_2821446 < baseStart_2821446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821454 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5]
def baseStart_2821454 : Nat := 118140960795 + 2821454 * 2 ^ 59
def prefixEnd_2821454 : Nat := 4983230072969 + 3 ^ 40 * 2821454 * 2
def baseEnd_2821454 : Nat := 1448762046550709281949375

theorem tailTrace_2821454 : CollatzResearch.WordTrace tailWord_2821454 prefixEnd_2821454 1448762046550709281949375 := by
  unfold tailWord_2821454
  simp only [CollatzResearch.WordTrace]
  refine ⟨12863360190045187353124927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68604587680240999216666277 12863360190045187353124927)
  ·
    refine ⟨19295040285067781029687391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12863360190045187353124927 19295040285067781029687391)
    ·
      refine ⟨28942560427601671544531087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19295040285067781029687391 28942560427601671544531087)
      ·
        refine ⟨43413840641402507316796631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28942560427601671544531087 43413840641402507316796631)
        ·
          refine ⟨65120760962103760975194947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43413840641402507316796631 65120760962103760975194947)
          ·
            refine ⟨97681141443155641462792421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65120760962103760975194947 97681141443155641462792421)
            ·
              refine ⟨18315214020591682774273579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97681141443155641462792421 18315214020591682774273579)
              ·
                refine ⟨27472821030887524161410369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18315214020591682774273579 27472821030887524161410369)
                ·
                  refine ⟨20604615773165643121057777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27472821030887524161410369 20604615773165643121057777)
                  ·
                    refine ⟨15453461829874232340793333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20604615773165643121057777 15453461829874232340793333)
                    ·
                      refine ⟨1448762046550709281949375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15453461829874232340793333 1448762046550709281949375)
                      ·
                        rfl

theorem cell23_2821454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_2821454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821454 prefixEnd_2821454 := by exact prefixLift 2821454
  have htrace : WordTrace (prefixWord ++ tailWord_2821454) baseStart_2821454 baseEnd_2821454 := by
    simpa [prefixWord, tailWord_2821454, baseEnd_2821454] using wordTrace_append hprefix tailTrace_2821454
  have hstable : (prefixWord ++ tailWord_2821454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821454).length < 2 ^ (prefixWord ++ tailWord_2821454).sum := by decide
  have hdescent : baseEnd_2821454 < baseStart_2821454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821469 : List Nat := [1, 4, 5, 1, 1, 2, 1, 2, 2, 4]
def baseStart_2821469 : Nat := 118140960795 + 2821469 * 2 ^ 59
def prefixEnd_2821469 : Nat := 4983230072969 + 3 ^ 40 * 2821469 * 2
def baseEnd_2821469 : Nat := 482923249586842241087269

theorem tailTrace_2821469 : CollatzResearch.WordTrace tailWord_2821469 prefixEnd_2821469 482923249586842241087269 := by
  unfold tailWord_2821469
  simp only [CollatzResearch.WordTrace]
  refine ⟨102907428615307156386795461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68604952410204770924530307 102907428615307156386795461)
  ·
    refine ⟨19295142865370091822524149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102907428615307156386795461 19295142865370091822524149)
    ·
      refine ⟨1808919643628446108361639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19295142865370091822524149 1808919643628446108361639)
      ·
        refine ⟨2713379465442669162542459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1808919643628446108361639 2713379465442669162542459)
        ·
          refine ⟨4070069198164003743813689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2713379465442669162542459 4070069198164003743813689)
          ·
            refine ⟨3052551898623002807860267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4070069198164003743813689 3052551898623002807860267)
            ·
              refine ⟨4578827847934504211790401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3052551898623002807860267 4578827847934504211790401)
              ·
                refine ⟨3434120885950878158842801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4578827847934504211790401 3434120885950878158842801)
                ·
                  refine ⟨2575590664463158619132101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3434120885950878158842801 2575590664463158619132101)
                  ·
                    refine ⟨482923249586842241087269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2575590664463158619132101 482923249586842241087269)
                    ·
                      rfl

theorem cell23_2821469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_2821469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821469 prefixEnd_2821469 := by exact prefixLift 2821469
  have htrace : WordTrace (prefixWord ++ tailWord_2821469) baseStart_2821469 baseEnd_2821469 := by
    simpa [prefixWord, tailWord_2821469, baseEnd_2821469] using wordTrace_append hprefix tailTrace_2821469
  have hstable : (prefixWord ++ tailWord_2821469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821469).length < 2 ^ (prefixWord ++ tailWord_2821469).sum := by decide
  have hdescent : baseEnd_2821469 < baseStart_2821469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821475 : List Nat := [1, 1, 1, 5, 2, 4, 1, 2, 2, 1, 3]
def baseStart_2821475 : Nat := 118140960795 + 2821475 * 2 ^ 59
def prefixEnd_2821475 : Nat := 4983230072969 + 3 ^ 40 * 2821475 * 2
def baseEnd_2821475 : Nat := 1448772829644453699786779

theorem tailTrace_2821475 : CollatzResearch.WordTrace tailWord_2821475 prefixEnd_2821475 1448772829644453699786779 := by
  unfold tailWord_2821475
  simp only [CollatzResearch.WordTrace]
  refine ⟨102907647453285419411513879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68605098302190279607675919 102907647453285419411513879)
  ·
    refine ⟨154361471179928129117270819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102907647453285419411513879 154361471179928129117270819)
    ·
      refine ⟨231542206769892193675906229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154361471179928129117270819 231542206769892193675906229)
      ·
        refine ⟨21707081884677393157116209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 231542206769892193675906229 21707081884677393157116209)
        ·
          refine ⟨16280311413508044867837157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21707081884677393157116209 16280311413508044867837157)
          ·
            refine ⟨3052558390032758412719467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16280311413508044867837157 3052558390032758412719467)
            ·
              refine ⟨4578837585049137619079201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3052558390032758412719467 4578837585049137619079201)
              ·
                refine ⟨3434128188786853214309401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4578837585049137619079201 3434128188786853214309401)
                ·
                  refine ⟨2575596141590139910732051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3434128188786853214309401 2575596141590139910732051)
                  ·
                    refine ⟨3863394212385209866098077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2575596141590139910732051 3863394212385209866098077)
                    ·
                      refine ⟨1448772829644453699786779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3863394212385209866098077 1448772829644453699786779)
                      ·
                        rfl

theorem cell23_2821475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_2821475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821475 prefixEnd_2821475 := by exact prefixLift 2821475
  have htrace : WordTrace (prefixWord ++ tailWord_2821475) baseStart_2821475 baseEnd_2821475 := by
    simpa [prefixWord, tailWord_2821475, baseEnd_2821475] using wordTrace_append hprefix tailTrace_2821475
  have hstable : (prefixWord ++ tailWord_2821475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821475).length < 2 ^ (prefixWord ++ tailWord_2821475).sum := by decide
  have hdescent : baseEnd_2821475 < baseStart_2821475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821518 : List Nat := [4, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5]
def baseStart_2821518 : Nat := 118140960795 + 2821518 * 2 ^ 59
def prefixEnd_2821518 : Nat := 4983230072969 + 3 ^ 40 * 2821518 * 2
def baseEnd_2821518 : Nat := 1448794909312597031549081

theorem tailTrace_2821518 : CollatzResearch.WordTrace tailWord_2821518 prefixEnd_2821518 1448794909312597031549081 := by
  unfold tailWord_2821518
  simp only [CollatzResearch.WordTrace]
  refine ⟨12863651974016204719416151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68606143861419758503552805 12863651974016204719416151)
  ·
    refine ⟨19295477961024307079124227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12863651974016204719416151 19295477961024307079124227)
    ·
      refine ⟨28943216941536460618686341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19295477961024307079124227 28943216941536460618686341)
      ·
        refine ⟨5426853176538086366003689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28943216941536460618686341 5426853176538086366003689)
        ·
          refine ⟨4070139882403564774502767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5426853176538086366003689 4070139882403564774502767)
          ·
            refine ⟨6105209823605347161754151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4070139882403564774502767 6105209823605347161754151)
            ·
              refine ⟨9157814735408020742631227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6105209823605347161754151 9157814735408020742631227)
              ·
                refine ⟨13736722103112031113946841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9157814735408020742631227 13736722103112031113946841)
                ·
                  refine ⟨10302541577334023335460131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13736722103112031113946841 10302541577334023335460131)
                  ·
                    refine ⟨15453812366001035003190197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10302541577334023335460131 15453812366001035003190197)
                    ·
                      refine ⟨1448794909312597031549081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15453812366001035003190197 1448794909312597031549081)
                      ·
                        rfl

theorem cell23_2821518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_2821518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821518 prefixEnd_2821518 := by exact prefixLift 2821518
  have htrace : WordTrace (prefixWord ++ tailWord_2821518) baseStart_2821518 baseEnd_2821518 := by
    simpa [prefixWord, tailWord_2821518, baseEnd_2821518] using wordTrace_append hprefix tailTrace_2821518
  have hstable : (prefixWord ++ tailWord_2821518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821518).length < 2 ^ (prefixWord ++ tailWord_2821518).sum := by decide
  have hdescent : baseEnd_2821518 < baseStart_2821518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821538 : List Nat := [3, 3, 1, 2, 1, 4, 1, 1, 7]
def baseStart_2821538 : Nat := 118140960795 + 2821538 * 2 ^ 59
def prefixEnd_2821538 : Nat := 4983230072969 + 3 ^ 40 * 2821538 * 2
def baseEnd_2821538 : Nat := 160978353213965217033221

theorem tailTrace_2821538 : CollatzResearch.WordTrace tailWord_2821538 prefixEnd_2821538 160978353213965217033221 := by
  unfold tailWord_2821538
  simp only [CollatzResearch.WordTrace]
  refine ⟨25727486313014295292764317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68606630168038120780704845 25727486313014295292764317)
  ·
    refine ⟨9647807367380360734786619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25727486313014295292764317 9647807367380360734786619)
    ·
      refine ⟨14471711051070541102179929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9647807367380360734786619 14471711051070541102179929)
      ·
        refine ⟨10853783288302905826634947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14471711051070541102179929 10853783288302905826634947)
        ·
          refine ⟨16280674932454358739952421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10853783288302905826634947 16280674932454358739952421)
          ·
            refine ⟨3052626549835192263741079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16280674932454358739952421 3052626549835192263741079)
            ·
              refine ⟨4578939824752788395611619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3052626549835192263741079 4578939824752788395611619)
              ·
                refine ⟨6868409737129182593417429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4578939824752788395611619 6868409737129182593417429)
                ·
                  refine ⟨160978353213965217033221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6868409737129182593417429 160978353213965217033221)
                  ·
                    rfl

theorem cell23_2821538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_2821538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821538 prefixEnd_2821538 := by exact prefixLift 2821538
  have htrace : WordTrace (prefixWord ++ tailWord_2821538) baseStart_2821538 baseEnd_2821538 := by
    simpa [prefixWord, tailWord_2821538, baseEnd_2821538] using wordTrace_append hprefix tailTrace_2821538
  have hstable : (prefixWord ++ tailWord_2821538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821538).length < 2 ^ (prefixWord ++ tailWord_2821538).sum := by decide
  have hdescent : baseEnd_2821538 < baseStart_2821538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821549 : List Nat := [1, 5, 2, 2, 1, 1, 4, 1, 2, 2, 2]
def baseStart_2821549 : Nat := 118140960795 + 2821549 * 2 ^ 59
def prefixEnd_2821549 : Nat := 4983230072969 + 3 ^ 40 * 2821549 * 2
def baseEnd_2821549 : Nat := 1448810827212886410261439

theorem tailTrace_2821549 : CollatzResearch.WordTrace tailWord_2821549 prefixEnd_2821549 1448810827212886410261439 := by
  unfold tailWord_2821549
  simp only [CollatzResearch.WordTrace]
  refine ⟨102910346455017330049707701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68606897636678220033138467 102910346455017330049707701)
  ·
    refine ⟨9647844980157874692160097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102910346455017330049707701 9647844980157874692160097)
    ·
      refine ⟨7235883735118406019120073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9647844980157874692160097 7235883735118406019120073)
      ·
        refine ⟨5426912801338804514340055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7235883735118406019120073 5426912801338804514340055)
        ·
          refine ⟨8140369202008206771510083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5426912801338804514340055 8140369202008206771510083)
          ·
            refine ⟨12210553803012310157265125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8140369202008206771510083 12210553803012310157265125)
            ·
              refine ⟨2289478838064808154487211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12210553803012310157265125 2289478838064808154487211)
              ·
                refine ⟨3434218257097212231730817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2289478838064808154487211 3434218257097212231730817)
                ·
                  refine ⟨2575663692822909173798113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3434218257097212231730817 2575663692822909173798113)
                  ·
                    refine ⟨1931747769617181880348585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2575663692822909173798113 1931747769617181880348585)
                    ·
                      refine ⟨1448810827212886410261439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1931747769617181880348585 1448810827212886410261439)
                      ·
                        rfl

theorem cell23_2821549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_2821549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821549 prefixEnd_2821549 := by exact prefixLift 2821549
  have htrace : WordTrace (prefixWord ++ tailWord_2821549) baseStart_2821549 baseEnd_2821549 := by
    simpa [prefixWord, tailWord_2821549, baseEnd_2821549] using wordTrace_append hprefix tailTrace_2821549
  have hstable : (prefixWord ++ tailWord_2821549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821549).length < 2 ^ (prefixWord ++ tailWord_2821549).sum := by decide
  have hdescent : baseEnd_2821549 < baseStart_2821549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821571 : List Nat := [1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 4]
def baseStart_2821571 : Nat := 118140960795 + 2821571 * 2 ^ 59
def prefixEnd_2821571 : Nat := 4983230072969 + 3 ^ 40 * 2821571 * 2
def baseEnd_2821571 : Nat := 1448822123787285324186337

theorem tailTrace_2821571 : CollatzResearch.WordTrace tailWord_2821571 prefixEnd_2821571 1448822123787285324186337 := by
  unfold tailWord_2821571
  simp only [CollatzResearch.WordTrace]
  refine ⟨102911148860937627807008567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68607432573958418538005711 102911148860937627807008567)
  ·
    refine ⟨154366723291406441710512851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102911148860937627807008567 154366723291406441710512851)
    ·
      refine ⟨231550084937109662565769277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154366723291406441710512851 231550084937109662565769277)
      ·
        refine ⟨86831281851416123462163479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231550084937109662565769277 86831281851416123462163479)
        ·
          refine ⟨130246922777124185193245219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86831281851416123462163479 130246922777124185193245219)
          ·
            refine ⟨195370384165686277789867829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130246922777124185193245219 195370384165686277789867829)
            ·
              refine ⟨18315973515533088542800109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 195370384165686277789867829 18315973515533088542800109)
              ·
                refine ⟨6868490068324908203550041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18315973515533088542800109 6868490068324908203550041)
                ·
                  refine ⟨5151367551243681152662531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6868490068324908203550041 5151367551243681152662531)
                  ·
                    refine ⟨7727051326865521728993797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5151367551243681152662531 7727051326865521728993797)
                    ·
                      refine ⟨1448822123787285324186337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7727051326865521728993797 1448822123787285324186337)
                      ·
                        rfl

theorem cell23_2821571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_2821571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821571 prefixEnd_2821571 := by exact prefixLift 2821571
  have htrace : WordTrace (prefixWord ++ tailWord_2821571) baseStart_2821571 baseEnd_2821571 := by
    simpa [prefixWord, tailWord_2821571, baseEnd_2821571] using wordTrace_append hprefix tailTrace_2821571
  have hstable : (prefixWord ++ tailWord_2821571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821571).length < 2 ^ (prefixWord ++ tailWord_2821571).sum := by decide
  have hdescent : baseEnd_2821571 < baseStart_2821571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821584 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 6]
def baseStart_2821584 : Nat := 118140960795 + 2821584 * 2 ^ 59
def prefixEnd_2821584 : Nat := 4983230072969 + 3 ^ 40 * 2821584 * 2
def baseEnd_2821584 : Nat := 1448828799035793773323777

theorem tailTrace_2821584 : CollatzResearch.WordTrace tailWord_2821584 prefixEnd_2821584 1448828799035793773323777 := by
  unfold tailWord_2821584
  simp only [CollatzResearch.WordTrace]
  refine ⟨51455811504945265513615903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68607748673260354018154537 51455811504945265513615903)
  ·
    refine ⟨77183717257417898270423855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51455811504945265513615903 77183717257417898270423855)
    ·
      refine ⟨115775575886126847405635783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77183717257417898270423855 115775575886126847405635783)
      ·
        refine ⟨173663363829190271108453675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115775575886126847405635783 173663363829190271108453675)
        ·
          refine ⟨260495045743785406662680513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173663363829190271108453675 260495045743785406662680513)
          ·
            refine ⟨195371284307839054997010385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260495045743785406662680513 195371284307839054997010385)
            ·
              refine ⟨146528463230879291247757789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195371284307839054997010385 146528463230879291247757789)
              ·
                refine ⟨54948173711579734217909171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146528463230879291247757789 54948173711579734217909171)
                ·
                  refine ⟨82422260567369601326863757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54948173711579734217909171 82422260567369601326863757)
                  ·
                    refine ⟨30908347712763600497573909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82422260567369601326863757 30908347712763600497573909)
                    ·
                      refine ⟨1448828799035793773323777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30908347712763600497573909 1448828799035793773323777)
                      ·
                        rfl

theorem cell23_2821584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 6].length) (baseStart_2821584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821584 prefixEnd_2821584 := by exact prefixLift 2821584
  have htrace : WordTrace (prefixWord ++ tailWord_2821584) baseStart_2821584 baseEnd_2821584 := by
    simpa [prefixWord, tailWord_2821584, baseEnd_2821584] using wordTrace_append hprefix tailTrace_2821584
  have hstable : (prefixWord ++ tailWord_2821584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821584).length < 2 ^ (prefixWord ++ tailWord_2821584).sum := by decide
  have hdescent : baseEnd_2821584 < baseStart_2821584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821605 : List Nat := [1, 3, 1, 5, 1, 2, 1, 1, 2, 4, 2]
def baseStart_2821605 : Nat := 118140960795 + 2821605 * 2 ^ 59
def prefixEnd_2821605 : Nat := 4983230072969 + 3 ^ 40 * 2821605 * 2
def baseEnd_2821605 : Nat := 1448839582129538191161181

theorem tailTrace_2821605 : CollatzResearch.WordTrace tailWord_2821605 prefixEnd_2821605 1448839582129538191161181 := by
  unfold tailWord_2821605
  simp only [CollatzResearch.WordTrace]
  refine ⟨102912388942814451613746269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68608259295209634409164179 102912388942814451613746269)
  ·
    refine ⟨38592145853555419355154851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102912388942814451613746269 38592145853555419355154851)
    ·
      refine ⟨57888218780333129032732277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38592145853555419355154851 57888218780333129032732277)
      ·
        refine ⟨5427020510656230846818651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57888218780333129032732277 5427020510656230846818651)
        ·
          refine ⟨8140530765984346270227977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5427020510656230846818651 8140530765984346270227977)
          ·
            refine ⟨6105398074488259702670983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8140530765984346270227977 6105398074488259702670983)
            ·
              refine ⟨9158097111732389554006475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6105398074488259702670983 9158097111732389554006475)
              ·
                refine ⟨13737145667598584331009713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9158097111732389554006475 13737145667598584331009713)
                ·
                  refine ⟨10302859250698938248257285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13737145667598584331009713 10302859250698938248257285)
                  ·
                    refine ⟨1931786109506050921548241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10302859250698938248257285 1931786109506050921548241)
                    ·
                      refine ⟨1448839582129538191161181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1931786109506050921548241 1448839582129538191161181)
                      ·
                        rfl

theorem cell23_2821605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_2821605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821605 prefixEnd_2821605 := by exact prefixLift 2821605
  have htrace : WordTrace (prefixWord ++ tailWord_2821605) baseStart_2821605 baseEnd_2821605 := by
    simpa [prefixWord, tailWord_2821605, baseEnd_2821605] using wordTrace_append hprefix tailTrace_2821605
  have hstable : (prefixWord ++ tailWord_2821605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821605).length < 2 ^ (prefixWord ++ tailWord_2821605).sum := by decide
  have hdescent : baseEnd_2821605 < baseStart_2821605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821681 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 5, 1, 5]
def baseStart_2821681 : Nat := 118140960795 + 2821681 * 2 ^ 59
def prefixEnd_2821681 : Nat := 4983230072969 + 3 ^ 40 * 2821681 * 2
def baseEnd_2821681 : Nat := 1448878606659279893810831

theorem tailTrace_2821681 : CollatzResearch.WordTrace tailWord_2821681 prefixEnd_2821681 1448878606659279893810831 := by
  unfold tailWord_2821681
  simp only [CollatzResearch.WordTrace]
  refine ⟨102915160890539116593512897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68610107260359411062341931 102915160890539116593512897)
  ·
    refine ⟨77186370667904337445134673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102915160890539116593512897 77186370667904337445134673)
    ·
      refine ⟨57889778000928253083851005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77186370667904337445134673 57889778000928253083851005)
      ·
        refine ⟨21708666750348094906444127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57889778000928253083851005 21708666750348094906444127)
        ·
          refine ⟨32563000125522142359666191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21708666750348094906444127 32563000125522142359666191)
          ·
            refine ⟨48844500188283213539499287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32563000125522142359666191 48844500188283213539499287)
            ·
              refine ⟨73266750282424820309248931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48844500188283213539499287 73266750282424820309248931)
              ·
                refine ⟨109900125423637230463873397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73266750282424820309248931 109900125423637230463873397)
                ·
                  refine ⟨10303136758465990355988131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109900125423637230463873397 10303136758465990355988131)
                  ·
                    refine ⟨15454705137698985533982197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10303136758465990355988131 15454705137698985533982197)
                    ·
                      refine ⟨1448878606659279893810831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15454705137698985533982197 1448878606659279893810831)
                      ·
                        rfl

theorem cell23_2821681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_2821681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821681 prefixEnd_2821681 := by exact prefixLift 2821681
  have htrace : WordTrace (prefixWord ++ tailWord_2821681) baseStart_2821681 baseEnd_2821681 := by
    simpa [prefixWord, tailWord_2821681, baseEnd_2821681] using wordTrace_append hprefix tailTrace_2821681
  have hstable : (prefixWord ++ tailWord_2821681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821681).length < 2 ^ (prefixWord ++ tailWord_2821681).sum := by decide
  have hdescent : baseEnd_2821681 < baseStart_2821681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821688 : List Nat := [2, 1, 2, 1, 4, 2, 1, 2, 4, 4]
def baseStart_2821688 : Nat := 118140960795 + 2821688 * 2 ^ 59
def prefixEnd_2821688 : Nat := 4983230072969 + 3 ^ 40 * 2821688 * 2
def baseEnd_2821688 : Nat := 482960733674620455474433

theorem tailTrace_2821688 : CollatzResearch.WordTrace tailWord_2821688 prefixEnd_2821688 482960733674620455474433 := by
  unfold tailWord_2821688
  simp only [CollatzResearch.WordTrace]
  refine ⟨51457708100756878394508859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68610277467675837859345145 51457708100756878394508859)
  ·
    refine ⟨77186562151135317591763289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51457708100756878394508859 77186562151135317591763289)
    ·
      refine ⟨57889921613351488193822467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77186562151135317591763289 57889921613351488193822467)
      ·
        refine ⟨86834882420027232290733701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57889921613351488193822467 86834882420027232290733701)
        ·
          refine ⟨16281540453755106054512569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86834882420027232290733701 16281540453755106054512569)
          ·
            refine ⟨12211155340316329540884427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16281540453755106054512569 12211155340316329540884427)
            ·
              refine ⟨18316733010474494311326641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12211155340316329540884427 18316733010474494311326641)
              ·
                refine ⟨13737549757855870733494981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18316733010474494311326641 13737549757855870733494981)
                ·
                  refine ⟨2575790579597975762530309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13737549757855870733494981 2575790579597975762530309)
                  ·
                    refine ⟨482960733674620455474433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2575790579597975762530309 482960733674620455474433)
                    ·
                      rfl

theorem cell23_2821688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 4, 4].length) (baseStart_2821688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821688 prefixEnd_2821688 := by exact prefixLift 2821688
  have htrace : WordTrace (prefixWord ++ tailWord_2821688) baseStart_2821688 baseEnd_2821688 := by
    simpa [prefixWord, tailWord_2821688, baseEnd_2821688] using wordTrace_append hprefix tailTrace_2821688
  have hstable : (prefixWord ++ tailWord_2821688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821688).length < 2 ^ (prefixWord ++ tailWord_2821688).sum := by decide
  have hdescent : baseEnd_2821688 < baseStart_2821688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821689 : List Nat := [1, 2, 1, 5, 1, 4, 1, 3, 1, 1, 3]
def baseStart_2821689 : Nat := 118140960795 + 2821689 * 2 ^ 59
def prefixEnd_2821689 : Nat := 4983230072969 + 3 ^ 40 * 2821689 * 2
def baseEnd_2821689 : Nat := 1448882714504515862510795

theorem tailTrace_2821689 : CollatzResearch.WordTrace tailWord_2821689 prefixEnd_2821689 1448882714504515862510795 := by
  unfold tailWord_2821689
  simp only [CollatzResearch.WordTrace]
  refine ⟨102915452674510133959804121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68610301783006755973202747 102915452674510133959804121)
  ·
    refine ⟨77186589505882600469853091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102915452674510133959804121 77186589505882600469853091)
    ·
      refine ⟨115779884258823900704779637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77186589505882600469853091 115779884258823900704779637)
      ·
        refine ⟨10854364149264740691073091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115779884258823900704779637 10854364149264740691073091)
        ·
          refine ⟨16281546223897111036609637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10854364149264740691073091 16281546223897111036609637)
          ·
            refine ⟨3052789916980708319364307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16281546223897111036609637 3052789916980708319364307)
            ·
              refine ⟨4579184875471062479046461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3052789916980708319364307 4579184875471062479046461)
              ·
                refine ⟨1717194328301648429642423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4579184875471062479046461 1717194328301648429642423)
                ·
                  refine ⟨2575791492452472644463635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1717194328301648429642423 2575791492452472644463635)
                  ·
                    refine ⟨3863687238678708966695453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2575791492452472644463635 3863687238678708966695453)
                    ·
                      refine ⟨1448882714504515862510795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3863687238678708966695453 1448882714504515862510795)
                      ·
                        rfl

theorem cell23_2821689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_2821689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821689 prefixEnd_2821689 := by exact prefixLift 2821689
  have htrace : WordTrace (prefixWord ++ tailWord_2821689) baseStart_2821689 baseEnd_2821689 := by
    simpa [prefixWord, tailWord_2821689, baseEnd_2821689] using wordTrace_append hprefix tailTrace_2821689
  have hstable : (prefixWord ++ tailWord_2821689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821689).length < 2 ^ (prefixWord ++ tailWord_2821689).sum := by decide
  have hdescent : baseEnd_2821689 < baseStart_2821689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821728 : List Nat := [2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 3]
def baseStart_2821728 : Nat := 118140960795 + 2821728 * 2 ^ 59
def prefixEnd_2821728 : Nat := 4983230072969 + 3 ^ 40 * 2821728 * 2
def baseEnd_2821728 : Nat := 1448902740250041209923115

theorem tailTrace_2821728 : CollatzResearch.WordTrace tailWord_2821728 prefixEnd_2821728 1448902740250041209923115 := by
  unfold tailWord_2821728
  simp only [CollatzResearch.WordTrace]
  refine ⟨51458437560684421810236919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68611250080912562413649225 51458437560684421810236919)
  ·
    refine ⟨77187656341026632715355379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51458437560684421810236919 77187656341026632715355379)
    ·
      refine ⟨115781484511539949073033069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77187656341026632715355379 115781484511539949073033069)
      ·
        refine ⟨43418056691827480902387401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115781484511539949073033069 43418056691827480902387401)
        ·
          refine ⟨32563542518870610676790551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43418056691827480902387401 32563542518870610676790551)
          ·
            refine ⟨48845313778305916015185827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32563542518870610676790551 48845313778305916015185827)
            ·
              refine ⟨73267970667458874022778741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48845313778305916015185827 73267970667458874022778741)
              ·
                refine ⟨6868872250074269439635507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73267970667458874022778741 6868872250074269439635507)
                ·
                  refine ⟨10303308375111404159453261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6868872250074269439635507 10303308375111404159453261)
                  ·
                    refine ⟨3863740640666776559794973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10303308375111404159453261 3863740640666776559794973)
                    ·
                      refine ⟨1448902740250041209923115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3863740640666776559794973 1448902740250041209923115)
                      ·
                        rfl

theorem cell23_2821728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_2821728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821728 prefixEnd_2821728 := by exact prefixLift 2821728
  have htrace : WordTrace (prefixWord ++ tailWord_2821728) baseStart_2821728 baseEnd_2821728 := by
    simpa [prefixWord, tailWord_2821728, baseEnd_2821728] using wordTrace_append hprefix tailTrace_2821728
  have hstable : (prefixWord ++ tailWord_2821728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821728).length < 2 ^ (prefixWord ++ tailWord_2821728).sum := by decide
  have hdescent : baseEnd_2821728 < baseStart_2821728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821732 : List Nat := [2, 3, 1, 1, 2, 5, 1, 2, 1, 2, 3]
def baseStart_2821732 : Nat := 118140960795 + 2821732 * 2 ^ 59
def prefixEnd_2821732 : Nat := 4983230072969 + 3 ^ 40 * 2821732 * 2
def baseEnd_2821732 : Nat := 1448904794172659194273097

theorem tailTrace_2821732 : CollatzResearch.WordTrace tailWord_2821732 prefixEnd_2821732 1448904794172659194273097 := by
  unfold tailWord_2821732
  simp only [CollatzResearch.WordTrace]
  refine ⟨51458510506677176151809725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68611347342236234869079633 51458510506677176151809725)
  ·
    refine ⟨19296941440003941056928647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51458510506677176151809725 19296941440003941056928647)
    ·
      refine ⟨28945412160005911585392971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19296941440003941056928647 28945412160005911585392971)
      ·
        refine ⟨43418118240008867378089457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28945412160005911585392971 43418118240008867378089457)
        ·
          refine ⟨32563588680006650533567093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43418118240008867378089457 32563588680006650533567093)
          ·
            refine ⟨3052836438750623487521915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32563588680006650533567093 3052836438750623487521915)
            ·
              refine ⟨4579254658125935231282873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3052836438750623487521915 4579254658125935231282873)
              ·
                refine ⟨3434440993594451423462155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4579254658125935231282873 3434440993594451423462155)
                ·
                  refine ⟨5151661490391677135193233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3434440993594451423462155 5151661490391677135193233)
                  ·
                    refine ⟨3863746117793757851394925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5151661490391677135193233 3863746117793757851394925)
                    ·
                      refine ⟨1448904794172659194273097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3863746117793757851394925 1448904794172659194273097)
                      ·
                        rfl

theorem cell23_2821732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_2821732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821732 prefixEnd_2821732 := by exact prefixLift 2821732
  have htrace : WordTrace (prefixWord ++ tailWord_2821732) baseStart_2821732 baseEnd_2821732 := by
    simpa [prefixWord, tailWord_2821732, baseEnd_2821732] using wordTrace_append hprefix tailTrace_2821732
  have hstable : (prefixWord ++ tailWord_2821732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821732).length < 2 ^ (prefixWord ++ tailWord_2821732).sum := by decide
  have hdescent : baseEnd_2821732 < baseStart_2821732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821749 : List Nat := [1, 3, 4, 2, 1, 2, 3, 1, 1, 2, 3]
def baseStart_2821749 : Nat := 118140960795 + 2821749 * 2 ^ 59
def prefixEnd_2821749 : Nat := 4983230072969 + 3 ^ 40 * 2821749 * 2
def baseEnd_2821749 : Nat := 1448913523343785627760519

theorem tailTrace_2821749 : CollatzResearch.WordTrace tailWord_2821749 prefixEnd_2821749 1448913523343785627760519 := by
  unfold tailWord_2821749
  simp only [CollatzResearch.WordTrace]
  refine ⟨102917641054292764206988301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68611760702861842804658867 102917641054292764206988301)
  ·
    refine ⟨38594115395359786577620613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102917641054292764206988301 38594115395359786577620613)
    ·
      refine ⟨7236396636629959983303865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38594115395359786577620613 7236396636629959983303865)
      ·
        refine ⟨5427297477472469987477899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7236396636629959983303865 5427297477472469987477899)
        ·
          refine ⟨8140946216208704981216849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5427297477472469987477899 8140946216208704981216849)
          ·
            refine ⟨6105709662156528735912637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8140946216208704981216849 6105709662156528735912637)
            ·
              refine ⟨2289641123308698275967239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6105709662156528735912637 2289641123308698275967239)
              ·
                refine ⟨3434461684963047413950859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2289641123308698275967239 3434461684963047413950859)
                ·
                  refine ⟨5151692527444571120926289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3434461684963047413950859 5151692527444571120926289)
                  ·
                    refine ⟨3863769395583428340694717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5151692527444571120926289 3863769395583428340694717)
                    ·
                      refine ⟨1448913523343785627760519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3863769395583428340694717 1448913523343785627760519)
                      ·
                        rfl

theorem cell23_2821749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_2821749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821749 prefixEnd_2821749 := by exact prefixLift 2821749
  have htrace : WordTrace (prefixWord ++ tailWord_2821749) baseStart_2821749 baseEnd_2821749 := by
    simpa [prefixWord, tailWord_2821749, baseEnd_2821749] using wordTrace_append hprefix tailTrace_2821749
  have hstable : (prefixWord ++ tailWord_2821749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821749).length < 2 ^ (prefixWord ++ tailWord_2821749).sum := by decide
  have hdescent : baseEnd_2821749 < baseStart_2821749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821800 : List Nat := [2, 1, 7, 1, 2, 1, 2, 1, 1, 2, 3]
def baseStart_2821800 : Nat := 118140960795 + 2821800 * 2 ^ 59
def prefixEnd_2821800 : Nat := 4983230072969 + 3 ^ 40 * 2821800 * 2
def baseEnd_2821800 : Nat := 1448939710857164928222785

theorem tailTrace_2821800 : CollatzResearch.WordTrace tailWord_2821800 prefixEnd_2821800 1448939710857164928222785 := by
  unfold tailWord_2821800
  simp only [CollatzResearch.WordTrace]
  refine ⟨51459750588553999958547427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68613000784738666611396569 51459750588553999958547427)
  ·
    refine ⟨77189625882830999937821141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51459750588553999958547427 77189625882830999937821141)
    ·
      refine ⟨1809131856628851561042683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 77189625882830999937821141 1809131856628851561042683)
      ·
        refine ⟨2713697784943277341564025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1809131856628851561042683 2713697784943277341564025)
        ·
          refine ⟨2035273338707458006173019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2713697784943277341564025 2035273338707458006173019)
          ·
            refine ⟨3052910008061187009259529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2035273338707458006173019 3052910008061187009259529)
            ·
              refine ⟨2289682506045890256944647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3052910008061187009259529 2289682506045890256944647)
              ·
                refine ⟨3434523759068835385416971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2289682506045890256944647 3434523759068835385416971)
                ·
                  refine ⟨5151785638603253078125457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3434523759068835385416971 5151785638603253078125457)
                  ·
                    refine ⟨3863839228952439808594093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5151785638603253078125457 3863839228952439808594093)
                    ·
                      refine ⟨1448939710857164928222785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3863839228952439808594093 1448939710857164928222785)
                      ·
                        rfl

theorem cell23_2821800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_2821800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821800 prefixEnd_2821800 := by exact prefixLift 2821800
  have htrace : WordTrace (prefixWord ++ tailWord_2821800) baseStart_2821800 baseEnd_2821800 := by
    simpa [prefixWord, tailWord_2821800, baseEnd_2821800] using wordTrace_append hprefix tailTrace_2821800
  have hstable : (prefixWord ++ tailWord_2821800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821800).length < 2 ^ (prefixWord ++ tailWord_2821800).sum := by decide
  have hdescent : baseEnd_2821800 < baseStart_2821800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821806 : List Nat := [4, 1, 4, 1, 2, 1, 1, 3, 1, 3, 2]
def baseStart_2821806 : Nat := 118140960795 + 2821806 * 2 ^ 59
def prefixEnd_2821806 : Nat := 4983230072969 + 3 ^ 40 * 2821806 * 2
def baseEnd_2821806 : Nat := 1448942791741091904747757

theorem tailTrace_2821806 : CollatzResearch.WordTrace tailWord_2821806 prefixEnd_2821806 1448942791741091904747757 := by
  unfold tailWord_2821806
  simp only [CollatzResearch.WordTrace]
  refine ⟨12864965001885782867726659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68613146676724175294542181 12864965001885782867726659)
  ·
    refine ⟨19297447502828674301589989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12864965001885782867726659 19297447502828674301589989)
    ·
      refine ⟨3618271406780376431548123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19297447502828674301589989 3618271406780376431548123)
      ·
        refine ⟨5427407110170564647322185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3618271406780376431548123 5427407110170564647322185)
        ·
          refine ⟨4070555332627923485491639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5427407110170564647322185 4070555332627923485491639)
          ·
            refine ⟨6105832998941885228237459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4070555332627923485491639 6105832998941885228237459)
            ·
              refine ⟨9158749498412827842356189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6105832998941885228237459 9158749498412827842356189)
              ·
                refine ⟨3434531061904810440883571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9158749498412827842356189 3434531061904810440883571)
                ·
                  refine ⟨5151796592857215661325357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3434531061904810440883571 5151796592857215661325357)
                  ·
                    refine ⟨1931923722321455872997009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5151796592857215661325357 1931923722321455872997009)
                    ·
                      refine ⟨1448942791741091904747757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1931923722321455872997009 1448942791741091904747757)
                      ·
                        rfl

theorem cell23_2821806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_2821806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821806 prefixEnd_2821806 := by exact prefixLift 2821806
  have htrace : WordTrace (prefixWord ++ tailWord_2821806) baseStart_2821806 baseEnd_2821806 := by
    simpa [prefixWord, tailWord_2821806, baseEnd_2821806] using wordTrace_append hprefix tailTrace_2821806
  have hstable : (prefixWord ++ tailWord_2821806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821806).length < 2 ^ (prefixWord ++ tailWord_2821806).sum := by decide
  have hdescent : baseEnd_2821806 < baseStart_2821806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821836 : List Nat := [2, 2, 1, 5, 3, 1, 1, 1, 1, 4, 2]
def baseStart_2821836 : Nat := 118140960795 + 2821836 * 2 ^ 59
def prefixEnd_2821836 : Nat := 4983230072969 + 3 ^ 40 * 2821836 * 2
def baseEnd_2821836 : Nat := 1448958196160726787372619

theorem tailTrace_2821836 : CollatzResearch.WordTrace tailWord_2821836 prefixEnd_2821836 1448958196160726787372619 := by
  unfold tailWord_2821836
  simp only [CollatzResearch.WordTrace]
  refine ⟨51460407102488789032702681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68613876136651718710270241 51460407102488789032702681)
  ·
    refine ⟨38595305326866591774527011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51460407102488789032702681 38595305326866591774527011)
    ·
      refine ⟨57892957990299887661790517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38595305326866591774527011 57892957990299887661790517)
      ·
        refine ⟨5427464811590614468292861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57892957990299887661790517 5427464811590614468292861)
        ·
          refine ⟨2035299304346480425609823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5427464811590614468292861 2035299304346480425609823)
          ·
            refine ⟨3052948956519720638414735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2035299304346480425609823 3052948956519720638414735)
            ·
              refine ⟨4579423434779580957622103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3052948956519720638414735 4579423434779580957622103)
              ·
                refine ⟨6869135152169371436433155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4579423434779580957622103 6869135152169371436433155)
                ·
                  refine ⟨10303702728254057154649733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6869135152169371436433155 10303702728254057154649733)
                  ·
                    refine ⟨1931944261547635716496825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10303702728254057154649733 1931944261547635716496825)
                    ·
                      refine ⟨1448958196160726787372619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1931944261547635716496825 1448958196160726787372619)
                      ·
                        rfl

theorem cell23_2821836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_2821836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821836 prefixEnd_2821836 := by exact prefixLift 2821836
  have htrace : WordTrace (prefixWord ++ tailWord_2821836) baseStart_2821836 baseEnd_2821836 := by
    simpa [prefixWord, tailWord_2821836, baseEnd_2821836] using wordTrace_append hprefix tailTrace_2821836
  have hstable : (prefixWord ++ tailWord_2821836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821836).length < 2 ^ (prefixWord ++ tailWord_2821836).sum := by decide
  have hdescent : baseEnd_2821836 < baseStart_2821836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821838 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 3, 7]
def baseStart_2821838 : Nat := 118140960795 + 2821838 * 2 ^ 59
def prefixEnd_2821838 : Nat := 4983230072969 + 3 ^ 40 * 2821838 * 2
def baseEnd_2821838 : Nat := 482986407707345259849203

theorem tailTrace_2821838 : CollatzResearch.WordTrace tailWord_2821838 prefixEnd_2821838 482986407707345259849203 := by
  unfold tailWord_2821838
  simp only [CollatzResearch.WordTrace]
  refine ⟨12865110893871291550872271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68613924767313554937985445 12865110893871291550872271)
  ·
    refine ⟨19297666340806937326308407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12865110893871291550872271 19297666340806937326308407)
    ·
      refine ⟨28946499511210405989462611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19297666340806937326308407 28946499511210405989462611)
      ·
        refine ⟨43419749266815608984193917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28946499511210405989462611 43419749266815608984193917)
        ·
          refine ⟨16282405975055853369072719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43419749266815608984193917 16282405975055853369072719)
          ·
            refine ⟨24423608962583780053609079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16282405975055853369072719 24423608962583780053609079)
            ·
              refine ⟨36635413443875670080413619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24423608962583780053609079 36635413443875670080413619)
              ·
                refine ⟨54953120165813505120620429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36635413443875670080413619 54953120165813505120620429)
                ·
                  refine ⟨20607420062180064420232661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54953120165813505120620429 20607420062180064420232661)
                  ·
                    refine ⟨482986407707345259849203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20607420062180064420232661 482986407707345259849203)
                    ·
                      rfl

theorem cell23_2821838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_2821838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821838 prefixEnd_2821838 := by exact prefixLift 2821838
  have htrace : WordTrace (prefixWord ++ tailWord_2821838) baseStart_2821838 baseEnd_2821838 := by
    simpa [prefixWord, tailWord_2821838, baseEnd_2821838] using wordTrace_append hprefix tailTrace_2821838
  have hstable : (prefixWord ++ tailWord_2821838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821838).length < 2 ^ (prefixWord ++ tailWord_2821838).sum := by decide
  have hdescent : baseEnd_2821838 < baseStart_2821838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821859 : List Nat := [1, 1, 1, 7, 2, 2, 1, 3, 5]
def baseStart_2821859 : Nat := 118140960795 + 2821859 * 2 ^ 59
def prefixEnd_2821859 : Nat := 4983230072969 + 3 ^ 40 * 2821859 * 2
def baseEnd_2821859 : Nat := 160996667357308910820557

theorem tailTrace_2821859 : CollatzResearch.WordTrace tailWord_2821859 prefixEnd_2821859 160996667357308910820557 := by
  unfold tailWord_2821859
  simp only [CollatzResearch.WordTrace]
  refine ⟨102921653083894252993492631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68614435389262835328995087 102921653083894252993492631)
  ·
    refine ⟨154382479625841379490238947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102921653083894252993492631 154382479625841379490238947)
    ·
      refine ⟨231573719438762069235358421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154382479625841379490238947 231573719438762069235358421)
      ·
        refine ⟨5427509049345985997703713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 231573719438762069235358421 5427509049345985997703713)
        ·
          refine ⟨4070631787009489498277785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5427509049345985997703713 4070631787009489498277785)
          ·
            refine ⟨3052973840257117123708339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4070631787009489498277785 3052973840257117123708339)
            ·
              refine ⟨4579460760385675685562509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3052973840257117123708339 4579460760385675685562509)
              ·
                refine ⟨1717297785144628382085941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4579460760385675685562509 1717297785144628382085941)
                ·
                  refine ⟨160996667357308910820557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1717297785144628382085941 160996667357308910820557)
                  ·
                    rfl

theorem cell23_2821859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 3, 5].length) (baseStart_2821859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821859 prefixEnd_2821859 := by exact prefixLift 2821859
  have htrace : WordTrace (prefixWord ++ tailWord_2821859) baseStart_2821859 baseEnd_2821859 := by
    simpa [prefixWord, tailWord_2821859, baseEnd_2821859] using wordTrace_append hprefix tailTrace_2821859
  have hstable : (prefixWord ++ tailWord_2821859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821859).length < 2 ^ (prefixWord ++ tailWord_2821859).sum := by decide
  have hdescent : baseEnd_2821859 < baseStart_2821859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821875 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 4, 4, 2]
def baseStart_2821875 : Nat := 118140960795 + 2821875 * 2 ^ 59
def prefixEnd_2821875 : Nat := 4983230072969 + 3 ^ 40 * 2821875 * 2
def baseEnd_2821875 : Nat := 1448978221906252134784939

theorem tailTrace_2821875 : CollatzResearch.WordTrace tailWord_2821875 prefixEnd_2821875 1448978221906252134784939 := by
  unfold tailWord_2821875
  simp only [CollatzResearch.WordTrace]
  refine ⟨102922236651836287726075079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68614824434557525150716719 102922236651836287726075079)
  ·
    refine ⟨154383354977754431589112619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102922236651836287726075079 154383354977754431589112619)
    ·
      refine ⟨231575032466631647383668929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154383354977754431589112619 231575032466631647383668929)
      ·
        refine ⟨173681274349973735537751697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231575032466631647383668929 173681274349973735537751697)
        ·
          refine ⟨130260955762480301653313773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173681274349973735537751697 130260955762480301653313773)
          ·
            refine ⟨48847858410930113119992665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130260955762480301653313773 48847858410930113119992665)
            ·
              refine ⟨36635893808197584839994499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48847858410930113119992665 36635893808197584839994499)
              ·
                refine ⟨54953840712296377259991749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36635893808197584839994499 54953840712296377259991749)
                ·
                  refine ⟨10303845133555570736248453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54953840712296377259991749 10303845133555570736248453)
                  ·
                    refine ⟨1931970962541669513046585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10303845133555570736248453 1931970962541669513046585)
                    ·
                      refine ⟨1448978221906252134784939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1931970962541669513046585 1448978221906252134784939)
                      ·
                        rfl

theorem cell23_2821875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 4, 2].length) (baseStart_2821875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821875 prefixEnd_2821875 := by exact prefixLift 2821875
  have htrace : WordTrace (prefixWord ++ tailWord_2821875) baseStart_2821875 baseEnd_2821875 := by
    simpa [prefixWord, tailWord_2821875, baseEnd_2821875] using wordTrace_append hprefix tailTrace_2821875
  have hstable : (prefixWord ++ tailWord_2821875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821875).length < 2 ^ (prefixWord ++ tailWord_2821875).sum := by decide
  have hdescent : baseEnd_2821875 < baseStart_2821875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821885 : List Nat := [1, 4, 1, 1, 1, 1, 2, 5, 3, 4]
def baseStart_2821885 : Nat := 118140960795 + 2821885 * 2 ^ 59
def prefixEnd_2821885 : Nat := 4983230072969 + 3 ^ 40 * 2821885 * 2
def baseEnd_2821885 : Nat := 482994452237599031886631

theorem tailTrace_2821885 : CollatzResearch.WordTrace tailWord_2821885 prefixEnd_2821885 482994452237599031886631 := by
  unfold tailWord_2821885
  simp only [CollatzResearch.WordTrace]
  refine ⟨102922601381800059433939109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68615067587866706289292739 102922601381800059433939109)
  ·
    refine ⟨19297987759087511143863583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102922601381800059433939109 19297987759087511143863583)
    ·
      refine ⟨28946981638631266715795375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19297987759087511143863583 28946981638631266715795375)
      ·
        refine ⟨43420472457946900073693063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28946981638631266715795375 43420472457946900073693063)
        ·
          refine ⟨65130708686920350110539595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43420472457946900073693063 65130708686920350110539595)
          ·
            refine ⟨97696063030380525165809393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65130708686920350110539595 97696063030380525165809393)
            ·
              refine ⟨73272047272785393874357045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97696063030380525165809393 73272047272785393874357045)
              ·
                refine ⟨6869254431823630675720973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73272047272785393874357045 6869254431823630675720973)
                ·
                  refine ⟨2575970411933861503395365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6869254431823630675720973 2575970411933861503395365)
                  ·
                    refine ⟨482994452237599031886631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2575970411933861503395365 482994452237599031886631)
                    ·
                      rfl

theorem cell23_2821885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_2821885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821885 prefixEnd_2821885 := by exact prefixLift 2821885
  have htrace : WordTrace (prefixWord ++ tailWord_2821885) baseStart_2821885 baseEnd_2821885 := by
    simpa [prefixWord, tailWord_2821885, baseEnd_2821885] using wordTrace_append hprefix tailTrace_2821885
  have hstable : (prefixWord ++ tailWord_2821885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821885).length < 2 ^ (prefixWord ++ tailWord_2821885).sum := by decide
  have hdescent : baseEnd_2821885 < baseStart_2821885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821969 : List Nat := [1, 2, 2, 1, 5, 1, 3, 1, 2, 3, 2]
def baseStart_2821969 : Nat := 118140960795 + 2821969 * 2 ^ 59
def prefixEnd_2821969 : Nat := 4983230072969 + 3 ^ 40 * 2821969 * 2
def baseEnd_2821969 : Nat := 1449026489087774767009507

theorem tailTrace_2821969 : CollatzResearch.WordTrace tailWord_2821969 prefixEnd_2821969 1449026489087774767009507 := by
  unfold tailWord_2821969
  simp only [CollatzResearch.WordTrace]
  refine ⟨102925665113495741779996961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68617110075663827853331307 102925665113495741779996961)
  ·
    refine ⟨77194248835121806334997721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102925665113495741779996961 77194248835121806334997721)
    ·
      refine ⟨57895686626341354751248291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77194248835121806334997721 57895686626341354751248291)
      ·
        refine ⟨86843529939512032126872437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57895686626341354751248291 86843529939512032126872437)
        ·
          refine ⟨8141580931829253011894291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86843529939512032126872437 8141580931829253011894291)
          ·
            refine ⟨12212371397743879517841437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8141580931829253011894291 12212371397743879517841437)
            ·
              refine ⟨4579639274153954819190539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12212371397743879517841437 4579639274153954819190539)
              ·
                refine ⟨6869458911230932228785809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4579639274153954819190539 6869458911230932228785809)
                ·
                  refine ⟨5152094183423199171589357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6869458911230932228785809 5152094183423199171589357)
                  ·
                    refine ⟨1932035318783699689346009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5152094183423199171589357 1932035318783699689346009)
                    ·
                      refine ⟨1449026489087774767009507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1932035318783699689346009 1449026489087774767009507)
                      ·
                        rfl

theorem cell23_2821969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 3, 2].length) (baseStart_2821969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821969 prefixEnd_2821969 := by exact prefixLift 2821969
  have htrace : WordTrace (prefixWord ++ tailWord_2821969) baseStart_2821969 baseEnd_2821969 := by
    simpa [prefixWord, tailWord_2821969, baseEnd_2821969] using wordTrace_append hprefix tailTrace_2821969
  have hstable : (prefixWord ++ tailWord_2821969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821969).length < 2 ^ (prefixWord ++ tailWord_2821969).sum := by decide
  have hdescent : baseEnd_2821969 < baseStart_2821969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821985 : List Nat := [1, 2, 3, 1, 1, 1, 4, 3, 1, 1, 5]
def baseStart_2821985 : Nat := 118140960795 + 2821985 * 2 ^ 59
def prefixEnd_2821985 : Nat := 4983230072969 + 3 ^ 40 * 2821985 * 2
def baseEnd_2821985 : Nat := 1449034704778246704409433

theorem tailTrace_2821985 : CollatzResearch.WordTrace tailWord_2821985 prefixEnd_2821985 1449034704778246704409433 := by
  unfold tailWord_2821985
  simp only [CollatzResearch.WordTrace]
  refine ⟨102926248681437776512579409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68617499120958517675052939 102926248681437776512579409)
  ·
    refine ⟨77194686511078332384434557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102926248681437776512579409 77194686511078332384434557)
    ·
      refine ⟨28948007441654374644162959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77194686511078332384434557 28948007441654374644162959)
      ·
        refine ⟨43422011162481561966244439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28948007441654374644162959 43422011162481561966244439)
        ·
          refine ⟨65133016743722342949366659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43422011162481561966244439 65133016743722342949366659)
          ·
            refine ⟨97699525115583514424049989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65133016743722342949366659 97699525115583514424049989)
            ·
              refine ⟨18318660959171908954509373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97699525115583514424049989 18318660959171908954509373)
              ·
                refine ⟨6869497859689465857941015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18318660959171908954509373 6869497859689465857941015)
                ·
                  refine ⟨10304246789534198786911523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6869497859689465857941015 10304246789534198786911523)
                  ·
                    refine ⟨15456370184301298180367285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10304246789534198786911523 15456370184301298180367285)
                    ·
                      refine ⟨1449034704778246704409433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15456370184301298180367285 1449034704778246704409433)
                      ·
                        rfl

theorem cell23_2821985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_2821985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821985 prefixEnd_2821985 := by exact prefixLift 2821985
  have htrace : WordTrace (prefixWord ++ tailWord_2821985) baseStart_2821985 baseEnd_2821985 := by
    simpa [prefixWord, tailWord_2821985, baseEnd_2821985] using wordTrace_append hprefix tailTrace_2821985
  have hstable : (prefixWord ++ tailWord_2821985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821985).length < 2 ^ (prefixWord ++ tailWord_2821985).sum := by decide
  have hdescent : baseEnd_2821985 < baseStart_2821985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2821992 : List Nat := [2, 1, 4, 2, 1, 1, 3, 1, 4, 4]
def baseStart_2821992 : Nat := 118140960795 + 2821992 * 2 ^ 59
def prefixEnd_2821992 : Nat := 4983230072969 + 3 ^ 40 * 2821992 * 2
def baseEnd_2821992 : Nat := 483012766380942725673967

theorem tailTrace_2821992 : CollatzResearch.WordTrace tailWord_2821992 prefixEnd_2821992 483012766380942725673967 := by
  unfold tailWord_2821992
  simp only [CollatzResearch.WordTrace]
  refine ⟨51463251996206208354042115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68617669328274944472056153 51463251996206208354042115)
  ·
    refine ⟨77194877994309312531063173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51463251996206208354042115 77194877994309312531063173)
    ·
      refine ⟨14474039623932996099574345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77194877994309312531063173 14474039623932996099574345)
      ·
        refine ⟨10855529717949747074680759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14474039623932996099574345 10855529717949747074680759)
        ·
          refine ⟨16283294576924620612021139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10855529717949747074680759 16283294576924620612021139)
          ·
            refine ⟨24424941865386930918031709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16283294576924620612021139 24424941865386930918031709)
            ·
              refine ⟨9159353199520099094261891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24424941865386930918031709 9159353199520099094261891)
              ·
                refine ⟨13739029799280148641392837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9159353199520099094261891 13739029799280148641392837)
                ·
                  refine ⟨2576068087365027870261157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13739029799280148641392837 2576068087365027870261157)
                  ·
                    refine ⟨483012766380942725673967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2576068087365027870261157 483012766380942725673967)
                    ·
                      rfl

theorem cell23_2821992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_2821992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2821992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2821992 prefixEnd_2821992 := by exact prefixLift 2821992
  have htrace : WordTrace (prefixWord ++ tailWord_2821992) baseStart_2821992 baseEnd_2821992 := by
    simpa [prefixWord, tailWord_2821992, baseEnd_2821992] using wordTrace_append hprefix tailTrace_2821992
  have hstable : (prefixWord ++ tailWord_2821992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2821992).length < 2 ^ (prefixWord ++ tailWord_2821992).sum := by decide
  have hdescent : baseEnd_2821992 < baseStart_2821992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2821992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822005 : List Nat := [1, 3, 4, 1, 1, 1, 2, 10]
def baseStart_2822005 : Nat := 118140960795 + 2822005 * 2 ^ 59
def prefixEnd_2822005 : Nat := 4983230072969 + 3 ^ 40 * 2822005 * 2
def baseEnd_2822005 : Nat := 53668332384864319487383

theorem tailTrace_2822005 : CollatzResearch.WordTrace tailWord_2822005 prefixEnd_2822005 53668332384864319487383 := by
  unfold tailWord_2822005
  simp only [CollatzResearch.WordTrace]
  refine ⟨102926978141365319928307469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68617985427576879952204979 102926978141365319928307469)
  ·
    refine ⟨38597616803011994973115301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102926978141365319928307469 38597616803011994973115301)
    ·
      refine ⟨7237053150564749057459119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38597616803011994973115301 7237053150564749057459119)
      ·
        refine ⟨10855579725847123586188679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7237053150564749057459119 10855579725847123586188679)
        ·
          refine ⟨16283369588770685379283019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10855579725847123586188679 16283369588770685379283019)
          ·
            refine ⟨24425054383156028068924529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16283369588770685379283019 24425054383156028068924529)
            ·
              refine ⟨18318790787367021051693397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24425054383156028068924529 18318790787367021051693397)
              ·
                refine ⟨53668332384864319487383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18318790787367021051693397 53668332384864319487383)
                ·
                  rfl

theorem cell23_2822005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 10].length) (baseStart_2822005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822005 prefixEnd_2822005 := by exact prefixLift 2822005
  have htrace : WordTrace (prefixWord ++ tailWord_2822005) baseStart_2822005 baseEnd_2822005 := by
    simpa [prefixWord, tailWord_2822005, baseEnd_2822005] using wordTrace_append hprefix tailTrace_2822005
  have hstable : (prefixWord ++ tailWord_2822005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822005).length < 2 ^ (prefixWord ++ tailWord_2822005).sum := by decide
  have hdescent : baseEnd_2822005 < baseStart_2822005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822009 : List Nat := [1, 2, 1, 3, 2, 2, 5, 1, 2, 4]
def baseStart_2822009 : Nat := 118140960795 + 2822009 * 2 ^ 59
def prefixEnd_2822009 : Nat := 4983230072969 + 3 ^ 40 * 2822009 * 2
def baseEnd_2822009 : Nat := 483015676104651536836441

theorem tailTrace_2822009 : CollatzResearch.WordTrace tailWord_2822009 prefixEnd_2822009 483015676104651536836441 := by
  unfold tailWord_2822009
  simp only [CollatzResearch.WordTrace]
  refine ⟨102927124033350828611453081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68618082688900552407635387 102927124033350828611453081)
  ·
    refine ⟨77195343025013121458589811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102927124033350828611453081 77195343025013121458589811)
    ·
      refine ⟨115793014537519682187884717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77195343025013121458589811 115793014537519682187884717)
      ·
        refine ⟨43422380451569880820456769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115793014537519682187884717 43422380451569880820456769)
        ·
          refine ⟨32566785338677410615342577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43422380451569880820456769 32566785338677410615342577)
          ·
            refine ⟨24425089004008057961506933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32566785338677410615342577 24425089004008057961506933)
            ·
              refine ⟨2289852094125755433891275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24425089004008057961506933 2289852094125755433891275)
              ·
                refine ⟨3434778141188633150836913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2289852094125755433891275 3434778141188633150836913)
                ·
                  refine ⟨2576083605891474863127685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3434778141188633150836913 2576083605891474863127685)
                  ·
                    refine ⟨483015676104651536836441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2576083605891474863127685 483015676104651536836441)
                    ·
                      rfl

theorem cell23_2822009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 2, 4].length) (baseStart_2822009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822009 prefixEnd_2822009 := by exact prefixLift 2822009
  have htrace : WordTrace (prefixWord ++ tailWord_2822009) baseStart_2822009 baseEnd_2822009 := by
    simpa [prefixWord, tailWord_2822009, baseEnd_2822009] using wordTrace_append hprefix tailTrace_2822009
  have hstable : (prefixWord ++ tailWord_2822009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822009).length < 2 ^ (prefixWord ++ tailWord_2822009).sum := by decide
  have hdescent : baseEnd_2822009 < baseStart_2822009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822019 : List Nat := [1, 1, 1, 3, 4, 3, 2, 2, 1, 2, 3]
def baseStart_2822019 : Nat := 118140960795 + 2822019 * 2 ^ 59
def prefixEnd_2822019 : Nat := 4983230072969 + 3 ^ 40 * 2822019 * 2
def baseEnd_2822019 : Nat := 1449052163120499571384277

theorem tailTrace_2822019 : CollatzResearch.WordTrace tailWord_2822019 prefixEnd_2822019 1449052163120499571384277 := by
  unfold tailWord_2822019
  simp only [CollatzResearch.WordTrace]
  refine ⟨102927488763314600319317111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68618325842209733546211407 102927488763314600319317111)
  ·
    refine ⟨154391233144971900478975667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102927488763314600319317111 154391233144971900478975667)
    ·
      refine ⟨231586849717457850718463501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154391233144971900478975667 231586849717457850718463501)
      ·
        refine ⟨86845068644046694019423813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231586849717457850718463501 86845068644046694019423813)
        ·
          refine ⟨16283450370758755128641965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86845068644046694019423813 16283450370758755128641965)
          ·
            refine ⟨6106293889034533173240737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16283450370758755128641965 6106293889034533173240737)
            ·
              refine ⟨4579720416775899879930553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6106293889034533173240737 4579720416775899879930553)
              ·
                refine ⟨3434790312581924909947915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4579720416775899879930553 3434790312581924909947915)
                ·
                  refine ⟨5152185468872887364921873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3434790312581924909947915 5152185468872887364921873)
                  ·
                    refine ⟨3864139101654665523691405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5152185468872887364921873 3864139101654665523691405)
                    ·
                      refine ⟨1449052163120499571384277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3864139101654665523691405 1449052163120499571384277)
                      ·
                        rfl

theorem cell23_2822019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 2, 3].length) (baseStart_2822019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822019 prefixEnd_2822019 := by exact prefixLift 2822019
  have htrace : WordTrace (prefixWord ++ tailWord_2822019) baseStart_2822019 baseEnd_2822019 := by
    simpa [prefixWord, tailWord_2822019, baseEnd_2822019] using wordTrace_append hprefix tailTrace_2822019
  have hstable : (prefixWord ++ tailWord_2822019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822019).length < 2 ^ (prefixWord ++ tailWord_2822019).sum := by decide
  have hdescent : baseEnd_2822019 < baseStart_2822019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822032 : List Nat := [2, 1, 1, 1, 1, 1, 2, 6, 4, 1, 3]
def baseStart_2822032 : Nat := 118140960795 + 2822032 * 2 ^ 59
def prefixEnd_2822032 : Nat := 4983230072969 + 3 ^ 40 * 2822032 * 2
def baseEnd_2822032 : Nat := 1449058838369008020521717

theorem tailTrace_2822032 : CollatzResearch.WordTrace tailWord_2822032 prefixEnd_2822032 1449058838369008020521717 := by
  unfold tailWord_2822032
  simp only [CollatzResearch.WordTrace]
  refine ⟨51463981456133751769770175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68618641941511669026360233 51463981456133751769770175)
  ·
    refine ⟨77195972184200627654655263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51463981456133751769770175 77195972184200627654655263)
    ·
      refine ⟨115793958276300941481982895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77195972184200627654655263 115793958276300941481982895)
      ·
        refine ⟨173690937414451412222974343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115793958276300941481982895 173690937414451412222974343)
        ·
          refine ⟨260536406121677118334461515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173690937414451412222974343 260536406121677118334461515)
          ·
            refine ⟨390804609182515677501692273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260536406121677118334461515 390804609182515677501692273)
            ·
              refine ⟨293103456886886758126269205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 390804609182515677501692273 293103456886886758126269205)
              ·
                refine ⟨13739224541572816787168869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 293103456886886758126269205 13739224541572816787168869)
                ·
                  refine ⟨2576104601544903147594163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13739224541572816787168869 2576104601544903147594163)
                  ·
                    refine ⟨3864156902317354721391245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2576104601544903147594163 3864156902317354721391245)
                    ·
                      refine ⟨1449058838369008020521717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3864156902317354721391245 1449058838369008020521717)
                      ·
                        rfl

theorem cell23_2822032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 4, 1, 3].length) (baseStart_2822032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822032 prefixEnd_2822032 := by exact prefixLift 2822032
  have htrace : WordTrace (prefixWord ++ tailWord_2822032) baseStart_2822032 baseEnd_2822032 := by
    simpa [prefixWord, tailWord_2822032, baseEnd_2822032] using wordTrace_append hprefix tailTrace_2822032
  have hstable : (prefixWord ++ tailWord_2822032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822032).length < 2 ^ (prefixWord ++ tailWord_2822032).sum := by decide
  have hdescent : baseEnd_2822032 < baseStart_2822032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822050 : List Nat := [3, 3, 1, 2, 4, 1, 1, 1, 3, 2, 2]
def baseStart_2822050 : Nat := 118140960795 + 2822050 * 2 ^ 59
def prefixEnd_2822050 : Nat := 4983230072969 + 3 ^ 40 * 2822050 * 2
def baseEnd_2822050 : Nat := 1449068081020788950096635

theorem tailTrace_2822050 : CollatzResearch.WordTrace tailWord_2822050 prefixEnd_2822050 1449068081020788950096635 := by
  unfold tailWord_2822050
  simp only [CollatzResearch.WordTrace]
  refine ⟨25732154856550573153423901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68619079617468195075797069 25732154856550573153423901)
  ·
    refine ⟨9649558071206464932533963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25732154856550573153423901 9649558071206464932533963)
    ·
      refine ⟨14474337106809697398800945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9649558071206464932533963 14474337106809697398800945)
      ·
        refine ⟨10855752830107273049100709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14474337106809697398800945 10855752830107273049100709)
        ·
          refine ⟨2035453655645113696706383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10855752830107273049100709 2035453655645113696706383)
          ·
            refine ⟨3053180483467670545059575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2035453655645113696706383 3053180483467670545059575)
            ·
              refine ⟨4579770725201505817589363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3053180483467670545059575 4579770725201505817589363)
              ·
                refine ⟨6869656087802258726384045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4579770725201505817589363 6869656087802258726384045)
                ·
                  refine ⟨2576121032925847022394017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6869656087802258726384045 2576121032925847022394017)
                  ·
                    refine ⟨1932090774694385266795513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2576121032925847022394017 1932090774694385266795513)
                    ·
                      refine ⟨1449068081020788950096635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1932090774694385266795513 1449068081020788950096635)
                      ·
                        rfl

theorem cell23_2822050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_2822050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822050 prefixEnd_2822050 := by exact prefixLift 2822050
  have htrace : WordTrace (prefixWord ++ tailWord_2822050) baseStart_2822050 baseEnd_2822050 := by
    simpa [prefixWord, tailWord_2822050, baseEnd_2822050] using wordTrace_append hprefix tailTrace_2822050
  have hstable : (prefixWord ++ tailWord_2822050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822050).length < 2 ^ (prefixWord ++ tailWord_2822050).sum := by decide
  have hdescent : baseEnd_2822050 < baseStart_2822050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822075 : List Nat := [1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 5]
def baseStart_2822075 : Nat := 118140960795 + 2822075 * 2 ^ 59
def prefixEnd_2822075 : Nat := 4983230072969 + 3 ^ 40 * 2822075 * 2
def baseEnd_2822075 : Nat := 1449080918037151352284019

theorem tailTrace_2822075 : CollatzResearch.WordTrace tailWord_2822075 prefixEnd_2822075 1449080918037151352284019 := by
  unfold tailWord_2822075
  simp only [CollatzResearch.WordTrace]
  refine ⟨102929531251111721883355679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68619687500741147922237119 102929531251111721883355679)
  ·
    refine ⟨154394296876667582825033519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102929531251111721883355679 154394296876667582825033519)
    ·
      refine ⟨231591445315001374237550279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154394296876667582825033519 231591445315001374237550279)
      ·
        refine ⟨347387167972502061356325419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231591445315001374237550279 347387167972502061356325419)
        ·
          refine ⟨521080751958753092034488129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347387167972502061356325419 521080751958753092034488129)
          ·
            refine ⟨390810563969064819025866097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 521080751958753092034488129 390810563969064819025866097)
            ·
              refine ⟨293107922976798614269399573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 390810563969064819025866097 293107922976798614269399573)
              ·
                refine ⟨13739433889537435043878105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 293107922976798614269399573 13739433889537435043878105)
                ·
                  refine ⟨10304575417153076282908579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13739433889537435043878105 10304575417153076282908579)
                  ·
                    refine ⟨15456863125729614424362869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10304575417153076282908579 15456863125729614424362869)
                    ·
                      refine ⟨1449080918037151352284019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15456863125729614424362869 1449080918037151352284019)
                      ·
                        rfl

theorem cell23_2822075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 5].length) (baseStart_2822075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822075 prefixEnd_2822075 := by exact prefixLift 2822075
  have htrace : WordTrace (prefixWord ++ tailWord_2822075) baseStart_2822075 baseEnd_2822075 := by
    simpa [prefixWord, tailWord_2822075, baseEnd_2822075] using wordTrace_append hprefix tailTrace_2822075
  have hstable : (prefixWord ++ tailWord_2822075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822075).length < 2 ^ (prefixWord ++ tailWord_2822075).sum := by decide
  have hdescent : baseEnd_2822075 < baseStart_2822075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822085 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 3, 4, 4]
def baseStart_2822085 : Nat := 118140960795 + 2822085 * 2 ^ 59
def prefixEnd_2822085 : Nat := 4983230072969 + 3 ^ 40 * 2822085 * 2
def baseEnd_2822085 : Nat := 1449086052843696313158973

theorem tailTrace_2822085 : CollatzResearch.WordTrace tailWord_2822085 prefixEnd_2822085 1449086052843696313158973 := by
  unfold tailWord_2822085
  simp only [CollatzResearch.WordTrace]
  refine ⟨102929895981075493591219709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68619930654050329060813139 102929895981075493591219709)
  ·
    refine ⟨38598710992903310096707391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102929895981075493591219709 38598710992903310096707391)
    ·
      refine ⟨57898066489354965145061087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38598710992903310096707391 57898066489354965145061087)
      ·
        refine ⟨86847099734032447717591631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57898066489354965145061087 86847099734032447717591631)
        ·
          refine ⟨130270649601048671576387447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86847099734032447717591631 130270649601048671576387447)
          ·
            refine ⟨195405974401573007364581171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130270649601048671576387447 195405974401573007364581171)
            ·
              refine ⟨293108961602359511046871757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195405974401573007364581171 293108961602359511046871757)
              ·
                refine ⟨109915860600884816642576909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 293108961602359511046871757 109915860600884816642576909)
                ·
                  refine ⟨41218447725331806240966341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109915860600884816642576909 41218447725331806240966341)
                  ·
                    refine ⟨7728458948499713670181189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41218447725331806240966341 7728458948499713670181189)
                    ·
                      refine ⟨1449086052843696313158973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7728458948499713670181189 1449086052843696313158973)
                      ·
                        rfl

theorem cell23_2822085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_2822085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822085 prefixEnd_2822085 := by exact prefixLift 2822085
  have htrace : WordTrace (prefixWord ++ tailWord_2822085) baseStart_2822085 baseEnd_2822085 := by
    simpa [prefixWord, tailWord_2822085, baseEnd_2822085] using wordTrace_append hprefix tailTrace_2822085
  have hstable : (prefixWord ++ tailWord_2822085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822085).length < 2 ^ (prefixWord ++ tailWord_2822085).sum := by decide
  have hdescent : baseEnd_2822085 < baseStart_2822085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822092 : List Nat := [2, 2, 1, 4, 1, 2, 2, 1, 2, 1, 5]
def baseStart_2822092 : Nat := 118140960795 + 2822092 * 2 ^ 59
def prefixEnd_2822092 : Nat := 4983230072969 + 3 ^ 40 * 2822092 * 2
def baseEnd_2822092 : Nat := 1449089647208277785771441

theorem tailTrace_2822092 : CollatzResearch.WordTrace tailWord_2822092 prefixEnd_2822092 1449089647208277785771441 := by
  unfold tailWord_2822092
  simp only [CollatzResearch.WordTrace]
  refine ⟨51465075646025066893362265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68620100861366755857816353 51465075646025066893362265)
  ·
    refine ⟨38598806734518800170021699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51465075646025066893362265 38598806734518800170021699)
    ·
      refine ⟨57898210101778200255032549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38598806734518800170021699 57898210101778200255032549)
      ·
        refine ⟨10855914394083412547818603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57898210101778200255032549 10855914394083412547818603)
        ·
          refine ⟨16283871591125118821727905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10855914394083412547818603 16283871591125118821727905)
          ·
            refine ⟨12212903693343839116295929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16283871591125118821727905 12212903693343839116295929)
            ·
              refine ⟨9159677770007879337221947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12212903693343839116295929 9159677770007879337221947)
              ·
                refine ⟨13739516655011819005832921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9159677770007879337221947 13739516655011819005832921)
                ·
                  refine ⟨10304637491258864254374691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13739516655011819005832921 10304637491258864254374691)
                  ·
                    refine ⟨15456956236888296381562037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10304637491258864254374691 15456956236888296381562037)
                    ·
                      refine ⟨1449089647208277785771441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15456956236888296381562037 1449089647208277785771441)
                      ·
                        rfl

theorem cell23_2822092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_2822092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822092 prefixEnd_2822092 := by exact prefixLift 2822092
  have htrace : WordTrace (prefixWord ++ tailWord_2822092) baseStart_2822092 baseEnd_2822092 := by
    simpa [prefixWord, tailWord_2822092, baseEnd_2822092] using wordTrace_append hprefix tailTrace_2822092
  have hstable : (prefixWord ++ tailWord_2822092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822092).length < 2 ^ (prefixWord ++ tailWord_2822092).sum := by decide
  have hdescent : baseEnd_2822092 < baseStart_2822092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822119 : List Nat := [1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 4]
def baseStart_2822119 : Nat := 118140960795 + 2822119 * 2 ^ 59
def prefixEnd_2822119 : Nat := 4983230072969 + 3 ^ 40 * 2822119 * 2
def baseEnd_2822119 : Nat := 1449103511185949180133817

theorem tailTrace_2822119 : CollatzResearch.WordTrace tailWord_2822119 prefixEnd_2822119 1449103511185949180133817 := by
  unfold tailWord_2822119
  simp only [CollatzResearch.WordTrace]
  refine ⟨102931136062952317397957411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68620757375301544931971607 102931136062952317397957411)
  ·
    refine ⟨154396704094428476096936117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102931136062952317397957411 154396704094428476096936117)
    ·
      refine ⟨14474691008852669634087761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 154396704094428476096936117 14474691008852669634087761)
      ·
        refine ⟨10856018256639502225565821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14474691008852669634087761 10856018256639502225565821)
        ·
          refine ⟨4071006846239813334587183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10856018256639502225565821 4071006846239813334587183)
          ·
            refine ⟨6106510269359720001880775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4071006846239813334587183 6106510269359720001880775)
            ·
              refine ⟨9159765404039580002821163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6106510269359720001880775 9159765404039580002821163)
              ·
                refine ⟨13739648106059370004231745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9159765404039580002821163 13739648106059370004231745)
                ·
                  refine ⟨10304736079544527503173809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13739648106059370004231745 10304736079544527503173809)
                  ·
                    refine ⟨7728552059658395627380357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10304736079544527503173809 7728552059658395627380357)
                    ·
                      refine ⟨1449103511185949180133817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7728552059658395627380357 1449103511185949180133817)
                      ·
                        rfl

theorem cell23_2822119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_2822119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822119 prefixEnd_2822119 := by exact prefixLift 2822119
  have htrace : WordTrace (prefixWord ++ tailWord_2822119) baseStart_2822119 baseEnd_2822119 := by
    simpa [prefixWord, tailWord_2822119, baseEnd_2822119] using wordTrace_append hprefix tailTrace_2822119
  have hstable : (prefixWord ++ tailWord_2822119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822119).length < 2 ^ (prefixWord ++ tailWord_2822119).sum := by decide
  have hdescent : baseEnd_2822119 < baseStart_2822119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822135 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 5]
def baseStart_2822135 : Nat := 118140960795 + 2822135 * 2 ^ 59
def prefixEnd_2822135 : Nat := 4983230072969 + 3 ^ 40 * 2822135 * 2
def baseEnd_2822135 : Nat := 1449111726876421117533743

theorem tailTrace_2822135 : CollatzResearch.WordTrace tailWord_2822135 prefixEnd_2822135 1449111726876421117533743 := by
  unfold tailWord_2822135
  simp only [CollatzResearch.WordTrace]
  refine ⟨102931719630894352130539859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68621146420596234753693239 102931719630894352130539859)
  ·
    refine ⟨154397579446341528195809789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102931719630894352130539859 154397579446341528195809789)
    ·
      refine ⟨57899092292378073073428671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154397579446341528195809789 57899092292378073073428671)
      ·
        refine ⟨86848638438567109610143007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57899092292378073073428671 86848638438567109610143007)
        ·
          refine ⟨130272957657850664415214511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86848638438567109610143007 130272957657850664415214511)
          ·
            refine ⟨195409436486775996622821767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130272957657850664415214511 195409436486775996622821767)
            ·
              refine ⟨293114154730163994934232651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195409436486775996622821767 293114154730163994934232651)
              ·
                refine ⟨439671232095245992401348977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 293114154730163994934232651 439671232095245992401348977)
                ·
                  refine ⟨329753424071434494301011733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 439671232095245992401348977 329753424071434494301011733)
                  ·
                    refine ⟨15457191753348491920359925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 329753424071434494301011733 15457191753348491920359925)
                    ·
                      refine ⟨1449111726876421117533743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15457191753348491920359925 1449111726876421117533743)
                      ·
                        rfl

theorem cell23_2822135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_2822135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822135 prefixEnd_2822135 := by exact prefixLift 2822135
  have htrace : WordTrace (prefixWord ++ tailWord_2822135) baseStart_2822135 baseEnd_2822135 := by
    simpa [prefixWord, tailWord_2822135, baseEnd_2822135] using wordTrace_append hprefix tailTrace_2822135
  have hstable : (prefixWord ++ tailWord_2822135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822135).length < 2 ^ (prefixWord ++ tailWord_2822135).sum := by decide
  have hdescent : baseEnd_2822135 < baseStart_2822135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822157 : List Nat := [1, 7, 1, 2, 1, 1, 1, 1, 4, 2, 2]
def baseStart_2822157 : Nat := 118140960795 + 2822157 * 2 ^ 59
def prefixEnd_2822157 : Nat := 4983230072969 + 3 ^ 40 * 2822157 * 2
def baseEnd_2822157 : Nat := 1449123023450820031458643

theorem tailTrace_2822157 : CollatzResearch.WordTrace tailWord_2822157 prefixEnd_2822157 1449123023450820031458643 := by
  unfold tailWord_2822157
  simp only [CollatzResearch.WordTrace]
  refine ⟨102932522036814649887840725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68621681357876433258560483 102932522036814649887840725)
  ·
    refine ⟨2412480985237843356746267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 102932522036814649887840725 2412480985237843356746267)
    ·
      refine ⟨3618721477856765035119401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2412480985237843356746267 3618721477856765035119401)
      ·
        refine ⟨2714041108392573776339551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3618721477856765035119401 2714041108392573776339551)
        ·
          refine ⟨4071061662588860664509327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2714041108392573776339551 4071061662588860664509327)
          ·
            refine ⟨6106592493883290996763991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4071061662588860664509327 6106592493883290996763991)
            ·
              refine ⟨9159888740824936495145987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6106592493883290996763991 9159888740824936495145987)
              ·
                refine ⟨13739833111237404742718981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9159888740824936495145987 13739833111237404742718981)
                ·
                  refine ⟨2576218708357013389259809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13739833111237404742718981 2576218708357013389259809)
                  ·
                    refine ⟨1932164031267760041944857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2576218708357013389259809 1932164031267760041944857)
                    ·
                      refine ⟨1449123023450820031458643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1932164031267760041944857 1449123023450820031458643)
                      ·
                        rfl

theorem cell23_2822157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_2822157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822157 prefixEnd_2822157 := by exact prefixLift 2822157
  have htrace : WordTrace (prefixWord ++ tailWord_2822157) baseStart_2822157 baseEnd_2822157 := by
    simpa [prefixWord, tailWord_2822157, baseEnd_2822157] using wordTrace_append hprefix tailTrace_2822157
  have hstable : (prefixWord ++ tailWord_2822157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822157).length < 2 ^ (prefixWord ++ tailWord_2822157).sum := by decide
  have hdescent : baseEnd_2822157 < baseStart_2822157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822179 : List Nat := [1, 1, 1, 4, 3, 1, 1, 3, 2, 4, 2]
def baseStart_2822179 : Nat := 118140960795 + 2822179 * 2 ^ 59
def prefixEnd_2822179 : Nat := 4983230072969 + 3 ^ 40 * 2822179 * 2
def baseEnd_2822179 : Nat := 1449134320025218945383541

theorem tailTrace_2822179 : CollatzResearch.WordTrace tailWord_2822179 prefixEnd_2822179 1449134320025218945383541 := by
  unfold tailWord_2822179
  simp only [CollatzResearch.WordTrace]
  refine ⟨102933324442734947645141591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68622216295156631763427727 102933324442734947645141591)
  ·
    refine ⟨154399986664102421467712387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102933324442734947645141591 154399986664102421467712387)
    ·
      refine ⟨231599979996153632201568581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154399986664102421467712387 231599979996153632201568581)
      ·
        refine ⟨43424996249278806037794109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 231599979996153632201568581 43424996249278806037794109)
        ·
          refine ⟨16284373593479552264172791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43424996249278806037794109 16284373593479552264172791)
          ·
            refine ⟨24426560390219328396259187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16284373593479552264172791 24426560390219328396259187)
            ·
              refine ⟨36639840585328992594388781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24426560390219328396259187 36639840585328992594388781)
              ·
                refine ⟨13739940219498372222895793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36639840585328992594388781 13739940219498372222895793)
                ·
                  refine ⟨10304955164623779167171845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13739940219498372222895793 10304955164623779167171845)
                  ·
                    refine ⟨1932179093366958593844721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10304955164623779167171845 1932179093366958593844721)
                    ·
                      refine ⟨1449134320025218945383541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1932179093366958593844721 1449134320025218945383541)
                      ·
                        rfl

theorem cell23_2822179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 4, 2].length) (baseStart_2822179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822179 prefixEnd_2822179 := by exact prefixLift 2822179
  have htrace : WordTrace (prefixWord ++ tailWord_2822179) baseStart_2822179 baseEnd_2822179 := by
    simpa [prefixWord, tailWord_2822179, baseEnd_2822179] using wordTrace_append hprefix tailTrace_2822179
  have hstable : (prefixWord ++ tailWord_2822179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822179).length < 2 ^ (prefixWord ++ tailWord_2822179).sum := by decide
  have hdescent : baseEnd_2822179 < baseStart_2822179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822236 : List Nat := [2, 2, 4, 1, 1, 2, 4, 1, 6]
def baseStart_2822236 : Nat := 118140960795 + 2822236 * 2 ^ 59
def prefixEnd_2822236 : Nat := 4983230072969 + 3 ^ 40 * 2822236 * 2
def baseEnd_2822236 : Nat := 161018176491391691374531

theorem tailTrace_2822236 : CollatzResearch.WordTrace tailWord_2822236 prefixEnd_2822236 161018176491391691374531 := by
  unfold tailWord_2822236
  simp only [CollatzResearch.WordTrace]
  refine ⟨51467701701764223189983281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68623602269018964253311041 51467701701764223189983281)
  ·
    refine ⟨38600776276323167392487461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51467701701764223189983281 38600776276323167392487461)
    ·
      refine ⟨7237645551810593886091399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38600776276323167392487461 7237645551810593886091399)
      ·
        refine ⟨10856468327715890829137099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7237645551810593886091399 10856468327715890829137099)
        ·
          refine ⟨16284702491573836243705649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10856468327715890829137099 16284702491573836243705649)
          ·
            refine ⟨12213526868680377182779237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16284702491573836243705649 12213526868680377182779237)
            ·
              refine ⟨2290036287877570721771107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12213526868680377182779237 2290036287877570721771107)
              ·
                refine ⟨3435054431816356082656661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2290036287877570721771107 3435054431816356082656661)
                ·
                  refine ⟨161018176491391691374531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3435054431816356082656661 161018176491391691374531)
                  ·
                    rfl

theorem cell23_2822236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 6].length) (baseStart_2822236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822236 prefixEnd_2822236 := by exact prefixLift 2822236
  have htrace : WordTrace (prefixWord ++ tailWord_2822236) baseStart_2822236 baseEnd_2822236 := by
    simpa [prefixWord, tailWord_2822236, baseEnd_2822236] using wordTrace_append hprefix tailTrace_2822236
  have hstable : (prefixWord ++ tailWord_2822236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822236).length < 2 ^ (prefixWord ++ tailWord_2822236).sum := by decide
  have hdescent : baseEnd_2822236 < baseStart_2822236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822239 : List Nat := [1, 1, 2, 3, 1, 1, 2, 4, 1, 5, 2]
def baseStart_2822239 : Nat := 118140960795 + 2822239 * 2 ^ 59
def prefixEnd_2822239 : Nat := 4983230072969 + 3 ^ 40 * 2822239 * 2
def baseEnd_2822239 : Nat := 1449165128864488710633265

theorem tailTrace_2822239 : CollatzResearch.WordTrace tailWord_2822239 prefixEnd_2822239 1449165128864488710633265 := by
  unfold tailWord_2822239
  simp only [CollatzResearch.WordTrace]
  refine ⟨102935512822517577892325771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68623675215011718594883847 102935512822517577892325771)
  ·
    refine ⟨154403269233776366838488657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102935512822517577892325771 154403269233776366838488657)
    ·
      refine ⟨115802451925332275128866493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154403269233776366838488657 115802451925332275128866493)
      ·
        refine ⟨43425919471999603173324935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115802451925332275128866493 43425919471999603173324935)
        ·
          refine ⟨65138879207999404759987403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43425919471999603173324935 65138879207999404759987403)
          ·
            refine ⟨97708318811999107139981105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65138879207999404759987403 97708318811999107139981105)
            ·
              refine ⟨73281239108999330354985829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97708318811999107139981105 73281239108999330354985829)
              ·
                refine ⟨13740232332937374441559843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73281239108999330354985829 13740232332937374441559843)
                ·
                  refine ⟨20610348499406061662339765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13740232332937374441559843 20610348499406061662339765)
                  ·
                    refine ⟨1932220171819318280844353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20610348499406061662339765 1932220171819318280844353)
                    ·
                      refine ⟨1449165128864488710633265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1932220171819318280844353 1449165128864488710633265)
                      ·
                        rfl

theorem cell23_2822239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 5, 2].length) (baseStart_2822239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822239 prefixEnd_2822239 := by exact prefixLift 2822239
  have htrace : WordTrace (prefixWord ++ tailWord_2822239) baseStart_2822239 baseEnd_2822239 := by
    simpa [prefixWord, tailWord_2822239, baseEnd_2822239] using wordTrace_append hprefix tailTrace_2822239
  have hstable : (prefixWord ++ tailWord_2822239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822239).length < 2 ^ (prefixWord ++ tailWord_2822239).sum := by decide
  have hdescent : baseEnd_2822239 < baseStart_2822239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822256 : List Nat := [2, 1, 1, 1, 5, 2, 1, 3, 2, 3, 2]
def baseStart_2822256 : Nat := 118140960795 + 2822256 * 2 ^ 59
def prefixEnd_2822256 : Nat := 4983230072969 + 3 ^ 40 * 2822256 * 2
def baseEnd_2822256 : Nat := 1449173858035615144120687

theorem tailTrace_2822256 : CollatzResearch.WordTrace tailWord_2822256 prefixEnd_2822256 1449173858035615144120687 := by
  unfold tailWord_2822256
  simp only [CollatzResearch.WordTrace]
  refine ⟨51468066431727994897847311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68624088575637326530463081 51468066431727994897847311)
  ·
    refine ⟨77202099647591992346770967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51468066431727994897847311 77202099647591992346770967)
    ·
      refine ⟨115803149471387988520156451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77202099647591992346770967 115803149471387988520156451)
      ·
        refine ⟨173704724207081982780234677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115803149471387988520156451 173704724207081982780234677)
        ·
          refine ⟨16284817894413935885647001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 173704724207081982780234677 16284817894413935885647001)
          ·
            refine ⟨12213613420810451914235251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16284817894413935885647001 12213613420810451914235251)
            ·
              refine ⟨18320420131215677871352877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12213613420810451914235251 18320420131215677871352877)
              ·
                refine ⟨6870157549205879201757329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18320420131215677871352877 6870157549205879201757329)
                ·
                  refine ⟨5152618161904409401317997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6870157549205879201757329 5152618161904409401317997)
                  ·
                    refine ⟨1932231810714153525494249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5152618161904409401317997 1932231810714153525494249)
                    ·
                      refine ⟨1449173858035615144120687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1932231810714153525494249 1449173858035615144120687)
                      ·
                        rfl

theorem cell23_2822256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 2, 3, 2].length) (baseStart_2822256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822256 prefixEnd_2822256 := by exact prefixLift 2822256
  have htrace : WordTrace (prefixWord ++ tailWord_2822256) baseStart_2822256 baseEnd_2822256 := by
    simpa [prefixWord, tailWord_2822256, baseEnd_2822256] using wordTrace_append hprefix tailTrace_2822256
  have hstable : (prefixWord ++ tailWord_2822256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822256).length < 2 ^ (prefixWord ++ tailWord_2822256).sum := by decide
  have hdescent : baseEnd_2822256 < baseStart_2822256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822279 : List Nat := [1, 1, 4, 2, 1, 1, 2, 3, 4, 4]
def baseStart_2822279 : Nat := 118140960795 + 2822279 * 2 ^ 59
def prefixEnd_2822279 : Nat := 4983230072969 + 3 ^ 40 * 2822279 * 2
def baseEnd_2822279 : Nat := 483061889363556184711027

theorem tailTrace_2822279 : CollatzResearch.WordTrace tailWord_2822279 prefixEnd_2822279 483061889363556184711027 := by
  unfold tailWord_2822279
  simp only [CollatzResearch.WordTrace]
  refine ⟨102936971742372664723781891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68624647828248443149187927 102936971742372664723781891)
  ·
    refine ⟨154405457613558997085672837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102936971742372664723781891 154405457613558997085672837)
    ·
      refine ⟨28951023302542311953563657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154405457613558997085672837 28951023302542311953563657)
      ·
        refine ⟨21713267476906733965172743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28951023302542311953563657 21713267476906733965172743)
        ·
          refine ⟨32569901215360100947759115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21713267476906733965172743 32569901215360100947759115)
          ·
            refine ⟨48854851823040151421638673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32569901215360100947759115 48854851823040151421638673)
            ·
              refine ⟨36641138867280113566229005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48854851823040151421638673 36641138867280113566229005)
              ·
                refine ⟨13740427075230042587335877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36641138867280113566229005 13740427075230042587335877)
                ·
                  refine ⟨2576330076605632985125477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13740427075230042587335877 2576330076605632985125477)
                  ·
                    refine ⟨483061889363556184711027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2576330076605632985125477 483061889363556184711027)
                    ·
                      rfl

theorem cell23_2822279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_2822279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822279 prefixEnd_2822279 := by exact prefixLift 2822279
  have htrace : WordTrace (prefixWord ++ tailWord_2822279) baseStart_2822279 baseEnd_2822279 := by
    simpa [prefixWord, tailWord_2822279, baseEnd_2822279] using wordTrace_append hprefix tailTrace_2822279
  have hstable : (prefixWord ++ tailWord_2822279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822279).length < 2 ^ (prefixWord ++ tailWord_2822279).sum := by decide
  have hdescent : baseEnd_2822279 < baseStart_2822279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822280 : List Nat := [2, 1, 3, 4, 1, 2, 1, 4, 1, 1, 3]
def baseStart_2822280 : Nat := 118140960795 + 2822280 * 2 ^ 59
def prefixEnd_2822280 : Nat := 4983230072969 + 3 ^ 40 * 2822280 * 2
def baseEnd_2822280 : Nat := 1449186181571323050220577

theorem tailTrace_2822280 : CollatzResearch.WordTrace tailWord_2822280 prefixEnd_2822280 1449186181571323050220577 := by
  unfold tailWord_2822280
  simp only [CollatzResearch.WordTrace]
  refine ⟨51468504107684520947284147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68624672143579361263045529 51468504107684520947284147)
  ·
    refine ⟨77202756161526781420926221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51468504107684520947284147 77202756161526781420926221)
    ·
      refine ⟨28951033560572543032847333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77202756161526781420926221 28951033560572543032847333)
      ·
        refine ⟨5428318792607351818658875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28951033560572543032847333 5428318792607351818658875)
        ·
          refine ⟨8142478188911027727988313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5428318792607351818658875 8142478188911027727988313)
          ·
            refine ⟨6106858641683270795991235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8142478188911027727988313 6106858641683270795991235)
            ·
              refine ⟨9160287962524906193986853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6106858641683270795991235 9160287962524906193986853)
              ·
                refine ⟨1717553992973419911372535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9160287962524906193986853 1717553992973419911372535)
                ·
                  refine ⟨2576330989460129867058803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1717553992973419911372535 2576330989460129867058803)
                  ·
                    refine ⟨3864496484190194800588205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2576330989460129867058803 3864496484190194800588205)
                    ·
                      refine ⟨1449186181571323050220577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3864496484190194800588205 1449186181571323050220577)
                      ·
                        rfl

theorem cell23_2822280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_2822280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822280 prefixEnd_2822280 := by exact prefixLift 2822280
  have htrace : WordTrace (prefixWord ++ tailWord_2822280) baseStart_2822280 baseEnd_2822280 := by
    simpa [prefixWord, tailWord_2822280, baseEnd_2822280] using wordTrace_append hprefix tailTrace_2822280
  have hstable : (prefixWord ++ tailWord_2822280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822280).length < 2 ^ (prefixWord ++ tailWord_2822280).sum := by decide
  have hdescent : baseEnd_2822280 < baseStart_2822280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822296 : List Nat := [2, 1, 2, 4, 3, 1, 2, 1, 1, 6]
def baseStart_2822296 : Nat := 118140960795 + 2822296 * 2 ^ 59
def prefixEnd_2822296 : Nat := 4983230072969 + 3 ^ 40 * 2822296 * 2
def baseEnd_2822296 : Nat := 483064799087264995873501

theorem tailTrace_2822296 : CollatzResearch.WordTrace tailWord_2822296 prefixEnd_2822296 483064799087264995873501 := by
  unfold tailWord_2822296
  simp only [CollatzResearch.WordTrace]
  refine ⟨51468795891655538313575371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68625061188874051084767161 51468795891655538313575371)
  ·
    refine ⟨77203193837483307470363057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51468795891655538313575371 77203193837483307470363057)
    ·
      refine ⟨57902395378112480602772293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77203193837483307470363057 57902395378112480602772293)
      ·
        refine ⟨10856699133396090113019805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57902395378112480602772293 10856699133396090113019805)
        ·
          refine ⟨4071262175023533792382427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10856699133396090113019805 4071262175023533792382427)
          ·
            refine ⟨6106893262535300688573641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4071262175023533792382427 6106893262535300688573641)
            ·
              refine ⟨4580169946901475516430231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6106893262535300688573641 4580169946901475516430231)
              ·
                refine ⟨6870254920352213274645347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4580169946901475516430231 6870254920352213274645347)
                ·
                  refine ⟨10305382380528319911968021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6870254920352213274645347 10305382380528319911968021)
                  ·
                    refine ⟨483064799087264995873501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10305382380528319911968021 483064799087264995873501)
                    ·
                      rfl

theorem cell23_2822296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 1, 6].length) (baseStart_2822296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822296 prefixEnd_2822296 := by exact prefixLift 2822296
  have htrace : WordTrace (prefixWord ++ tailWord_2822296) baseStart_2822296 baseEnd_2822296 := by
    simpa [prefixWord, tailWord_2822296, baseEnd_2822296] using wordTrace_append hprefix tailTrace_2822296
  have hstable : (prefixWord ++ tailWord_2822296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822296).length < 2 ^ (prefixWord ++ tailWord_2822296).sum := by decide
  have hdescent : baseEnd_2822296 < baseStart_2822296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822303 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 5, 2, 2]
def baseStart_2822303 : Nat := 118140960795 + 2822303 * 2 ^ 59
def prefixEnd_2822303 : Nat := 4983230072969 + 3 ^ 40 * 2822303 * 2
def baseEnd_2822303 : Nat := 1449197991626376460232971

theorem tailTrace_2822303 : CollatzResearch.WordTrace tailWord_2822303 prefixEnd_2822303 1449197991626376460232971 := by
  unfold tailWord_2822303
  simp only [CollatzResearch.WordTrace]
  refine ⟨102937847094285716822655563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68625231396190477881770375 102937847094285716822655563)
  ·
    refine ⟨154406770641428575233983345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102937847094285716822655563 154406770641428575233983345)
    ·
      refine ⟨115805077981071431425487509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154406770641428575233983345 115805077981071431425487509)
      ·
        refine ⟨5428363030362723348069727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 115805077981071431425487509 5428363030362723348069727)
        ·
          refine ⟨8142544545544085022104591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5428363030362723348069727 8142544545544085022104591)
          ·
            refine ⟨12213816818316127533156887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8142544545544085022104591 12213816818316127533156887)
            ·
              refine ⟨18320725227474191299735331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12213816818316127533156887 18320725227474191299735331)
              ·
                refine ⟨27481087841211286949602997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18320725227474191299735331 27481087841211286949602997)
                ·
                  refine ⟨2576351985113558151525281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27481087841211286949602997 2576351985113558151525281)
                  ·
                    refine ⟨1932263988835168613643961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2576351985113558151525281 1932263988835168613643961)
                    ·
                      refine ⟨1449197991626376460232971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1932263988835168613643961 1449197991626376460232971)
                      ·
                        rfl

theorem cell23_2822303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_2822303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822303 prefixEnd_2822303 := by exact prefixLift 2822303
  have htrace : WordTrace (prefixWord ++ tailWord_2822303) baseStart_2822303 baseEnd_2822303 := by
    simpa [prefixWord, tailWord_2822303, baseEnd_2822303] using wordTrace_append hprefix tailTrace_2822303
  have hstable : (prefixWord ++ tailWord_2822303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822303).length < 2 ^ (prefixWord ++ tailWord_2822303).sum := by decide
  have hdescent : baseEnd_2822303 < baseStart_2822303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822309 : List Nat := [1, 3, 1, 2, 1, 3, 5, 7]
def baseStart_2822309 : Nat := 118140960795 + 2822309 * 2 ^ 59
def prefixEnd_2822309 : Nat := 4983230072969 + 3 ^ 40 * 2822309 * 2
def baseEnd_2822309 : Nat := 53674113796677905065109

theorem tailTrace_2822309 : CollatzResearch.WordTrace tailWord_2822309 prefixEnd_2822309 53674113796677905065109 := by
  unfold tailWord_2822309
  simp only [CollatzResearch.WordTrace]
  refine ⟨102938065932263979847373981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68625377288175986564915987 102938065932263979847373981)
  ·
    refine ⟨38601774724598992442765243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102938065932263979847373981 38601774724598992442765243)
    ·
      refine ⟨57902662086898488664147865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38601774724598992442765243 57902662086898488664147865)
      ·
        refine ⟨43426996565173866498110899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57902662086898488664147865 43426996565173866498110899)
        ·
          refine ⟨65140494847760799747166349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43426996565173866498110899 65140494847760799747166349)
          ·
            refine ⟨24427685567910299905187381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65140494847760799747166349 24427685567910299905187381)
            ·
              refine ⟨2290095521991590616111317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24427685567910299905187381 2290095521991590616111317)
              ·
                refine ⟨53674113796677905065109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2290095521991590616111317 53674113796677905065109)
                ·
                  rfl

theorem cell23_2822309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 7].length) (baseStart_2822309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822309 prefixEnd_2822309 := by exact prefixLift 2822309
  have htrace : WordTrace (prefixWord ++ tailWord_2822309) baseStart_2822309 baseEnd_2822309 := by
    simpa [prefixWord, tailWord_2822309, baseEnd_2822309] using wordTrace_append hprefix tailTrace_2822309
  have hstable : (prefixWord ++ tailWord_2822309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822309).length < 2 ^ (prefixWord ++ tailWord_2822309).sum := by decide
  have hdescent : baseEnd_2822309 < baseStart_2822309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822337 : List Nat := [1, 2, 6, 1, 2, 1, 2, 1, 3, 2, 2]
def baseStart_2822337 : Nat := 118140960795 + 2822337 * 2 ^ 59
def prefixEnd_2822337 : Nat := 4983230072969 + 3 ^ 40 * 2822337 * 2
def baseEnd_2822337 : Nat := 1449215449968629327207815

theorem tailTrace_2822337 : CollatzResearch.WordTrace tailWord_2822337 prefixEnd_2822337 1449215449968629327207815 := by
  unfold tailWord_2822337
  simp only [CollatzResearch.WordTrace]
  refine ⟨102939087176162540629393265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68626058117441693752928843 102939087176162540629393265)
  ·
    refine ⟨77204315382121905472044949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102939087176162540629393265 77204315382121905472044949)
    ·
      refine ⟨3618952283536964319002107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 77204315382121905472044949 3618952283536964319002107)
      ·
        refine ⟨5428428425305446478503161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3618952283536964319002107 5428428425305446478503161)
        ·
          refine ⟨4071321318979084858877371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5428428425305446478503161 4071321318979084858877371)
          ·
            refine ⟨6106981978468627288316057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4071321318979084858877371 6106981978468627288316057)
            ·
              refine ⟨4580236483851470466237043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6106981978468627288316057 4580236483851470466237043)
              ·
                refine ⟨6870354725777205699355565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4580236483851470466237043 6870354725777205699355565)
                ·
                  refine ⟨2576383022166452137258337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6870354725777205699355565 2576383022166452137258337)
                  ·
                    refine ⟨1932287266624839102943753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2576383022166452137258337 1932287266624839102943753)
                    ·
                      refine ⟨1449215449968629327207815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1932287266624839102943753 1449215449968629327207815)
                      ·
                        rfl

theorem cell23_2822337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_2822337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822337 prefixEnd_2822337 := by exact prefixLift 2822337
  have htrace : WordTrace (prefixWord ++ tailWord_2822337) baseStart_2822337 baseEnd_2822337 := by
    simpa [prefixWord, tailWord_2822337, baseEnd_2822337] using wordTrace_append hprefix tailTrace_2822337
  have hstable : (prefixWord ++ tailWord_2822337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822337).length < 2 ^ (prefixWord ++ tailWord_2822337).sum := by decide
  have hdescent : baseEnd_2822337 < baseStart_2822337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822371 : List Nat := [1, 1, 1, 8, 2, 1, 1, 3, 1, 2, 2]
def baseStart_2822371 : Nat := 118140960795 + 2822371 * 2 ^ 59
def prefixEnd_2822371 : Nat := 4983230072969 + 3 ^ 40 * 2822371 * 2
def baseEnd_2822371 : Nat := 1449232908310882194182659

theorem tailTrace_2822371 : CollatzResearch.WordTrace tailWord_2822371 prefixEnd_2822371 1449232908310882194182659 := by
  unfold tailWord_2822371
  simp only [CollatzResearch.WordTrace]
  refine ⟨102940327258039364436130967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68626884838692909624087311 102940327258039364436130967)
  ·
    refine ⟨154410490887059046654196451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102940327258039364436130967 154410490887059046654196451)
    ·
      refine ⟨231615736330588569981294677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154410490887059046654196451 231615736330588569981294677)
      ·
        refine ⟨2714246910124084804468297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 231615736330588569981294677 2714246910124084804468297)
        ·
          refine ⟨2035685182593063603351223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2714246910124084804468297 2035685182593063603351223)
          ·
            refine ⟨3053527773889595405026835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2035685182593063603351223 3053527773889595405026835)
            ·
              refine ⟨4580291660834393107540253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3053527773889595405026835 4580291660834393107540253)
              ·
                refine ⟨1717609372812897415327595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4580291660834393107540253 1717609372812897415327595)
                ·
                  refine ⟨2576414059219346122991393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1717609372812897415327595 2576414059219346122991393)
                  ·
                    refine ⟨1932310544414509592243545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2576414059219346122991393 1932310544414509592243545)
                    ·
                      refine ⟨1449232908310882194182659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1932310544414509592243545 1449232908310882194182659)
                      ·
                        rfl

theorem cell23_2822371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_2822371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822371 prefixEnd_2822371 := by exact prefixLift 2822371
  have htrace : WordTrace (prefixWord ++ tailWord_2822371) baseStart_2822371 baseEnd_2822371 := by
    simpa [prefixWord, tailWord_2822371, baseEnd_2822371] using wordTrace_append hprefix tailTrace_2822371
  have hstable : (prefixWord ++ tailWord_2822371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822371).length < 2 ^ (prefixWord ++ tailWord_2822371).sum := by decide
  have hdescent : baseEnd_2822371 < baseStart_2822371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822379 : List Nat := [1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 5]
def baseStart_2822379 : Nat := 118140960795 + 2822379 * 2 ^ 59
def prefixEnd_2822379 : Nat := 4983230072969 + 3 ^ 40 * 2822379 * 2
def baseEnd_2822379 : Nat := 1449237016156118162882621

theorem tailTrace_2822379 : CollatzResearch.WordTrace tailWord_2822379 prefixEnd_2822379 1449237016156118162882621 := by
  unfold tailWord_2822379
  simp only [CollatzResearch.WordTrace]
  refine ⟨102940619042010381802422191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68627079361340254534948127 102940619042010381802422191)
  ·
    refine ⟨154410928563015572703633287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102940619042010381802422191 154410928563015572703633287)
    ·
      refine ⟨231616392844523359055449931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154410928563015572703633287 231616392844523359055449931)
      ·
        refine ⟨347424589266785038583174897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231616392844523359055449931 347424589266785038583174897)
        ·
          refine ⟨260568441950088778937381173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347424589266785038583174897 260568441950088778937381173)
          ·
            refine ⟨24428291432820823025379485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 260568441950088778937381173 24428291432820823025379485)
            ·
              refine ⟨9160609287307808634517307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24428291432820823025379485 9160609287307808634517307)
              ·
                refine ⟨13740913930961712951775961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9160609287307808634517307 13740913930961712951775961)
                ·
                  refine ⟨10305685448221284713831971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13740913930961712951775961 10305685448221284713831971)
                  ·
                    refine ⟨15458528172331927070747957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10305685448221284713831971 15458528172331927070747957)
                    ·
                      refine ⟨1449237016156118162882621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15458528172331927070747957 1449237016156118162882621)
                      ·
                        rfl

theorem cell23_2822379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 5].length) (baseStart_2822379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822379 prefixEnd_2822379 := by exact prefixLift 2822379
  have htrace : WordTrace (prefixWord ++ tailWord_2822379) baseStart_2822379 baseEnd_2822379 := by
    simpa [prefixWord, tailWord_2822379, baseEnd_2822379] using wordTrace_append hprefix tailTrace_2822379
  have hstable : (prefixWord ++ tailWord_2822379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822379).length < 2 ^ (prefixWord ++ tailWord_2822379).sum := by decide
  have hdescent : baseEnd_2822379 < baseStart_2822379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822404 : List Nat := [2, 3, 2, 2, 4, 1, 2, 1, 2, 1, 3]
def baseStart_2822404 : Nat := 118140960795 + 2822404 * 2 ^ 59
def prefixEnd_2822404 : Nat := 4983230072969 + 3 ^ 40 * 2822404 * 2
def baseEnd_2822404 : Nat := 1449249853172480565070007

theorem tailTrace_2822404 : CollatzResearch.WordTrace tailWord_2822404 prefixEnd_2822404 1449249853172480565070007 := by
  unfold tailWord_2822404
  simp only [CollatzResearch.WordTrace]
  refine ⟨51470765433459905536041133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68627687244613207381388177 51470765433459905536041133)
  ·
    refine ⟨19301537037547464576015425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51470765433459905536041133 19301537037547464576015425)
    ·
      refine ⟨14476152778160598432011569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19301537037547464576015425 14476152778160598432011569)
      ·
        refine ⟨10857114583620448824008677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14476152778160598432011569 10857114583620448824008677)
        ·
          refine ⟨2035708984428834154501627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10857114583620448824008677 2035708984428834154501627)
          ·
            refine ⟨3053563476643251231752441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2035708984428834154501627 3053563476643251231752441)
            ·
              refine ⟨2290172607482438423814331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3053563476643251231752441 2290172607482438423814331)
              ·
                refine ⟨3435258911223657635721497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2290172607482438423814331 3435258911223657635721497)
                ·
                  refine ⟨2576444183417743226791123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3435258911223657635721497 2576444183417743226791123)
                  ·
                    refine ⟨3864666275126614840186685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2576444183417743226791123 3864666275126614840186685)
                    ·
                      refine ⟨1449249853172480565070007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3864666275126614840186685 1449249853172480565070007)
                      ·
                        rfl

theorem cell23_2822404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_2822404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822404 prefixEnd_2822404 := by exact prefixLift 2822404
  have htrace : WordTrace (prefixWord ++ tailWord_2822404) baseStart_2822404 baseEnd_2822404 := by
    simpa [prefixWord, tailWord_2822404, baseEnd_2822404] using wordTrace_append hprefix tailTrace_2822404
  have hstable : (prefixWord ++ tailWord_2822404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822404).length < 2 ^ (prefixWord ++ tailWord_2822404).sum := by decide
  have hdescent : baseEnd_2822404 < baseStart_2822404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822479 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 4]
def baseStart_2822479 : Nat := 118140960795 + 2822479 * 2 ^ 59
def prefixEnd_2822479 : Nat := 4983230072969 + 3 ^ 40 * 2822479 * 2
def baseEnd_2822479 : Nat := 1449288364221567771632161

theorem tailTrace_2822479 : CollatzResearch.WordTrace tailWord_2822479 prefixEnd_2822479 1449288364221567771632161 := by
  unfold tailWord_2822479
  simp only [CollatzResearch.WordTrace]
  refine ⟨102944266341648098881062491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68629510894432065920708327 102944266341648098881062491)
  ·
    refine ⟨154416399512472148321593737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102944266341648098881062491 154416399512472148321593737)
    ·
      refine ⟨115812299634354111241195303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154416399512472148321593737 115812299634354111241195303)
      ·
        refine ⟨173718449451531166861792955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115812299634354111241195303 173718449451531166861792955)
        ·
          refine ⟨260577674177296750292689433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173718449451531166861792955 260577674177296750292689433)
          ·
            refine ⟨195433255632972562719517075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260577674177296750292689433 195433255632972562719517075)
            ·
              refine ⟨293149883449458844079275613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195433255632972562719517075 293149883449458844079275613)
              ·
                refine ⟨109931206293547066529728355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 293149883449458844079275613 109931206293547066529728355)
                ·
                  refine ⟨164896809440320599794592533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109931206293547066529728355 164896809440320599794592533)
                  ·
                    refine ⟨7729537942515028115371525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 164896809440320599794592533 7729537942515028115371525)
                    ·
                      refine ⟨1449288364221567771632161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7729537942515028115371525 1449288364221567771632161)
                      ·
                        rfl

theorem cell23_2822479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 4].length) (baseStart_2822479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822479 prefixEnd_2822479 := by exact prefixLift 2822479
  have htrace : WordTrace (prefixWord ++ tailWord_2822479) baseStart_2822479 baseEnd_2822479 := by
    simpa [prefixWord, tailWord_2822479, baseEnd_2822479] using wordTrace_append hprefix tailTrace_2822479
  have hstable : (prefixWord ++ tailWord_2822479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822479).length < 2 ^ (prefixWord ++ tailWord_2822479).sum := by decide
  have hdescent : baseEnd_2822479 < baseStart_2822479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822489 : List Nat := [1, 2, 1, 2, 2, 2, 1, 4, 8]
def baseStart_2822489 : Nat := 118140960795 + 2822489 * 2 ^ 59
def prefixEnd_2822489 : Nat := 4983230072969 + 3 ^ 40 * 2822489 * 2
def baseEnd_2822489 : Nat := 161032611003123636945235

theorem tailTrace_2822489 : CollatzResearch.WordTrace tailWord_2822489 prefixEnd_2822489 161032611003123636945235 := by
  unfold tailWord_2822489
  simp only [CollatzResearch.WordTrace]
  refine ⟨102944631071611870588926521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68629754047741247059284347 102944631071611870588926521)
  ·
    refine ⟨77208473303708902941694891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102944631071611870588926521 77208473303708902941694891)
    ·
      refine ⟨115812709955563354412542337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77208473303708902941694891 115812709955563354412542337)
      ·
        refine ⟨86859532466672515809406753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115812709955563354412542337 86859532466672515809406753)
        ·
          refine ⟨65144649350004386857055065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86859532466672515809406753 65144649350004386857055065)
          ·
            refine ⟨48858487012503290142791299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65144649350004386857055065 48858487012503290142791299)
            ·
              refine ⟨73287730518754935214186949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48858487012503290142791299 73287730518754935214186949)
              ·
                refine ⟨13741449472266550352660053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73287730518754935214186949 13741449472266550352660053)
                ·
                  refine ⟨161032611003123636945235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13741449472266550352660053 161032611003123636945235)
                  ·
                    rfl

theorem cell23_2822489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 8].length) (baseStart_2822489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822489 prefixEnd_2822489 := by exact prefixLift 2822489
  have htrace : WordTrace (prefixWord ++ tailWord_2822489) baseStart_2822489 baseEnd_2822489 := by
    simpa [prefixWord, tailWord_2822489, baseEnd_2822489] using wordTrace_append hprefix tailTrace_2822489
  have hstable : (prefixWord ++ tailWord_2822489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822489).length < 2 ^ (prefixWord ++ tailWord_2822489).sum := by decide
  have hdescent : baseEnd_2822489 < baseStart_2822489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822519 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 2, 9]
def baseStart_2822519 : Nat := 118140960795 + 2822519 * 2 ^ 59
def prefixEnd_2822519 : Nat := 4983230072969 + 3 ^ 40 * 2822519 * 2
def baseEnd_2822519 : Nat := 483102967815915871710659

theorem tailTrace_2822519 : CollatzResearch.WordTrace tailWord_2822519 prefixEnd_2822519 483102967815915871710659 := by
  unfold tailWord_2822519
  simp only [CollatzResearch.WordTrace]
  refine ⟨102945725261503185712518611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68630483507668790475012407 102945725261503185712518611)
  ·
    refine ⟨154418587892254778568777917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102945725261503185712518611 154418587892254778568777917)
    ·
      refine ⟨57906970459595541963291719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154418587892254778568777917 57906970459595541963291719)
      ·
        refine ⟨86860455689393312944937579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57906970459595541963291719 86860455689393312944937579)
        ·
          refine ⟨130290683534089969417406369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86860455689393312944937579 130290683534089969417406369)
          ·
            refine ⟨97718012650567477063054777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130290683534089969417406369 97718012650567477063054777)
            ·
              refine ⟨73288509487925607797291083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97718012650567477063054777 73288509487925607797291083)
              ·
                refine ⟨109932764231888411695936625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73288509487925607797291083 109932764231888411695936625)
                ·
                  refine ⟨82449573173916308771952469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109932764231888411695936625 82449573173916308771952469)
                  ·
                    refine ⟨483102967815915871710659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 82449573173916308771952469 483102967815915871710659)
                    ·
                      rfl

theorem cell23_2822519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 9].length) (baseStart_2822519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822519 prefixEnd_2822519 := by exact prefixLift 2822519
  have htrace : WordTrace (prefixWord ++ tailWord_2822519) baseStart_2822519 baseEnd_2822519 := by
    simpa [prefixWord, tailWord_2822519, baseEnd_2822519] using wordTrace_append hprefix tailTrace_2822519
  have hstable : (prefixWord ++ tailWord_2822519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822519).length < 2 ^ (prefixWord ++ tailWord_2822519).sum := by decide
  have hdescent : baseEnd_2822519 < baseStart_2822519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822523 : List Nat := [1, 1, 1, 1, 1, 8, 3, 1, 6]
def baseStart_2822523 : Nat := 118140960795 + 2822523 * 2 ^ 59
def prefixEnd_2822523 : Nat := 4983230072969 + 3 ^ 40 * 2822523 * 2
def baseEnd_2822523 : Nat := 161034550818929511053551

theorem tailTrace_2822523 : CollatzResearch.WordTrace tailWord_2822523 prefixEnd_2822523 161034550818929511053551 := by
  unfold tailWord_2822523
  simp only [CollatzResearch.WordTrace]
  refine ⟨102945871153488694395664223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68630580768992462930442815 102945871153488694395664223)
  ·
    refine ⟨154418806730233041593496335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102945871153488694395664223 154418806730233041593496335)
    ·
      refine ⟨231628210095349562390244503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154418806730233041593496335 231628210095349562390244503)
      ·
        refine ⟨347442315143024343585366755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231628210095349562390244503 347442315143024343585366755)
        ·
          refine ⟨521163472714536515378050133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347442315143024343585366755 521163472714536515378050133)
          ·
            refine ⟨6107384445873474789586525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 521163472714536515378050133 6107384445873474789586525)
            ·
              refine ⟨2290269167202553046094947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6107384445873474789586525 2290269167202553046094947)
              ·
                refine ⟨3435403750803829569142421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2290269167202553046094947 3435403750803829569142421)
                ·
                  refine ⟨161034550818929511053551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3435403750803829569142421 161034550818929511053551)
                  ·
                    rfl

theorem cell23_2822523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 6].length) (baseStart_2822523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822523 prefixEnd_2822523 := by exact prefixLift 2822523
  have htrace : WordTrace (prefixWord ++ tailWord_2822523) baseStart_2822523 baseEnd_2822523 := by
    simpa [prefixWord, tailWord_2822523, baseEnd_2822523] using wordTrace_append hprefix tailTrace_2822523
  have hstable : (prefixWord ++ tailWord_2822523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822523).length < 2 ^ (prefixWord ++ tailWord_2822523).sum := by decide
  have hdescent : baseEnd_2822523 < baseStart_2822523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822560 : List Nat := [2, 1, 1, 4, 1, 4, 1, 2, 2, 3, 2]
def baseStart_2822560 : Nat := 118140960795 + 2822560 * 2 ^ 59
def prefixEnd_2822560 : Nat := 4983230072969 + 3 ^ 40 * 2822560 * 2
def baseEnd_2822560 : Nat := 1449329956154581954719289

theorem tailTrace_2822560 : CollatzResearch.WordTrace tailWord_2822560 prefixEnd_2822560 1449329956154581954719289 := by
  unfold tailWord_2822560
  simp only [CollatzResearch.WordTrace]
  refine ⟨51473610327177324857380567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68631480436236433143174089 51473610327177324857380567)
  ·
    refine ⟨77210415490765987286070851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51473610327177324857380567 77210415490765987286070851)
    ·
      refine ⟨115815623236148980929106277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77210415490765987286070851 115815623236148980929106277)
      ·
        refine ⟨21715429356777933924207427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115815623236148980929106277 21715429356777933924207427)
        ·
          refine ⟨32573144035166900886311141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21715429356777933924207427 32573144035166900886311141)
          ·
            refine ⟨6107464506593793916183339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32573144035166900886311141 6107464506593793916183339)
            ·
              refine ⟨9161196759890690874275009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6107464506593793916183339 9161196759890690874275009)
              ·
                refine ⟨6870897569918018155706257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9161196759890690874275009 6870897569918018155706257)
                ·
                  refine ⟨5153173177438513616779693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6870897569918018155706257 5153173177438513616779693)
                  ·
                    refine ⟨1932439941539442606292385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5153173177438513616779693 1932439941539442606292385)
                    ·
                      refine ⟨1449329956154581954719289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1932439941539442606292385 1449329956154581954719289)
                      ·
                        rfl

theorem cell23_2822560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_2822560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822560 prefixEnd_2822560 := by exact prefixLift 2822560
  have htrace : WordTrace (prefixWord ++ tailWord_2822560) baseStart_2822560 baseEnd_2822560 := by
    simpa [prefixWord, tailWord_2822560, baseEnd_2822560] using wordTrace_append hprefix tailTrace_2822560
  have hstable : (prefixWord ++ tailWord_2822560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822560).length < 2 ^ (prefixWord ++ tailWord_2822560).sum := by decide
  have hdescent : baseEnd_2822560 < baseStart_2822560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822567 : List Nat := [1, 1, 6, 1, 1, 4, 1, 1, 3, 1, 3]
def baseStart_2822567 : Nat := 118140960795 + 2822567 * 2 ^ 59
def prefixEnd_2822567 : Nat := 4983230072969 + 3 ^ 40 * 2822567 * 2
def baseEnd_2822567 : Nat := 1449333550519163427331757

theorem tailTrace_2822567 : CollatzResearch.WordTrace tailWord_2822567 prefixEnd_2822567 1449333550519163427331757 := by
  unfold tailWord_2822567
  simp only [CollatzResearch.WordTrace]
  refine ⟨102947475965329289910265955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68631650643552859940177303 102947475965329289910265955)
  ·
    refine ⟨154421213947993934865398933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102947475965329289910265955 154421213947993934865398933)
    ·
      refine ⟨7238494403812215696815575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 154421213947993934865398933 7238494403812215696815575)
      ·
        refine ⟨10857741605718323545223363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7238494403812215696815575 10857741605718323545223363)
        ·
          refine ⟨16286612408577485317835045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10857741605718323545223363 16286612408577485317835045)
          ·
            refine ⟨3053739826608278497094071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16286612408577485317835045 3053739826608278497094071)
            ·
              refine ⟨4580609739912417745641107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3053739826608278497094071 4580609739912417745641107)
              ·
                refine ⟨6870914609868626618461661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4580609739912417745641107 6870914609868626618461661)
                ·
                  refine ⟨2576592978700734981923123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6870914609868626618461661 2576592978700734981923123)
                  ·
                    refine ⟨3864889468051102472884685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2576592978700734981923123 3864889468051102472884685)
                    ·
                      refine ⟨1449333550519163427331757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3864889468051102472884685 1449333550519163427331757)
                      ·
                        rfl

theorem cell23_2822567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_2822567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822567 prefixEnd_2822567 := by exact prefixLift 2822567
  have htrace : WordTrace (prefixWord ++ tailWord_2822567) baseStart_2822567 baseEnd_2822567 := by
    simpa [prefixWord, tailWord_2822567, baseEnd_2822567] using wordTrace_append hprefix tailTrace_2822567
  have hstable : (prefixWord ++ tailWord_2822567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822567).length < 2 ^ (prefixWord ++ tailWord_2822567).sum := by decide
  have hdescent : baseEnd_2822567 < baseStart_2822567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822586 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 5, 2, 4]
def baseStart_2822586 : Nat := 118140960795 + 2822586 * 2 ^ 59
def prefixEnd_2822586 : Nat := 4983230072969 + 3 ^ 40 * 2822586 * 2
def baseEnd_2822586 : Nat := 1449343306651598852994169

theorem tailTrace_2822586 : CollatzResearch.WordTrace tailWord_2822586 prefixEnd_2822586 1449343306651598852994169 := by
  unfold tailWord_2822586
  simp only [CollatzResearch.WordTrace]
  refine ⟨25737042238065114038801903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68632112634840304103471741 25737042238065114038801903)
  ·
    refine ⟨38605563357097671058202855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25737042238065114038801903 38605563357097671058202855)
    ·
      refine ⟨57908345035646506587304283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38605563357097671058202855 57908345035646506587304283)
      ·
        refine ⟨86862517553469759880956425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57908345035646506587304283 86862517553469759880956425)
        ·
          refine ⟨65146888165102319910717319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86862517553469759880956425 65146888165102319910717319)
          ·
            refine ⟨97720332247653479866075979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65146888165102319910717319 97720332247653479866075979)
            ·
              refine ⟨146580498371480219799113969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97720332247653479866075979 146580498371480219799113969)
              ·
                refine ⟨109935373778610164849335477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146580498371480219799113969 109935373778610164849335477)
                ·
                  refine ⟨10306441291744702954625201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109935373778610164849335477 10306441291744702954625201)
                  ·
                    refine ⟨7729830968808527215968901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10306441291744702954625201 7729830968808527215968901)
                    ·
                      refine ⟨1449343306651598852994169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7729830968808527215968901 1449343306651598852994169)
                      ·
                        rfl

theorem cell23_2822586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_2822586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822586 prefixEnd_2822586 := by exact prefixLift 2822586
  have htrace : WordTrace (prefixWord ++ tailWord_2822586) baseStart_2822586 baseEnd_2822586 := by
    simpa [prefixWord, tailWord_2822586, baseEnd_2822586] using wordTrace_append hprefix tailTrace_2822586
  have hstable : (prefixWord ++ tailWord_2822586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822586).length < 2 ^ (prefixWord ++ tailWord_2822586).sum := by decide
  have hdescent : baseEnd_2822586 < baseStart_2822586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822590 : List Nat := [4, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4]
def baseStart_2822590 : Nat := 118140960795 + 2822590 * 2 ^ 59
def prefixEnd_2822590 : Nat := 4983230072969 + 3 ^ 40 * 2822590 * 2
def baseEnd_2822590 : Nat := 1449345360574216837344151

theorem tailTrace_2822590 : CollatzResearch.WordTrace tailWord_2822590 prefixEnd_2822590 1449345360574216837344151 := by
  unfold tailWord_2822590
  simp only [CollatzResearch.WordTrace]
  refine ⟨12868539355530745604794153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68632209896163976558902149 12868539355530745604794153)
  ·
    refine ⟨9651404516648059203595615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12868539355530745604794153 9651404516648059203595615)
    ·
      refine ⟨14477106774972088805393423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9651404516648059203595615 14477106774972088805393423)
      ·
        refine ⟨21715660162458133208090135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14477106774972088805393423 21715660162458133208090135)
        ·
          refine ⟨32573490243687199812135203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21715660162458133208090135 32573490243687199812135203)
          ·
            refine ⟨48860235365530799718202805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32573490243687199812135203 48860235365530799718202805)
            ·
              refine ⟨4580647065518512473581513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48860235365530799718202805 4580647065518512473581513)
              ·
                refine ⟨3435485299138884355186135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4580647065518512473581513 3435485299138884355186135)
                ·
                  refine ⟨5153227948708326532779203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3435485299138884355186135 5153227948708326532779203)
                  ·
                    refine ⟨7729841923062489799168805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5153227948708326532779203 7729841923062489799168805)
                    ·
                      refine ⟨1449345360574216837344151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7729841923062489799168805 1449345360574216837344151)
                      ·
                        rfl

theorem cell23_2822590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_2822590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822590 prefixEnd_2822590 := by exact prefixLift 2822590
  have htrace : WordTrace (prefixWord ++ tailWord_2822590) baseStart_2822590 baseEnd_2822590 := by
    simpa [prefixWord, tailWord_2822590, baseEnd_2822590] using wordTrace_append hprefix tailTrace_2822590
  have hstable : (prefixWord ++ tailWord_2822590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822590).length < 2 ^ (prefixWord ++ tailWord_2822590).sum := by decide
  have hdescent : baseEnd_2822590 < baseStart_2822590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822607 : List Nat := [1, 1, 2, 1, 1, 4, 1, 7, 1, 2, 2]
def baseStart_2822607 : Nat := 118140960795 + 2822607 * 2 ^ 59
def prefixEnd_2822607 : Nat := 4983230072969 + 3 ^ 40 * 2822607 * 2
def baseEnd_2822607 : Nat := 1449354089745343270831573

theorem tailTrace_2822607 : CollatzResearch.WordTrace tailWord_2822607 prefixEnd_2822607 1449354089745343270831573 := by
  unfold tailWord_2822607
  simp only [CollatzResearch.WordTrace]
  refine ⟨102948934885184376741722075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68632623256789584494481383 102948934885184376741722075)
  ·
    refine ⟨154423402327776565112583113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102948934885184376741722075 154423402327776565112583113)
    ·
      refine ⟨115817551745832423834437335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154423402327776565112583113 115817551745832423834437335)
      ·
        refine ⟨173726327618748635751656003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115817551745832423834437335 173726327618748635751656003)
        ·
          refine ⟨260589491428122953627484005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173726327618748635751656003 260589491428122953627484005)
          ·
            refine ⟨48860529642773053805153251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 260589491428122953627484005 48860529642773053805153251)
            ·
              refine ⟨73290794464159580707729877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48860529642773053805153251 73290794464159580707729877)
              ·
                refine ⟨1717752995253740172837419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 73290794464159580707729877 1717752995253740172837419)
                ·
                  refine ⟨2576629492880610259256129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1717752995253740172837419 2576629492880610259256129)
                  ·
                    refine ⟨1932472119660457694442097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2576629492880610259256129 1932472119660457694442097)
                    ·
                      refine ⟨1449354089745343270831573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1932472119660457694442097 1449354089745343270831573)
                      ·
                        rfl

theorem cell23_2822607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 7, 1, 2, 2].length) (baseStart_2822607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822607 prefixEnd_2822607 := by exact prefixLift 2822607
  have htrace : WordTrace (prefixWord ++ tailWord_2822607) baseStart_2822607 baseEnd_2822607 := by
    simpa [prefixWord, tailWord_2822607, baseEnd_2822607] using wordTrace_append hprefix tailTrace_2822607
  have hstable : (prefixWord ++ tailWord_2822607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822607).length < 2 ^ (prefixWord ++ tailWord_2822607).sum := by decide
  have hdescent : baseEnd_2822607 < baseStart_2822607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822640 : List Nat := [2, 1, 1, 1, 3, 3, 1, 5, 2, 1, 3]
def baseStart_2822640 : Nat := 118140960795 + 2822640 * 2 ^ 59
def prefixEnd_2822640 : Nat := 4983230072969 + 3 ^ 40 * 2822640 * 2
def baseEnd_2822640 : Nat := 1449371034606941641718921

theorem tailTrace_2822640 : CollatzResearch.WordTrace tailWord_2822640 prefixEnd_2822640 1449371034606941641718921 := by
  unfold tailWord_2822640
  simp only [CollatzResearch.WordTrace]
  refine ⟨51475069247032411688836687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68633425662709882251782249 51475069247032411688836687)
  ·
    refine ⟨77212603870548617533255031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51475069247032411688836687 77212603870548617533255031)
    ·
      refine ⟨115818905805822926299882547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77212603870548617533255031 115818905805822926299882547)
      ·
        refine ⟨173728358708734389449823821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115818905805822926299882547 173728358708734389449823821)
        ·
          refine ⟨65148134515775396043683933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173728358708734389449823821 65148134515775396043683933)
          ·
            refine ⟨24430550443415773516381475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65148134515775396043683933 24430550443415773516381475)
            ·
              refine ⟨36645825665123660274572213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24430550443415773516381475 36645825665123660274572213)
              ·
                refine ⟨3435546156105343150741145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36645825665123660274572213 3435546156105343150741145)
                ·
                  refine ⟨2576659617079007363055859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3435546156105343150741145 2576659617079007363055859)
                  ·
                    refine ⟨3864989425618511044583789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2576659617079007363055859 3864989425618511044583789)
                    ·
                      refine ⟨1449371034606941641718921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3864989425618511044583789 1449371034606941641718921)
                      ·
                        rfl

theorem cell23_2822640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 2, 1, 3].length) (baseStart_2822640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822640 prefixEnd_2822640 := by exact prefixLift 2822640
  have htrace : WordTrace (prefixWord ++ tailWord_2822640) baseStart_2822640 baseEnd_2822640 := by
    simpa [prefixWord, tailWord_2822640, baseEnd_2822640] using wordTrace_append hprefix tailTrace_2822640
  have hstable : (prefixWord ++ tailWord_2822640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822640).length < 2 ^ (prefixWord ++ tailWord_2822640).sum := by decide
  have hdescent : baseEnd_2822640 < baseStart_2822640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822658 : List Nat := [3, 4, 1, 2, 2, 1, 2, 3, 1, 2, 2]
def baseStart_2822658 : Nat := 118140960795 + 2822658 * 2 ^ 59
def prefixEnd_2822658 : Nat := 4983230072969 + 3 ^ 40 * 2822658 * 2
def baseEnd_2822658 : Nat := 1449380277258722571293839

theorem tailTrace_2822658 : CollatzResearch.WordTrace tailWord_2822658 prefixEnd_2822658 1449380277258722571293839 := by
  unfold tailWord_2822658
  simp only [CollatzResearch.WordTrace]
  refine ⟨25737698751999903112957157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68633863338666408301219085 25737698751999903112957157)
  ·
    refine ⟨4825818515999981833679467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25737698751999903112957157 4825818515999981833679467)
    ·
      refine ⟨7238727773999972750519201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4825818515999981833679467 7238727773999972750519201)
      ·
        refine ⟨5429045830499979562889401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7238727773999972750519201 5429045830499979562889401)
        ·
          refine ⟨4071784372874984672167051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5429045830499979562889401 4071784372874984672167051)
          ·
            refine ⟨6107676559312477008250577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4071784372874984672167051 6107676559312477008250577)
            ·
              refine ⟨4580757419484357756187933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6107676559312477008250577 4580757419484357756187933)
              ·
                refine ⟨1717784032306634158570475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4580757419484357756187933 1717784032306634158570475)
                ·
                  refine ⟨2576676048459951237855713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1717784032306634158570475 2576676048459951237855713)
                  ·
                    refine ⟨1932507036344963428391785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2576676048459951237855713 1932507036344963428391785)
                    ·
                      refine ⟨1449380277258722571293839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1932507036344963428391785 1449380277258722571293839)
                      ·
                        rfl

theorem cell23_2822658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_2822658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822658 prefixEnd_2822658 := by exact prefixLift 2822658
  have htrace : WordTrace (prefixWord ++ tailWord_2822658) baseStart_2822658 baseEnd_2822658 := by
    simpa [prefixWord, tailWord_2822658, baseEnd_2822658] using wordTrace_append hprefix tailTrace_2822658
  have hstable : (prefixWord ++ tailWord_2822658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822658).length < 2 ^ (prefixWord ++ tailWord_2822658).sum := by decide
  have hdescent : baseEnd_2822658 < baseStart_2822658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822667 : List Nat := [1, 1, 1, 1, 7, 2, 1, 3, 1, 3, 2]
def baseStart_2822667 : Nat := 118140960795 + 2822667 * 2 ^ 59
def prefixEnd_2822667 : Nat := 4983230072969 + 3 ^ 40 * 2822667 * 2
def baseEnd_2822667 : Nat := 1449384898584613036081297

theorem tailTrace_2822667 : CollatzResearch.WordTrace tailWord_2822667 prefixEnd_2822667 1449384898584613036081297 := by
  unfold tailWord_2822667
  simp only [CollatzResearch.WordTrace]
  refine ⟨102951123264967006988906255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68634082176644671325937503 102951123264967006988906255)
  ·
    refine ⟨154426684897450510483359383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102951123264967006988906255 154426684897450510483359383)
    ·
      refine ⟨231640027346175765725039075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154426684897450510483359383 231640027346175765725039075)
      ·
        refine ⟨347460041019263648587558613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231640027346175765725039075 347460041019263648587558613)
        ·
          refine ⟨8143594711388991763770905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 347460041019263648587558613 8143594711388991763770905)
          ·
            refine ⟨6107696033541743822828179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8143594711388991763770905 6107696033541743822828179)
            ·
              refine ⟨9161544050312615734242269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6107696033541743822828179 9161544050312615734242269)
              ·
                refine ⟨3435579018867230900340851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9161544050312615734242269 3435579018867230900340851)
                ·
                  refine ⟨5153368528300846350511277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3435579018867230900340851 5153368528300846350511277)
                  ·
                    refine ⟨1932513198112817381441729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5153368528300846350511277 1932513198112817381441729)
                    ·
                      refine ⟨1449384898584613036081297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1932513198112817381441729 1449384898584613036081297)
                      ·
                        rfl

theorem cell23_2822667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 3, 2].length) (baseStart_2822667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822667 prefixEnd_2822667 := by exact prefixLift 2822667
  have htrace : WordTrace (prefixWord ++ tailWord_2822667) baseStart_2822667 baseEnd_2822667 := by
    simpa [prefixWord, tailWord_2822667, baseEnd_2822667] using wordTrace_append hprefix tailTrace_2822667
  have hstable : (prefixWord ++ tailWord_2822667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822667).length < 2 ^ (prefixWord ++ tailWord_2822667).sum := by decide
  have hdescent : baseEnd_2822667 < baseStart_2822667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822693 : List Nat := [1, 3, 1, 2, 2, 1, 4, 1, 2, 2, 4]
def baseStart_2822693 : Nat := 118140960795 + 2822693 * 2 ^ 59
def prefixEnd_2822693 : Nat := 4983230072969 + 3 ^ 40 * 2822693 * 2
def baseEnd_2822693 : Nat := 1449398249081629934356177

theorem tailTrace_2822693 : CollatzResearch.WordTrace tailWord_2822693 prefixEnd_2822693 1449398249081629934356177 := by
  unfold tailWord_2822693
  simp only [CollatzResearch.WordTrace]
  refine ⟨102952071562872813429352733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68634714375248542286235155 102952071562872813429352733)
  ·
    refine ⟨38607026836077305036007275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102952071562872813429352733 38607026836077305036007275)
    ·
      refine ⟨57910540254115957554010913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38607026836077305036007275 57910540254115957554010913)
      ·
        refine ⟨43432905190586968165508185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57910540254115957554010913 43432905190586968165508185)
        ·
          refine ⟨32574678892940226124131139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43432905190586968165508185 32574678892940226124131139)
          ·
            refine ⟨48862018339410339186196709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32574678892940226124131139 48862018339410339186196709)
            ·
              refine ⟨9161628438639438597411883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48862018339410339186196709 9161628438639438597411883)
              ·
                refine ⟨13742442657959157896117825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9161628438639438597411883 13742442657959157896117825)
                ·
                  refine ⟨10306831993469368422088369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13742442657959157896117825 10306831993469368422088369)
                  ·
                    refine ⟨7730123995102026316566277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10306831993469368422088369 7730123995102026316566277)
                    ·
                      refine ⟨1449398249081629934356177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7730123995102026316566277 1449398249081629934356177)
                      ·
                        rfl

theorem cell23_2822693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_2822693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822693 prefixEnd_2822693 := by exact prefixLift 2822693
  have htrace : WordTrace (prefixWord ++ tailWord_2822693) baseStart_2822693 baseEnd_2822693 := by
    simpa [prefixWord, tailWord_2822693, baseEnd_2822693] using wordTrace_append hprefix tailTrace_2822693
  have hstable : (prefixWord ++ tailWord_2822693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822693).length < 2 ^ (prefixWord ++ tailWord_2822693).sum := by decide
  have hdescent : baseEnd_2822693 < baseStart_2822693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822720 : List Nat := [2, 1, 1, 2, 2, 2, 5, 3, 5]
def baseStart_2822720 : Nat := 118140960795 + 2822720 * 2 ^ 59
def prefixEnd_2822720 : Nat := 4983230072969 + 3 ^ 40 * 2822720 * 2
def baseEnd_2822720 : Nat := 161045790339922369857617

theorem tailTrace_2822720 : CollatzResearch.WordTrace tailWord_2822720 prefixEnd_2822720 161045790339922369857617 := by
  unfold tailWord_2822720
  simp only [CollatzResearch.WordTrace]
  refine ⟨51476528166887498520292807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68635370889183331360390409 51476528166887498520292807)
  ·
    refine ⟨77214792250331247780439211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51476528166887498520292807 77214792250331247780439211)
    ·
      refine ⟨115822188375496871670658817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77214792250331247780439211 115822188375496871670658817)
      ·
        refine ⟨86866641281622653752994113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115822188375496871670658817 86866641281622653752994113)
        ·
          refine ⟨65149980961216990314745585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86866641281622653752994113 65149980961216990314745585)
          ·
            refine ⟨48862485720912742736059189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65149980961216990314745585 48862485720912742736059189)
            ·
              refine ⟨4580858036335569631505549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48862485720912742736059189 4580858036335569631505549)
              ·
                refine ⟨1717821763625838611814581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4580858036335569631505549 1717821763625838611814581)
                ·
                  refine ⟨161045790339922369857617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1717821763625838611814581 161045790339922369857617)
                  ·
                    rfl

theorem cell23_2822720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 3, 5].length) (baseStart_2822720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822720 prefixEnd_2822720 := by exact prefixLift 2822720
  have htrace : WordTrace (prefixWord ++ tailWord_2822720) baseStart_2822720 baseEnd_2822720 := by
    simpa [prefixWord, tailWord_2822720, baseEnd_2822720] using wordTrace_append hprefix tailTrace_2822720
  have hstable : (prefixWord ++ tailWord_2822720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822720).length < 2 ^ (prefixWord ++ tailWord_2822720).sum := by decide
  have hdescent : baseEnd_2822720 < baseStart_2822720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822737 : List Nat := [1, 2, 2, 1, 3, 4, 3, 2, 5]
def baseStart_2822737 : Nat := 118140960795 + 2822737 * 2 ^ 59
def prefixEnd_2822737 : Nat := 4983230072969 + 3 ^ 40 * 2822737 * 2
def baseEnd_2822737 : Nat := 161046760247825306911775

theorem tailTrace_2822737 : CollatzResearch.WordTrace tailWord_2822737 prefixEnd_2822737 161046760247825306911775 := by
  unfold tailWord_2822737
  simp only [CollatzResearch.WordTrace]
  refine ⟨102953676374713408943954465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68635784249808939295969643 102953676374713408943954465)
  ·
    refine ⟨77215257281035056707965849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102953676374713408943954465 77215257281035056707965849)
    ·
      refine ⟨57911442960776292530974387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77215257281035056707965849 57911442960776292530974387)
      ·
        refine ⟨86867164441164438796461581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57911442960776292530974387 86867164441164438796461581)
        ·
          refine ⟨32575186665436664548673093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86867164441164438796461581 32575186665436664548673093)
          ·
            refine ⟨6107847499769374602876205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32575186665436664548673093 6107847499769374602876205)
            ·
              refine ⟨2290442812413515476078577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6107847499769374602876205 2290442812413515476078577)
              ·
                refine ⟨1717832109310136607058933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2290442812413515476078577 1717832109310136607058933)
                ·
                  refine ⟨161046760247825306911775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1717832109310136607058933 161046760247825306911775)
                  ·
                    rfl

theorem cell23_2822737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 2, 5].length) (baseStart_2822737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822737 prefixEnd_2822737 := by exact prefixLift 2822737
  have htrace : WordTrace (prefixWord ++ tailWord_2822737) baseStart_2822737 baseEnd_2822737 := by
    simpa [prefixWord, tailWord_2822737, baseEnd_2822737] using wordTrace_append hprefix tailTrace_2822737
  have hstable : (prefixWord ++ tailWord_2822737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822737).length < 2 ^ (prefixWord ++ tailWord_2822737).sum := by decide
  have hdescent : baseEnd_2822737 < baseStart_2822737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822743 : List Nat := [1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 5]
def baseStart_2822743 : Nat := 118140960795 + 2822743 * 2 ^ 59
def prefixEnd_2822743 : Nat := 4983230072969 + 3 ^ 40 * 2822743 * 2
def baseEnd_2822743 : Nat := 1449423923114354738730947

theorem tailTrace_2822743 : CollatzResearch.WordTrace tailWord_2822743 prefixEnd_2822743 1449423923114354738730947 := by
  unfold tailWord_2822743
  simp only [CollatzResearch.WordTrace]
  refine ⟨102953895212691671968672883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68635930141794447979115255 102953895212691671968672883)
  ·
    refine ⟨154430842819037507953009325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102953895212691671968672883 154430842819037507953009325)
    ·
      refine ⟨57911566057139065482378497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154430842819037507953009325 57911566057139065482378497)
      ·
        refine ⟨43433674542854299111783873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57911566057139065482378497 43433674542854299111783873)
        ·
          refine ⟨32575255907140724333837905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43433674542854299111783873 32575255907140724333837905)
          ·
            refine ⟨24431441930355543250378429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32575255907140724333837905 24431441930355543250378429)
            ·
              refine ⟨9161790723883328718891911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24431441930355543250378429 9161790723883328718891911)
              ·
                refine ⟨13742686085824993078337867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9161790723883328718891911 13742686085824993078337867)
                ·
                  refine ⟨20614029128737489617506801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13742686085824993078337867 20614029128737489617506801)
                  ·
                    refine ⟨15460521846553117213130101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20614029128737489617506801 15460521846553117213130101)
                    ·
                      refine ⟨1449423923114354738730947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15460521846553117213130101 1449423923114354738730947)
                      ·
                        rfl

theorem cell23_2822743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_2822743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822743 prefixEnd_2822743 := by exact prefixLift 2822743
  have htrace : WordTrace (prefixWord ++ tailWord_2822743) baseStart_2822743 baseEnd_2822743 := by
    simpa [prefixWord, tailWord_2822743, baseEnd_2822743] using wordTrace_append hprefix tailTrace_2822743
  have hstable : (prefixWord ++ tailWord_2822743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822743).length < 2 ^ (prefixWord ++ tailWord_2822743).sum := by decide
  have hdescent : baseEnd_2822743 < baseStart_2822743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822748 : List Nat := [2, 2, 4, 1, 3, 2, 2, 1, 2, 2, 2]
def baseStart_2822748 : Nat := 118140960795 + 2822748 * 2 ^ 59
def prefixEnd_2822748 : Nat := 4983230072969 + 3 ^ 40 * 2822748 * 2
def baseEnd_2822748 : Nat := 1449426490517627219168425

theorem tailTrace_2822748 : CollatzResearch.WordTrace tailWord_2822748 prefixEnd_2822748 1449426490517627219168425 := by
  unfold tailWord_2822748
  simp only [CollatzResearch.WordTrace]
  refine ⟨51477038788836778911302449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68636051718449038548403265 51477038788836778911302449)
  ·
    refine ⟨38607779091627584183476837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51477038788836778911302449 38607779091627584183476837)
    ·
      refine ⟨7238958579680172034401907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38607779091627584183476837 7238958579680172034401907)
      ·
        refine ⟨10858437869520258051602861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7238958579680172034401907 10858437869520258051602861)
        ·
          refine ⟨4071914201070096769351073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10858437869520258051602861 4071914201070096769351073)
          ·
            refine ⟨3053935650802572577013305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4071914201070096769351073 3053935650802572577013305)
            ·
              refine ⟨2290451738101929432759979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3053935650802572577013305 2290451738101929432759979)
              ·
                refine ⟨3435677607152894149139969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2290451738101929432759979 3435677607152894149139969)
                ·
                  refine ⟨2576758205364670611854977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3435677607152894149139969 2576758205364670611854977)
                  ·
                    refine ⟨1932568654023502958891233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2576758205364670611854977 1932568654023502958891233)
                    ·
                      refine ⟨1449426490517627219168425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1932568654023502958891233 1449426490517627219168425)
                      ·
                        rfl

theorem cell23_2822748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_2822748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822748 prefixEnd_2822748 := by exact prefixLift 2822748
  have htrace : WordTrace (prefixWord ++ tailWord_2822748) baseStart_2822748 baseEnd_2822748 := by
    simpa [prefixWord, tailWord_2822748, baseEnd_2822748] using wordTrace_append hprefix tailTrace_2822748
  have hstable : (prefixWord ++ tailWord_2822748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822748).length < 2 ^ (prefixWord ++ tailWord_2822748).sum := by decide
  have hdescent : baseEnd_2822748 < baseStart_2822748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822804 : List Nat := [2, 4, 2, 2, 1, 2, 1, 1, 2, 4, 2]
def baseStart_2822804 : Nat := 118140960795 + 2822804 * 2 ^ 59
def prefixEnd_2822804 : Nat := 4983230072969 + 3 ^ 40 * 2822804 * 2
def baseEnd_2822804 : Nat := 1449455245434279000068167

theorem tailTrace_2822804 : CollatzResearch.WordTrace tailWord_2822804 prefixEnd_2822804 1449455245434279000068167 := by
  unfold tailWord_2822804
  simp only [CollatzResearch.WordTrace]
  refine ⟨51478060032735339693321733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68637413376980452924428977 51478060032735339693321733)
  ·
    refine ⟨9652136256137876192497825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51478060032735339693321733 9652136256137876192497825)
    ·
      refine ⟨7239102192103407144373369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9652136256137876192497825 7239102192103407144373369)
      ·
        refine ⟨5429326644077555358280027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7239102192103407144373369 5429326644077555358280027)
        ·
          refine ⟨8143989966116333037420041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5429326644077555358280027 8143989966116333037420041)
          ·
            refine ⟨6107992474587249778065031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8143989966116333037420041 6107992474587249778065031)
            ·
              refine ⟨9161988711880874667097547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6107992474587249778065031 9161988711880874667097547)
              ·
                refine ⟨13742983067821312000646321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9161988711880874667097547 13742983067821312000646321)
                ·
                  refine ⟨10307237300865984000484741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13742983067821312000646321 10307237300865984000484741)
                  ·
                    refine ⟨1932606993912372000090889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10307237300865984000484741 1932606993912372000090889)
                    ·
                      refine ⟨1449455245434279000068167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1932606993912372000090889 1449455245434279000068167)
                      ·
                        rfl

theorem cell23_2822804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_2822804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822804 prefixEnd_2822804 := by exact prefixLift 2822804
  have htrace : WordTrace (prefixWord ++ tailWord_2822804) baseStart_2822804 baseEnd_2822804 := by
    simpa [prefixWord, tailWord_2822804, baseEnd_2822804] using wordTrace_append hprefix tailTrace_2822804
  have hstable : (prefixWord ++ tailWord_2822804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822804).length < 2 ^ (prefixWord ++ tailWord_2822804).sum := by decide
  have hdescent : baseEnd_2822804 < baseStart_2822804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822861 : List Nat := [1, 6, 2, 1, 2, 1, 3, 1, 6]
def baseStart_2822861 : Nat := 118140960795 + 2822861 * 2 ^ 59
def prefixEnd_2822861 : Nat := 4983230072969 + 3 ^ 40 * 2822861 * 2
def baseEnd_2822861 : Nat := 161053834870176141895045

theorem tailTrace_2822861 : CollatzResearch.WordTrace tailWord_2822861 prefixEnd_2822861 161053834870176141895045 := by
  unfold tailWord_2822861
  simp only [CollatzResearch.WordTrace]
  refine ⟨102958199026264178121468437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68638799350842785414312291 102958199026264178121468437)
  ·
    refine ⟨4826165579356133349443833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 102958199026264178121468437 4826165579356133349443833)
    ·
      refine ⟨3619624184517100012082875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4826165579356133349443833 3619624184517100012082875)
      ·
        refine ⟨5429436276775650018124313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3619624184517100012082875 5429436276775650018124313)
        ·
          refine ⟨4072077207581737513593235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5429436276775650018124313 4072077207581737513593235)
          ·
            refine ⟨6108115811372606270389853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4072077207581737513593235 6108115811372606270389853)
            ·
              refine ⟨2290543429264727351396195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6108115811372606270389853 2290543429264727351396195)
              ·
                refine ⟨3435815143897091027094293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2290543429264727351396195 3435815143897091027094293)
                ·
                  refine ⟨161053834870176141895045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3435815143897091027094293 161053834870176141895045)
                  ·
                    rfl

theorem cell23_2822861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_2822861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822861 prefixEnd_2822861 := by exact prefixLift 2822861
  have htrace : WordTrace (prefixWord ++ tailWord_2822861) baseStart_2822861 baseEnd_2822861 := by
    simpa [prefixWord, tailWord_2822861, baseEnd_2822861] using wordTrace_append hprefix tailTrace_2822861
  have hstable : (prefixWord ++ tailWord_2822861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822861).length < 2 ^ (prefixWord ++ tailWord_2822861).sum := by decide
  have hdescent : baseEnd_2822861 < baseStart_2822861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822888 : List Nat := [2, 1, 4, 1, 4, 2, 1, 3, 1, 1, 3]
def baseStart_2822888 : Nat := 118140960795 + 2822888 * 2 ^ 59
def prefixEnd_2822888 : Nat := 4983230072969 + 3 ^ 40 * 2822888 * 2
def baseEnd_2822888 : Nat := 1449498377809256671417781

theorem tailTrace_2822888 : CollatzResearch.WordTrace tailWord_2822888 prefixEnd_2822888 1449498377809256671417781 := by
  unfold tailWord_2822888
  simp only [CollatzResearch.WordTrace]
  refine ⟨51479591898583180866350659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68639455864777574488467545 51479591898583180866350659)
  ·
    refine ⟨77219387847874771299525989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51479591898583180866350659 77219387847874771299525989)
    ·
      refine ⟨14478635221476519618661123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77219387847874771299525989 14478635221476519618661123)
      ·
        refine ⟨21717952832214779427991685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14478635221476519618661123 21717952832214779427991685)
        ·
          refine ⟨4072116156040271142748441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21717952832214779427991685 4072116156040271142748441)
          ·
            refine ⟨3054087117030203357061331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4072116156040271142748441 3054087117030203357061331)
            ·
              refine ⟨4581130675545305035591997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3054087117030203357061331 4581130675545305035591997)
              ·
                refine ⟨1717924003329489388346999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4581130675545305035591997 1717924003329489388346999)
                ·
                  refine ⟨2576886004994234082520499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1717924003329489388346999 2576886004994234082520499)
                  ·
                    refine ⟨3865329007491351123780749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2576886004994234082520499 3865329007491351123780749)
                    ·
                      refine ⟨1449498377809256671417781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3865329007491351123780749 1449498377809256671417781)
                      ·
                        rfl

theorem cell23_2822888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_2822888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822888 prefixEnd_2822888 := by exact prefixLift 2822888
  have htrace : WordTrace (prefixWord ++ tailWord_2822888) baseStart_2822888 baseEnd_2822888 := by
    simpa [prefixWord, tailWord_2822888, baseEnd_2822888] using wordTrace_append hprefix tailTrace_2822888
  have hstable : (prefixWord ++ tailWord_2822888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822888).length < 2 ^ (prefixWord ++ tailWord_2822888).sum := by decide
  have hdescent : baseEnd_2822888 < baseStart_2822888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822890 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 3, 2, 4]
def baseStart_2822890 : Nat := 118140960795 + 2822890 * 2 ^ 59
def prefixEnd_2822890 : Nat := 4983230072969 + 3 ^ 40 * 2822890 * 2
def baseEnd_2822890 : Nat := 1449499404770565663592771

theorem tailTrace_2822890 : CollatzResearch.WordTrace tailWord_2822890 prefixEnd_2822890 1449499404770565663592771 := by
  unfold tailWord_2822890
  simp only [CollatzResearch.WordTrace]
  refine ⟨25739814185789779018568531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68639504495439410716182749 25739814185789779018568531)
  ·
    refine ⟨38609721278684668527852797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25739814185789779018568531 38609721278684668527852797)
    ·
      refine ⟨14478645479506750697944799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38609721278684668527852797 14478645479506750697944799)
      ·
        refine ⟨21717968219260126046917199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14478645479506750697944799 21717968219260126046917199)
        ·
          refine ⟨32576952328890189070375799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21717968219260126046917199 32576952328890189070375799)
          ·
            refine ⟨48865428493335283605563699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32576952328890189070375799 48865428493335283605563699)
            ·
              refine ⟨73298142740002925408345549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48865428493335283605563699 73298142740002925408345549)
              ·
                refine ⟨27486803527501097028129581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73298142740002925408345549 27486803527501097028129581)
                ·
                  refine ⟨10307551322812911385548593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27486803527501097028129581 10307551322812911385548593)
                  ·
                    refine ⟨7730663492109683539161445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10307551322812911385548593 7730663492109683539161445)
                    ·
                      refine ⟨1449499404770565663592771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7730663492109683539161445 1449499404770565663592771)
                      ·
                        rfl

theorem cell23_2822890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_2822890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822890 prefixEnd_2822890 := by exact prefixLift 2822890
  have htrace : WordTrace (prefixWord ++ tailWord_2822890) baseStart_2822890 baseEnd_2822890 := by
    simpa [prefixWord, tailWord_2822890, baseEnd_2822890] using wordTrace_append hprefix tailTrace_2822890
  have hstable : (prefixWord ++ tailWord_2822890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822890).length < 2 ^ (prefixWord ++ tailWord_2822890).sum := by decide
  have hdescent : baseEnd_2822890 < baseStart_2822890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822897 : List Nat := [1, 2, 2, 2, 2, 2, 1, 5, 1, 2, 3]
def baseStart_2822897 : Nat := 118140960795 + 2822897 * 2 ^ 59
def prefixEnd_2822897 : Nat := 4983230072969 + 3 ^ 40 * 2822897 * 2
def baseEnd_2822897 : Nat := 1449502999135147136205239

theorem tailTrace_2822897 : CollatzResearch.WordTrace tailWord_2822897 prefixEnd_2822897 1449502999135147136205239 := by
  unfold tailWord_2822897
  simp only [CollatzResearch.WordTrace]
  refine ⟨102959512054133756269778945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68639674702755837513185963 102959512054133756269778945)
  ·
    refine ⟨77219634040600317202334209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102959512054133756269778945 77219634040600317202334209)
    ·
      refine ⟨57914725530450237901750657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77219634040600317202334209 57914725530450237901750657)
      ·
        refine ⟨43436044147837678426312993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57914725530450237901750657 43436044147837678426312993)
        ·
          refine ⟨32577033110878258819734745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43436044147837678426312993 32577033110878258819734745)
          ·
            refine ⟨24432774833158694114801059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32577033110878258819734745 24432774833158694114801059)
            ·
              refine ⟨36649162249738041172201589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24432774833158694114801059 36649162249738041172201589)
              ·
                refine ⟨3435858960912941359893899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36649162249738041172201589 3435858960912941359893899)
                ·
                  refine ⟨5153788441369412039840849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3435858960912941359893899 5153788441369412039840849)
                  ·
                    refine ⟨3865341331027059029880637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5153788441369412039840849 3865341331027059029880637)
                    ·
                      refine ⟨1449502999135147136205239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3865341331027059029880637 1449502999135147136205239)
                      ·
                        rfl

theorem cell23_2822897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_2822897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822897 prefixEnd_2822897 := by exact prefixLift 2822897
  have htrace : WordTrace (prefixWord ++ tailWord_2822897) baseStart_2822897 baseEnd_2822897 := by
    simpa [prefixWord, tailWord_2822897, baseEnd_2822897] using wordTrace_append hprefix tailTrace_2822897
  have hstable : (prefixWord ++ tailWord_2822897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822897).length < 2 ^ (prefixWord ++ tailWord_2822897).sum := by decide
  have hdescent : baseEnd_2822897 < baseStart_2822897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822967 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 3, 4, 2]
def baseStart_2822967 : Nat := 118140960795 + 2822967 * 2 ^ 59
def prefixEnd_2822967 : Nat := 4983230072969 + 3 ^ 40 * 2822967 * 2
def baseEnd_2822967 : Nat := 1449538942780961862329917

theorem tailTrace_2822967 : CollatzResearch.WordTrace tailWord_2822967 prefixEnd_2822967 1449538942780961862329917 := by
  unfold tailWord_2822967
  simp only [CollatzResearch.WordTrace]
  refine ⟨102962065163880158224827155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68641376775920105483218103 102962065163880158224827155)
  ·
    refine ⟨154443097745820237337240733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102962065163880158224827155 154443097745820237337240733)
    ·
      refine ⟨57916161654682589001465275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154443097745820237337240733 57916161654682589001465275)
      ·
        refine ⟨86874242482023883502197913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57916161654682589001465275 86874242482023883502197913)
        ·
          refine ⟨65155681861517912626648435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86874242482023883502197913 65155681861517912626648435)
          ·
            refine ⟨97733522792276868939972653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65155681861517912626648435 97733522792276868939972653)
            ·
              refine ⟨36650071047103825852489745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97733522792276868939972653 36650071047103825852489745)
              ·
                refine ⟨27487553285327869389367309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36650071047103825852489745 27487553285327869389367309)
                ·
                  refine ⟨10307832481997951021012741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27487553285327869389367309 10307832481997951021012741)
                  ·
                    refine ⟨1932718590374615816439889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10307832481997951021012741 1932718590374615816439889)
                    ·
                      refine ⟨1449538942780961862329917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1932718590374615816439889 1449538942780961862329917)
                      ·
                        rfl

theorem cell23_2822967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 4, 2].length) (baseStart_2822967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822967 prefixEnd_2822967 := by exact prefixLift 2822967
  have htrace : WordTrace (prefixWord ++ tailWord_2822967) baseStart_2822967 baseEnd_2822967 := by
    simpa [prefixWord, tailWord_2822967, baseEnd_2822967] using wordTrace_append hprefix tailTrace_2822967
  have hstable : (prefixWord ++ tailWord_2822967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822967).length < 2 ^ (prefixWord ++ tailWord_2822967).sum := by decide
  have hdescent : baseEnd_2822967 < baseStart_2822967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2822984 : List Nat := [2, 1, 3, 1, 1, 3, 4, 1, 1, 4, 2]
def baseStart_2822984 : Nat := 118140960795 + 2822984 * 2 ^ 59
def prefixEnd_2822984 : Nat := 4983230072969 + 3 ^ 40 * 2822984 * 2
def baseEnd_2822984 : Nat := 1449547671952088295817339

theorem tailTrace_2822984 : CollatzResearch.WordTrace tailWord_2822984 prefixEnd_2822984 1449547671952088295817339 := by
  unfold tailWord_2822984
  simp only [CollatzResearch.WordTrace]
  refine ⟨51481342602409285064098003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68641790136545713418797337 51481342602409285064098003)
  ·
    refine ⟨77222013903613927596147005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51481342602409285064098003 77222013903613927596147005)
    ·
      refine ⟨28958255213855222848555127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77222013903613927596147005 28958255213855222848555127)
      ·
        refine ⟨43437382820782834272832691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28958255213855222848555127 43437382820782834272832691)
        ·
          refine ⟨65156074231174251409249037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43437382820782834272832691 65156074231174251409249037)
          ·
            refine ⟨24433527836690344278468389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65156074231174251409249037 24433527836690344278468389)
            ·
              refine ⟨4581286469379439552212823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24433527836690344278468389 4581286469379439552212823)
              ·
                refine ⟨6871929704069159328319235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4581286469379439552212823 6871929704069159328319235)
                ·
                  refine ⟨10307894556103738992478853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6871929704069159328319235 10307894556103738992478853)
                  ·
                    refine ⟨1932730229269451061089785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10307894556103738992478853 1932730229269451061089785)
                    ·
                      refine ⟨1449547671952088295817339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1932730229269451061089785 1449547671952088295817339)
                      ·
                        rfl

theorem cell23_2822984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 1, 4, 2].length) (baseStart_2822984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2822984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2822984 prefixEnd_2822984 := by exact prefixLift 2822984
  have htrace : WordTrace (prefixWord ++ tailWord_2822984) baseStart_2822984 baseEnd_2822984 := by
    simpa [prefixWord, tailWord_2822984, baseEnd_2822984] using wordTrace_append hprefix tailTrace_2822984
  have hstable : (prefixWord ++ tailWord_2822984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2822984).length < 2 ^ (prefixWord ++ tailWord_2822984).sum := by decide
  have hdescent : baseEnd_2822984 < baseStart_2822984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2822984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823027 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 1, 7, 2]
def baseStart_2823027 : Nat := 118140960795 + 2823027 * 2 ^ 59
def prefixEnd_2823027 : Nat := 4983230072969 + 3 ^ 40 * 2823027 * 2
def baseEnd_2823027 : Nat := 1449569751620231627579641

theorem tailTrace_2823027 : CollatzResearch.WordTrace tailWord_2823027 prefixEnd_2823027 1449569751620231627579641 := by
  unfold tailWord_2823027
  simp only [CollatzResearch.WordTrace]
  refine ⟨102964253543662788472011335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68642835695775192314674223 102964253543662788472011335)
  ·
    refine ⟨154446380315494182708017003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102964253543662788472011335 154446380315494182708017003)
    ·
      refine ⟨231669570473241274062025505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154446380315494182708017003 231669570473241274062025505)
      ·
        refine ⟨173752177854930955546519129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231669570473241274062025505 173752177854930955546519129)
        ·
          refine ⟨130314133391198216659889347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173752177854930955546519129 130314133391198216659889347)
          ·
            refine ⟨195471200086797324989834021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130314133391198216659889347 195471200086797324989834021)
            ·
              refine ⟨36650850016274498435593879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 195471200086797324989834021 36650850016274498435593879)
              ·
                refine ⟨54976275024411747653390819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36650850016274498435593879 54976275024411747653390819)
                ·
                  refine ⟨82464412536617621480086229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54976275024411747653390819 82464412536617621480086229)
                  ·
                    refine ⟨1932759668826975503439521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 82464412536617621480086229 1932759668826975503439521)
                    ·
                      refine ⟨1449569751620231627579641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1932759668826975503439521 1449569751620231627579641)
                      ·
                        rfl

theorem cell23_2823027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 7, 2].length) (baseStart_2823027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823027 prefixEnd_2823027 := by exact prefixLift 2823027
  have htrace : WordTrace (prefixWord ++ tailWord_2823027) baseStart_2823027 baseEnd_2823027 := by
    simpa [prefixWord, tailWord_2823027, baseEnd_2823027] using wordTrace_append hprefix tailTrace_2823027
  have hstable : (prefixWord ++ tailWord_2823027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823027).length < 2 ^ (prefixWord ++ tailWord_2823027).sum := by decide
  have hdescent : baseEnd_2823027 < baseStart_2823027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823057 : List Nat := [1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 4]
def baseStart_2823057 : Nat := 118140960795 + 2823057 * 2 ^ 59
def prefixEnd_2823057 : Nat := 4983230072969 + 3 ^ 40 * 2823057 * 2
def baseEnd_2823057 : Nat := 1449585156039866510204503

theorem tailTrace_2823057 : CollatzResearch.WordTrace tailWord_2823057 prefixEnd_2823057 1449585156039866510204503 := by
  unfold tailWord_2823057
  simp only [CollatzResearch.WordTrace]
  refine ⟨102965347733554103595603425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68643565155702735730402283 102965347733554103595603425)
  ·
    refine ⟨77224010800165577696702569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102965347733554103595603425 77224010800165577696702569)
    ·
      refine ⟨57918008100124183272526927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77224010800165577696702569 57918008100124183272526927)
      ·
        refine ⟨86877012150186274908790391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57918008100124183272526927 86877012150186274908790391)
        ·
          refine ⟨130315518225279412363185587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86877012150186274908790391 130315518225279412363185587)
          ·
            refine ⟨195473277337919118544778381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130315518225279412363185587 195473277337919118544778381)
            ·
              refine ⟨73302479001719669454291893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 195473277337919118544778381 73302479001719669454291893)
              ·
                refine ⟨6872107406411219011339865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73302479001719669454291893 6872107406411219011339865)
                ·
                  refine ⟨5154080554808414258504899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6872107406411219011339865 5154080554808414258504899)
                  ·
                    refine ⟨7731120832212621387757349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5154080554808414258504899 7731120832212621387757349)
                    ·
                      refine ⟨1449585156039866510204503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7731120832212621387757349 1449585156039866510204503)
                      ·
                        rfl

theorem cell23_2823057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_2823057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823057 prefixEnd_2823057 := by exact prefixLift 2823057
  have htrace : WordTrace (prefixWord ++ tailWord_2823057) baseStart_2823057 baseEnd_2823057 := by
    simpa [prefixWord, tailWord_2823057, baseEnd_2823057] using wordTrace_append hprefix tailTrace_2823057
  have hstable : (prefixWord ++ tailWord_2823057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823057).length < 2 ^ (prefixWord ++ tailWord_2823057).sum := by decide
  have hdescent : baseEnd_2823057 < baseStart_2823057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823058 : List Nat := [3, 2, 3, 2, 2, 2, 1, 3, 5]
def baseStart_2823058 : Nat := 118140960795 + 2823058 * 2 ^ 59
def prefixEnd_2823058 : Nat := 4983230072969 + 3 ^ 40 * 2823058 * 2
def baseEnd_2823058 : Nat := 161065074391169000699111

theorem tailTrace_2823058 : CollatzResearch.WordTrace tailWord_2823058 prefixEnd_2823058 161065074391169000699111 := by
  unfold tailWord_2823058
  simp only [CollatzResearch.WordTrace]
  refine ⟨25741346051637620191597457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68643589471033653844259885 25741346051637620191597457)
  ·
    refine ⟨19306009538728215143698093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25741346051637620191597457 19306009538728215143698093)
    ·
      refine ⟨7239753577023080678886785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19306009538728215143698093 7239753577023080678886785)
      ·
        refine ⟨5429815182767310509165089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7239753577023080678886785 5429815182767310509165089)
        ·
          refine ⟨4072361387075482881873817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5429815182767310509165089 4072361387075482881873817)
          ·
            refine ⟨3054271040306612161405363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4072361387075482881873817 3054271040306612161405363)
            ·
              refine ⟨4581406560459918242108045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3054271040306612161405363 4581406560459918242108045)
              ·
                refine ⟨1718027460172469340790517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4581406560459918242108045 1718027460172469340790517)
                ·
                  refine ⟨161065074391169000699111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1718027460172469340790517 161065074391169000699111)
                  ·
                    rfl

theorem cell23_2823058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 3, 5].length) (baseStart_2823058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823058 prefixEnd_2823058 := by exact prefixLift 2823058
  have htrace : WordTrace (prefixWord ++ tailWord_2823058) baseStart_2823058 baseEnd_2823058 := by
    simpa [prefixWord, tailWord_2823058, baseEnd_2823058] using wordTrace_append hprefix tailTrace_2823058
  have hstable : (prefixWord ++ tailWord_2823058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823058).length < 2 ^ (prefixWord ++ tailWord_2823058).sum := by decide
  have hdescent : baseEnd_2823058 < baseStart_2823058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823074 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 4, 1, 4]
def baseStart_2823074 : Nat := 118140960795 + 2823074 * 2 ^ 59
def prefixEnd_2823074 : Nat := 4983230072969 + 3 ^ 40 * 2823074 * 2
def baseEnd_2823074 : Nat := 1449593885210992943691925

theorem tailTrace_2823074 : CollatzResearch.WordTrace tailWord_2823074 prefixEnd_2823074 1449593885210992943691925 := by
  unfold tailWord_2823074
  simp only [CollatzResearch.WordTrace]
  refine ⟨25741491943623128874743069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68643978516328343665981517 25741491943623128874743069)
  ·
    refine ⟨9653059478858673328028651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25741491943623128874743069 9653059478858673328028651)
    ·
      refine ⟨14479589218288009992042977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9653059478858673328028651 14479589218288009992042977)
      ·
        refine ⟨10859691913716007494032233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14479589218288009992042977 10859691913716007494032233)
        ·
          refine ⟨8144768935287005620524175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10859691913716007494032233 8144768935287005620524175)
          ·
            refine ⟨12217153402930508430786263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8144768935287005620524175 12217153402930508430786263)
            ·
              refine ⟨18325730104395762646179395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12217153402930508430786263 18325730104395762646179395)
              ·
                refine ⟨27488595156593643969269093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18325730104395762646179395 27488595156593643969269093)
                ·
                  refine ⟨5154111591861308244237955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27488595156593643969269093 5154111591861308244237955)
                  ·
                    refine ⟨7731167387791962366356933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5154111591861308244237955 7731167387791962366356933)
                    ·
                      refine ⟨1449593885210992943691925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7731167387791962366356933 1449593885210992943691925)
                      ·
                        rfl

theorem cell23_2823074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_2823074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823074 prefixEnd_2823074 := by exact prefixLift 2823074
  have htrace : WordTrace (prefixWord ++ tailWord_2823074) baseStart_2823074 baseEnd_2823074 := by
    simpa [prefixWord, tailWord_2823074, baseEnd_2823074] using wordTrace_append hprefix tailTrace_2823074
  have hstable : (prefixWord ++ tailWord_2823074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823074).length < 2 ^ (prefixWord ++ tailWord_2823074).sum := by decide
  have hdescent : baseEnd_2823074 < baseStart_2823074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823108 : List Nat := [2, 3, 3, 3, 1, 1, 2, 1, 2, 1, 4]
def baseStart_2823108 : Nat := 118140960795 + 2823108 * 2 ^ 59
def prefixEnd_2823108 : Nat := 4983230072969 + 3 ^ 40 * 2823108 * 2
def baseEnd_2823108 : Nat := 1449611343553245810666769

theorem tailTrace_2823108 : CollatzResearch.WordTrace tailWord_2823108 prefixEnd_2823108 1449611343553245810666769 := by
  unfold tailWord_2823108
  simp only [CollatzResearch.WordTrace]
  refine ⟨51483603928184669652854989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68644805237579559537139985 51483603928184669652854989)
  ·
    refine ⟨19306351473069251119820621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51483603928184669652854989 19306351473069251119820621)
    ·
      refine ⟨7239881802400969169932733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19306351473069251119820621 7239881802400969169932733)
      ·
        refine ⟨2714955675900363438724775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7239881802400969169932733 2714955675900363438724775)
        ·
          refine ⟨4072433513850545158087163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2714955675900363438724775 4072433513850545158087163)
          ·
            refine ⟨6108650270775817737130745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4072433513850545158087163 6108650270775817737130745)
            ·
              refine ⟨4581487703081863302848059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6108650270775817737130745 4581487703081863302848059)
              ·
                refine ⟨6872231554622794954272089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4581487703081863302848059 6872231554622794954272089)
                ·
                  refine ⟨5154173665967096215704067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6872231554622794954272089 5154173665967096215704067)
                  ·
                    refine ⟨7731260498950644323556101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5154173665967096215704067 7731260498950644323556101)
                    ·
                      refine ⟨1449611343553245810666769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7731260498950644323556101 1449611343553245810666769)
                      ·
                        rfl

theorem cell23_2823108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_2823108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823108 prefixEnd_2823108 := by exact prefixLift 2823108
  have htrace : WordTrace (prefixWord ++ tailWord_2823108) baseStart_2823108 baseEnd_2823108 := by
    simpa [prefixWord, tailWord_2823108, baseEnd_2823108] using wordTrace_append hprefix tailTrace_2823108
  have hstable : (prefixWord ++ tailWord_2823108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823108).length < 2 ^ (prefixWord ++ tailWord_2823108).sum := by decide
  have hdescent : baseEnd_2823108 < baseStart_2823108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823135 : List Nat := [1, 1, 2, 3, 5, 2, 2, 2, 1, 4]
def baseStart_2823135 : Nat := 118140960795 + 2823135 * 2 ^ 59
def prefixEnd_2823135 : Nat := 4983230072969 + 3 ^ 40 * 2823135 * 2
def baseEnd_2823135 : Nat := 483208402510305735009715

theorem tailTrace_2823135 : CollatzResearch.WordTrace tailWord_2823135 prefixEnd_2823135 483208402510305735009715 := by
  unfold tailWord_2823135
  simp only [CollatzResearch.WordTrace]
  refine ⟨102968192627271522916942859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68645461751514348611295239 102968192627271522916942859)
  ·
    refine ⟨154452288940907284375414289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102968192627271522916942859 154452288940907284375414289)
    ·
      refine ⟨115839216705680463281560717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154452288940907284375414289 115839216705680463281560717)
      ·
        refine ⟨43439706264630173730585269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115839216705680463281560717 43439706264630173730585269)
        ·
          refine ⟨4072472462309078787242369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43439706264630173730585269 4072472462309078787242369)
          ·
            refine ⟨3054354346731809090431777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4072472462309078787242369 3054354346731809090431777)
            ·
              refine ⟨2290765760048856817823833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3054354346731809090431777 2290765760048856817823833)
              ·
                refine ⟨1718074320036642613367875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2290765760048856817823833 1718074320036642613367875)
                ·
                  refine ⟨2577111480054963920051813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1718074320036642613367875 2577111480054963920051813)
                  ·
                    refine ⟨483208402510305735009715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2577111480054963920051813 483208402510305735009715)
                    ·
                      rfl

theorem cell23_2823135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 2, 1, 4].length) (baseStart_2823135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823135 prefixEnd_2823135 := by exact prefixLift 2823135
  have htrace : WordTrace (prefixWord ++ tailWord_2823135) baseStart_2823135 baseEnd_2823135 := by
    simpa [prefixWord, tailWord_2823135, baseEnd_2823135] using wordTrace_append hprefix tailTrace_2823135
  have hstable : (prefixWord ++ tailWord_2823135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823135).length < 2 ^ (prefixWord ++ tailWord_2823135).sum := by decide
  have hdescent : baseEnd_2823135 < baseStart_2823135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823158 : List Nat := [5, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3]
def baseStart_2823158 : Nat := 118140960795 + 2823158 * 2 ^ 59
def prefixEnd_2823158 : Nat := 4983230072969 + 3 ^ 40 * 2823158 * 2
def baseEnd_2823158 : Nat := 1449637017585970615041539

theorem tailTrace_2823158 : CollatzResearch.WordTrace tailWord_2823158 prefixEnd_2823158 1449637017585970615041539 := by
  unfold tailWord_2823158
  simp only [CollatzResearch.WordTrace]
  refine ⟨6435564469136762365314383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68646021004125465230020085 6435564469136762365314383)
  ·
    refine ⟨9653346703705143547971575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6435564469136762365314383 9653346703705143547971575)
    ·
      refine ⟨14480020055557715321957363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9653346703705143547971575 14480020055557715321957363)
      ·
        refine ⟨21720030083336572982936045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14480020055557715321957363 21720030083336572982936045)
        ·
          refine ⟨8145011281251214868601017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21720030083336572982936045 8145011281251214868601017)
          ·
            refine ⟨6108758460938411151450763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8145011281251214868601017 6108758460938411151450763)
            ·
              refine ⟨9163137691407616727176145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6108758460938411151450763 9163137691407616727176145)
              ·
                refine ⟨6872353268555712545382109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9163137691407616727176145 6872353268555712545382109)
                ·
                  refine ⟨2577132475708392204518291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6872353268555712545382109 2577132475708392204518291)
                  ·
                    refine ⟨3865698713562588306777437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2577132475708392204518291 3865698713562588306777437)
                    ·
                      refine ⟨1449637017585970615041539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3865698713562588306777437 1449637017585970615041539)
                      ·
                        rfl

theorem cell23_2823158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_2823158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823158 prefixEnd_2823158 := by exact prefixLift 2823158
  have htrace : WordTrace (prefixWord ++ tailWord_2823158) baseStart_2823158 baseEnd_2823158 := by
    simpa [prefixWord, tailWord_2823158, baseEnd_2823158] using wordTrace_append hprefix tailTrace_2823158
  have hstable : (prefixWord ++ tailWord_2823158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823158).length < 2 ^ (prefixWord ++ tailWord_2823158).sum := by decide
  have hdescent : baseEnd_2823158 < baseStart_2823158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823164 : List Nat := [2, 2, 2, 1, 2, 3, 2, 1, 3, 1, 4]
def baseStart_2823164 : Nat := 118140960795 + 2823164 * 2 ^ 59
def prefixEnd_2823164 : Nat := 4983230072969 + 3 ^ 40 * 2823164 * 2
def baseEnd_2823164 : Nat := 1449640098469897591566511

theorem tailTrace_2823164 : CollatzResearch.WordTrace tailWord_2823164 prefixEnd_2823164 1449640098469897591566511 := by
  unfold tailWord_2823164
  simp only [CollatzResearch.WordTrace]
  refine ⟨51484625172083230434874273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68646166896110973913165697 51484625172083230434874273)
  ·
    refine ⟨38613468879062422826155705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51484625172083230434874273 38613468879062422826155705)
    ·
      refine ⟨28960101659296817119616779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38613468879062422826155705 28960101659296817119616779)
      ·
        refine ⟨43440152488945225679425169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28960101659296817119616779 43440152488945225679425169)
        ·
          refine ⟨32580114366708919259568877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43440152488945225679425169 32580114366708919259568877)
          ·
            refine ⟨12217542887515844722338329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32580114366708919259568877 12217542887515844722338329)
            ·
              refine ⟨9163157165636883541753747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12217542887515844722338329 9163157165636883541753747)
              ·
                refine ⟨13744735748455325312630621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9163157165636883541753747 13744735748455325312630621)
                ·
                  refine ⟨5154275905670746992236483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13744735748455325312630621 5154275905670746992236483)
                  ·
                    refine ⟨7731413858506120488354725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5154275905670746992236483 7731413858506120488354725)
                    ·
                      refine ⟨1449640098469897591566511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7731413858506120488354725 1449640098469897591566511)
                      ·
                        rfl

theorem cell23_2823164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_2823164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823164 prefixEnd_2823164 := by exact prefixLift 2823164
  have htrace : WordTrace (prefixWord ++ tailWord_2823164) baseStart_2823164 baseEnd_2823164 := by
    simpa [prefixWord, tailWord_2823164, baseEnd_2823164] using wordTrace_append hprefix tailTrace_2823164
  have hstable : (prefixWord ++ tailWord_2823164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823164).length < 2 ^ (prefixWord ++ tailWord_2823164).sum := by decide
  have hdescent : baseEnd_2823164 < baseStart_2823164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823178 : List Nat := [3, 1, 2, 2, 3, 3, 2, 1, 1, 5]
def baseStart_2823178 : Nat := 118140960795 + 2823178 * 2 ^ 59
def prefixEnd_2823178 : Nat := 4983230072969 + 3 ^ 40 * 2823178 * 2
def baseEnd_2823178 : Nat := 483215762399686845597149

theorem tailTrace_2823178 : CollatzResearch.WordTrace tailWord_2823178 prefixEnd_2823178 483215762399686845597149 := by
  unfold tailWord_2823178
  simp only [CollatzResearch.WordTrace]
  refine ⟨25742440241528935315189547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68646507310743827507172125 25742440241528935315189547)
  ·
    refine ⟨38613660362293402972784321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25742440241528935315189547 38613660362293402972784321)
    ·
      refine ⟨28960245271720052229588241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38613660362293402972784321 28960245271720052229588241)
      ·
        refine ⟨21720183953790039172191181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28960245271720052229588241 21720183953790039172191181)
        ·
          refine ⟨8145068982671264689571693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21720183953790039172191181 8145068982671264689571693)
          ·
            refine ⟨3054400868501724258589385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8145068982671264689571693 3054400868501724258589385)
            ·
              refine ⟨2290800651376293193942039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3054400868501724258589385 2290800651376293193942039)
              ·
                refine ⟨3436200977064439790913059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2290800651376293193942039 3436200977064439790913059)
                ·
                  refine ⟨5154301465596659686369589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3436200977064439790913059 5154301465596659686369589)
                  ·
                    refine ⟨483215762399686845597149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5154301465596659686369589 483215762399686845597149)
                    ·
                      rfl

theorem cell23_2823178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_2823178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823178 prefixEnd_2823178 := by exact prefixLift 2823178
  have htrace : WordTrace (prefixWord ++ tailWord_2823178) baseStart_2823178 baseEnd_2823178 := by
    simpa [prefixWord, tailWord_2823178, baseEnd_2823178] using wordTrace_append hprefix tailTrace_2823178
  have hstable : (prefixWord ++ tailWord_2823178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823178).length < 2 ^ (prefixWord ++ tailWord_2823178).sum := by decide
  have hdescent : baseEnd_2823178 < baseStart_2823178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823191 : List Nat := [1, 1, 3, 5, 1, 2, 1, 1, 4, 4]
def baseStart_2823191 : Nat := 118140960795 + 2823191 * 2 ^ 59
def prefixEnd_2823191 : Nat := 4983230072969 + 3 ^ 40 * 2823191 * 2
def baseEnd_2823191 : Nat := 483217987482522995309629

theorem tailTrace_2823191 : CollatzResearch.WordTrace tailWord_2823191 prefixEnd_2823191 483217987482522995309629 := by
  unfold tailWord_2823191
  simp only [CollatzResearch.WordTrace]
  refine ⟨102970235115068644480981427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68646823410045762987320951 102970235115068644480981427)
  ·
    refine ⟨154455352672602966721472141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102970235115068644480981427 154455352672602966721472141)
    ·
      refine ⟨57920757252226112520552053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154455352672602966721472141 57920757252226112520552053)
      ·
        refine ⟨5430070992396198048801755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57920757252226112520552053 5430070992396198048801755)
        ·
          refine ⟨8145106488594297073202633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5430070992396198048801755 8145106488594297073202633)
          ·
            refine ⟨6108829866445722804901975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8145106488594297073202633 6108829866445722804901975)
            ·
              refine ⟨9163244799668584207352963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6108829866445722804901975 9163244799668584207352963)
              ·
                refine ⟨13744867199502876311029445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9163244799668584207352963 13744867199502876311029445)
                ·
                  refine ⟨2577162599906789308318021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13744867199502876311029445 2577162599906789308318021)
                  ·
                    refine ⟨483217987482522995309629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2577162599906789308318021 483217987482522995309629)
                    ·
                      rfl

theorem cell23_2823191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 4, 4].length) (baseStart_2823191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823191 prefixEnd_2823191 := by exact prefixLift 2823191
  have htrace : WordTrace (prefixWord ++ tailWord_2823191) baseStart_2823191 baseEnd_2823191 := by
    simpa [prefixWord, tailWord_2823191, baseEnd_2823191] using wordTrace_append hprefix tailTrace_2823191
  have hstable : (prefixWord ++ tailWord_2823191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823191).length < 2 ^ (prefixWord ++ tailWord_2823191).sum := by decide
  have hdescent : baseEnd_2823191 < baseStart_2823191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823305 : List Nat := [1, 2, 1, 1, 4, 4, 2, 2, 2, 2, 2]
def baseStart_2823305 : Nat := 118140960795 + 2823305 * 2 ^ 59
def prefixEnd_2823305 : Nat := 4983230072969 + 3 ^ 40 * 2823305 * 2
def baseEnd_2823305 : Nat := 1449712499242181539903363

theorem tailTrace_2823305 : CollatzResearch.WordTrace tailWord_2823305 prefixEnd_2823305 1449712499242181539903363 := by
  unfold tailWord_2823305
  simp only [CollatzResearch.WordTrace]
  refine ⟨102974393036655641950631369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68649595357770427967087579 102974393036655641950631369)
  ·
    refine ⟨77230794777491731462973527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102974393036655641950631369 77230794777491731462973527)
    ·
      refine ⟨115846192166237597194460291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77230794777491731462973527 115846192166237597194460291)
      ·
        refine ⟨173769288249356395791690437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115846192166237597194460291 173769288249356395791690437)
        ·
          refine ⟨32581741546754324210941957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173769288249356395791690437 32581741546754324210941957)
          ·
            refine ⟨6109076540016435789551617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32581741546754324210941957 6109076540016435789551617)
            ·
              refine ⟨4581807405012326842163713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6109076540016435789551617 4581807405012326842163713)
              ·
                refine ⟨3436355553759245131622785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4581807405012326842163713 3436355553759245131622785)
                ·
                  refine ⟨2577266665319433848717089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3436355553759245131622785 2577266665319433848717089)
                  ·
                    refine ⟨1932949998989575386537817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2577266665319433848717089 1932949998989575386537817)
                    ·
                      refine ⟨1449712499242181539903363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1932949998989575386537817 1449712499242181539903363)
                      ·
                        rfl

theorem cell23_2823305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 2, 2, 2].length) (baseStart_2823305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823305 prefixEnd_2823305 := by exact prefixLift 2823305
  have htrace : WordTrace (prefixWord ++ tailWord_2823305) baseStart_2823305 baseEnd_2823305 := by
    simpa [prefixWord, tailWord_2823305, baseEnd_2823305] using wordTrace_append hprefix tailTrace_2823305
  have hstable : (prefixWord ++ tailWord_2823305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823305).length < 2 ^ (prefixWord ++ tailWord_2823305).sum := by decide
  have hdescent : baseEnd_2823305 < baseStart_2823305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823344 : List Nat := [2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 4]
def baseStart_2823344 : Nat := 118140960795 + 2823344 * 2 ^ 59
def prefixEnd_2823344 : Nat := 4983230072969 + 3 ^ 40 * 2823344 * 2
def baseEnd_2823344 : Nat := 1449732524987706887315683

theorem tailTrace_2823344 : CollatzResearch.WordTrace tailWord_2823344 prefixEnd_2823344 1449732524987706887315683 := by
  unfold tailWord_2823344
  simp only [CollatzResearch.WordTrace]
  refine ⟨51487907741757175805650543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68650543655676234407534057 51487907741757175805650543)
  ·
    refine ⟨77231861612635763708475815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51487907741757175805650543 77231861612635763708475815)
    ·
      refine ⟨115847792418953645562713723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77231861612635763708475815 115847792418953645562713723)
      ·
        refine ⟨173771688628430468344070585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115847792418953645562713723 173771688628430468344070585)
        ·
          refine ⟨130328766471322851258052939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173771688628430468344070585 130328766471322851258052939)
          ·
            refine ⟨195493149706984276887079409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130328766471322851258052939 195493149706984276887079409)
            ·
              refine ⟨146619862280238207665309557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195493149706984276887079409 146619862280238207665309557)
              ·
                refine ⟨13745612088772331968622771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 146619862280238207665309557 13745612088772331968622771)
                ·
                  refine ⟨20618418133158497952934157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13745612088772331968622771 20618418133158497952934157)
                  ·
                    refine ⟨7731906799934436732350309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20618418133158497952934157 7731906799934436732350309)
                    ·
                      refine ⟨1449732524987706887315683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7731906799934436732350309 1449732524987706887315683)
                      ·
                        rfl

theorem cell23_2823344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 4].length) (baseStart_2823344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823344 prefixEnd_2823344 := by exact prefixLift 2823344
  have htrace : WordTrace (prefixWord ++ tailWord_2823344) baseStart_2823344 baseEnd_2823344 := by
    simpa [prefixWord, tailWord_2823344, baseEnd_2823344] using wordTrace_append hprefix tailTrace_2823344
  have hstable : (prefixWord ++ tailWord_2823344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823344).length < 2 ^ (prefixWord ++ tailWord_2823344).sum := by decide
  have hdescent : baseEnd_2823344 < baseStart_2823344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823378 : List Nat := [3, 2, 2, 2, 1, 1, 1, 3, 2, 4, 2]
def baseStart_2823378 : Nat := 118140960795 + 2823378 * 2 ^ 59
def prefixEnd_2823378 : Nat := 4983230072969 + 3 ^ 40 * 2823378 * 2
def baseEnd_2823378 : Nat := 1449749983329959754290527

theorem tailTrace_2823378 : CollatzResearch.WordTrace tailWord_2823378 prefixEnd_2823378 1449749983329959754290527 := by
  unfold tailWord_2823378
  simp only [CollatzResearch.WordTrace]
  refine ⟨25744263891347793854509697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68651370376927450278692525 25744263891347793854509697)
  ·
    refine ⟨19308197918510845390882273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25744263891347793854509697 19308197918510845390882273)
    ·
      refine ⟨14481148438883134043161705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19308197918510845390882273 14481148438883134043161705)
      ·
        refine ⟨10860861329162350532371279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14481148438883134043161705 10860861329162350532371279)
        ·
          refine ⟨16291291993743525798556919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10860861329162350532371279 16291291993743525798556919)
          ·
            refine ⟨24436937990615288697835379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16291291993743525798556919 24436937990615288697835379)
            ·
              refine ⟨36655406985922933046753069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24436937990615288697835379 36655406985922933046753069)
              ·
                refine ⟨13745777619721099892532401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36655406985922933046753069 13745777619721099892532401)
                ·
                  refine ⟨10309333214790824919399301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13745777619721099892532401 10309333214790824919399301)
                  ·
                    refine ⟨1932999977773279672387369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10309333214790824919399301 1932999977773279672387369)
                    ·
                      refine ⟨1449749983329959754290527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1932999977773279672387369 1449749983329959754290527)
                      ·
                        rfl

theorem cell23_2823378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_2823378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823378 prefixEnd_2823378 := by exact prefixLift 2823378
  have htrace : WordTrace (prefixWord ++ tailWord_2823378) baseStart_2823378 baseEnd_2823378 := by
    simpa [prefixWord, tailWord_2823378, baseEnd_2823378] using wordTrace_append hprefix tailTrace_2823378
  have hstable : (prefixWord ++ tailWord_2823378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823378).length < 2 ^ (prefixWord ++ tailWord_2823378).sum := by decide
  have hdescent : baseEnd_2823378 < baseStart_2823378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823424 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 7]
def baseStart_2823424 : Nat := 118140960795 + 2823424 * 2 ^ 59
def prefixEnd_2823424 : Nat := 4983230072969 + 3 ^ 40 * 2823424 * 2
def baseEnd_2823424 : Nat := 1449773603440066574315315

theorem tailTrace_2823424 : CollatzResearch.WordTrace tailWord_2823424 prefixEnd_2823424 1449773603440066574315315 := by
  unfold tailWord_2823424
  simp only [CollatzResearch.WordTrace]
  refine ⟨51489366661612262637106663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68652488882149683516142217 51489366661612262637106663)
  ·
    refine ⟨77234049992418393955659995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51489366661612262637106663 77234049992418393955659995)
    ·
      refine ⟨115851074988627590933489993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77234049992418393955659995 115851074988627590933489993)
      ·
        refine ⟨86888306241470693200117495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115851074988627590933489993 86888306241470693200117495)
        ·
          refine ⟨130332459362206039800176243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86888306241470693200117495 130332459362206039800176243)
          ·
            refine ⟨195498689043309059700264365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130332459362206039800176243 195498689043309059700264365)
            ·
              refine ⟨73312008391240897387599137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 195498689043309059700264365 73312008391240897387599137)
              ·
                refine ⟨54984006293430673040699353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73312008391240897387599137 54984006293430673040699353)
                ·
                  refine ⟨41238004720073004780524515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54984006293430673040699353 41238004720073004780524515)
                  ·
                    refine ⟨61857007080109507170786773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41238004720073004780524515 61857007080109507170786773)
                    ·
                      refine ⟨1449773603440066574315315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 61857007080109507170786773 1449773603440066574315315)
                      ·
                        rfl

theorem cell23_2823424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_2823424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823424 prefixEnd_2823424 := by exact prefixLift 2823424
  have htrace : WordTrace (prefixWord ++ tailWord_2823424) baseStart_2823424 baseEnd_2823424 := by
    simpa [prefixWord, tailWord_2823424, baseEnd_2823424] using wordTrace_append hprefix tailTrace_2823424
  have hstable : (prefixWord ++ tailWord_2823424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823424).length < 2 ^ (prefixWord ++ tailWord_2823424).sum := by decide
  have hdescent : baseEnd_2823424 < baseStart_2823424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823448 : List Nat := [2, 1, 2, 3, 1, 3, 3, 2, 1, 5]
def baseStart_2823448 : Nat := 118140960795 + 2823448 * 2 ^ 59
def prefixEnd_2823448 : Nat := 4983230072969 + 3 ^ 40 * 2823448 * 2
def baseEnd_2823448 : Nat := 483261975658591493471735

theorem tailTrace_2823448 : CollatzResearch.WordTrace tailWord_2823448 prefixEnd_2823448 483261975658591493471735 := by
  unfold tailWord_2823448
  simp only [CollatzResearch.WordTrace]
  refine ⟨51489804337568788686543499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68653072450091718248724665 51489804337568788686543499)
  ·
    refine ⟨77234706506353183029815249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51489804337568788686543499 77234706506353183029815249)
    ·
      refine ⟨57926029879764887272361437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77234706506353183029815249 57926029879764887272361437)
      ·
        refine ⟨21722261204911832727135539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57926029879764887272361437 21722261204911832727135539)
        ·
          refine ⟨32583391807367749090703309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21722261204911832727135539 32583391807367749090703309)
          ·
            refine ⟨12218771927762905909013741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32583391807367749090703309 12218771927762905909013741)
            ·
              refine ⟨4582039472911089715880153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12218771927762905909013741 4582039472911089715880153)
              ·
                refine ⟨3436529604683317286910115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4582039472911089715880153 3436529604683317286910115)
                ·
                  refine ⟨5154794407024975930365173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3436529604683317286910115 5154794407024975930365173)
                  ·
                    refine ⟨483261975658591493471735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5154794407024975930365173 483261975658591493471735)
                    ·
                      rfl

theorem cell23_2823448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 1, 5].length) (baseStart_2823448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823448 prefixEnd_2823448 := by exact prefixLift 2823448
  have htrace : WordTrace (prefixWord ++ tailWord_2823448) baseStart_2823448 baseEnd_2823448 := by
    simpa [prefixWord, tailWord_2823448, baseEnd_2823448] using wordTrace_append hprefix tailTrace_2823448
  have hstable : (prefixWord ++ tailWord_2823448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823448).length < 2 ^ (prefixWord ++ tailWord_2823448).sum := by decide
  have hdescent : baseEnd_2823448 < baseStart_2823448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823461 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 3, 6]
def baseStart_2823461 : Nat := 118140960795 + 2823461 * 2 ^ 59
def prefixEnd_2823461 : Nat := 4983230072969 + 3 ^ 40 * 2823461 * 2
def baseEnd_2823461 : Nat := 483264200741427643184215

theorem tailTrace_2823461 : CollatzResearch.WordTrace tailWord_2823461 prefixEnd_2823461 483264200741427643184215 := by
  unfold tailWord_2823461
  simp only [CollatzResearch.WordTrace]
  refine ⟨102980082824090480593310237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68653388549393653728873491 102980082824090480593310237)
  ·
    refine ⟨38617531059033930222491339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102980082824090480593310237 38617531059033930222491339)
    ·
      refine ⟨57926296588550895333737009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38617531059033930222491339 57926296588550895333737009)
      ·
        refine ⟨43444722441413171500302757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57926296588550895333737009 43444722441413171500302757)
        ·
          refine ⟨8145885457764969656306767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43444722441413171500302757 8145885457764969656306767)
          ·
            refine ⟨12218828186647454484460151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8145885457764969656306767 12218828186647454484460151)
            ·
              refine ⟨18328242279971181726690227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12218828186647454484460151 18328242279971181726690227)
              ·
                refine ⟨27492363419956772590035341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18328242279971181726690227 27492363419956772590035341)
                ·
                  refine ⟨10309636282483789721263253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27492363419956772590035341 10309636282483789721263253)
                  ·
                    refine ⟨483264200741427643184215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10309636282483789721263253 483264200741427643184215)
                    ·
                      rfl

theorem cell23_2823461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 6].length) (baseStart_2823461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823461 prefixEnd_2823461 := by exact prefixLift 2823461
  have htrace : WordTrace (prefixWord ++ tailWord_2823461) baseStart_2823461 baseEnd_2823461 := by
    simpa [prefixWord, tailWord_2823461, baseEnd_2823461] using wordTrace_append hprefix tailTrace_2823461
  have hstable : (prefixWord ++ tailWord_2823461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823461).length < 2 ^ (prefixWord ++ tailWord_2823461).sum := by decide
  have hdescent : baseEnd_2823461 < baseStart_2823461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823508 : List Nat := [2, 4, 1, 1, 2, 1, 5, 7]
def baseStart_2823508 : Nat := 118140960795 + 2823508 * 2 ^ 59
def prefixEnd_2823508 : Nat := 4983230072969 + 3 ^ 40 * 2823508 * 2
def baseEnd_2823508 : Nat := 53696916141297935024627

theorem tailTrace_2823508 : CollatzResearch.WordTrace tailWord_2823508 prefixEnd_2823508 53696916141297935024627 := by
  unfold tailWord_2823508
  simp only [CollatzResearch.WordTrace]
  refine ⟨51490898527460103810135589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68654531369946805080180785 51490898527460103810135589)
  ·
    refine ⟨9654543473898769464400423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51490898527460103810135589 9654543473898769464400423)
    ·
      refine ⟨14481815210848154196600635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9654543473898769464400423 14481815210848154196600635)
      ·
        refine ⟨21722722816272231294900953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14481815210848154196600635 21722722816272231294900953)
        ·
          refine ⟨16292042112204173471175715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21722722816272231294900953 16292042112204173471175715)
          ·
            refine ⟨24438063168306260206763573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16292042112204173471175715 24438063168306260206763573)
            ·
              refine ⟨2291068422028711894384085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24438063168306260206763573 2291068422028711894384085)
              ·
                refine ⟨53696916141297935024627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2291068422028711894384085 53696916141297935024627)
                ·
                  rfl

theorem cell23_2823508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 7].length) (baseStart_2823508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823508 prefixEnd_2823508 := by exact prefixLift 2823508
  have htrace : WordTrace (prefixWord ++ tailWord_2823508) baseStart_2823508 baseEnd_2823508 := by
    simpa [prefixWord, tailWord_2823508, baseEnd_2823508] using wordTrace_append hprefix tailTrace_2823508
  have hstable : (prefixWord ++ tailWord_2823508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823508).length < 2 ^ (prefixWord ++ tailWord_2823508).sum := by decide
  have hdescent : baseEnd_2823508 < baseStart_2823508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823570 : List Nat := [3, 2, 3, 3, 2, 1, 1, 3, 1, 2, 2]
def baseStart_2823570 : Nat := 118140960795 + 2823570 * 2 ^ 59
def prefixEnd_2823570 : Nat := 4983230072969 + 3 ^ 40 * 2823570 * 2
def baseEnd_2823570 : Nat := 1449848571615623003089645

theorem tailTrace_2823570 : CollatzResearch.WordTrace tailWord_2823570 prefixEnd_2823570 1449848571615623003089645 := by
  unfold tailWord_2823570
  simp only [CollatzResearch.WordTrace]
  refine ⟨25746014595173898052257041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68656038920463728139352109 25746014595173898052257041)
  ·
    refine ⟨19309510946380423539192781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25746014595173898052257041 19309510946380423539192781)
    ·
      refine ⟨7241066604892658827197293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19309510946380423539192781 7241066604892658827197293)
      ·
        refine ⟨2715399976834747060198985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7241066604892658827197293 2715399976834747060198985)
        ·
          refine ⟨2036549982626060295149239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2715399976834747060198985 2036549982626060295149239)
          ·
            refine ⟨3054824973939090442723859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2036549982626060295149239 3054824973939090442723859)
            ·
              refine ⟨4582237460908635664085789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3054824973939090442723859 4582237460908635664085789)
              ·
                refine ⟨1718339047840738374032171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4582237460908635664085789 1718339047840738374032171)
                ·
                  refine ⟨2577508571761107561048257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1718339047840738374032171 2577508571761107561048257)
                  ·
                    refine ⟨1933131428820830670786193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2577508571761107561048257 1933131428820830670786193)
                    ·
                      refine ⟨1449848571615623003089645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1933131428820830670786193 1449848571615623003089645)
                      ·
                        rfl

theorem cell23_2823570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_2823570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823570 prefixEnd_2823570 := by exact prefixLift 2823570
  have htrace : WordTrace (prefixWord ++ tailWord_2823570) baseStart_2823570 baseEnd_2823570 := by
    simpa [prefixWord, tailWord_2823570, baseEnd_2823570] using wordTrace_append hprefix tailTrace_2823570
  have hstable : (prefixWord ++ tailWord_2823570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823570).length < 2 ^ (prefixWord ++ tailWord_2823570).sum := by decide
  have hdescent : baseEnd_2823570 < baseStart_2823570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823578 : List Nat := [3, 1, 1, 4, 1, 1, 3, 1, 2, 1, 5]
def baseStart_2823578 : Nat := 118140960795 + 2823578 * 2 ^ 59
def prefixEnd_2823578 : Nat := 4983230072969 + 3 ^ 40 * 2823578 * 2
def baseEnd_2823578 : Nat := 1449852679460858971789607

theorem tailTrace_2823578 : CollatzResearch.WordTrace tailWord_2823578 prefixEnd_2823578 1449852679460858971789607 := by
  unfold tailWord_2823578
  simp only [CollatzResearch.WordTrace]
  refine ⟨25746087541166652393829847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68656233443111073050212925 25746087541166652393829847)
  ·
    refine ⟨38619131311749978590744771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25746087541166652393829847 38619131311749978590744771)
    ·
      refine ⟨57928696967624967886117157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38619131311749978590744771 57928696967624967886117157)
      ·
        refine ⟨10861630681429681478646967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57928696967624967886117157 10861630681429681478646967)
        ·
          refine ⟨16292446022144522217970451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10861630681429681478646967 16292446022144522217970451)
          ·
            refine ⟨24438669033216783326955677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16292446022144522217970451 24438669033216783326955677)
            ·
              refine ⟨9164500887456293747608379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24438669033216783326955677 9164500887456293747608379)
              ·
                refine ⟨13746751331184440621412569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9164500887456293747608379 13746751331184440621412569)
                ·
                  refine ⟨10310063498388330466059427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13746751331184440621412569 10310063498388330466059427)
                  ·
                    refine ⟨15465095247582495699089141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10310063498388330466059427 15465095247582495699089141)
                    ·
                      refine ⟨1449852679460858971789607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15465095247582495699089141 1449852679460858971789607)
                      ·
                        rfl

theorem cell23_2823578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_2823578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823578 prefixEnd_2823578 := by exact prefixLift 2823578
  have htrace : WordTrace (prefixWord ++ tailWord_2823578) baseStart_2823578 baseEnd_2823578 := by
    simpa [prefixWord, tailWord_2823578, baseEnd_2823578] using wordTrace_append hprefix tailTrace_2823578
  have hstable : (prefixWord ++ tailWord_2823578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823578).length < 2 ^ (prefixWord ++ tailWord_2823578).sum := by decide
  have hdescent : baseEnd_2823578 < baseStart_2823578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823608 : List Nat := [2, 1, 2, 1, 2, 2, 2, 3, 2, 3, 3]
def baseStart_2823608 : Nat := 118140960795 + 2823608 * 2 ^ 59
def prefixEnd_2823608 : Nat := 4983230072969 + 3 ^ 40 * 2823608 * 2
def baseEnd_2823608 : Nat := 1449868083880493854414469

theorem tailTrace_2823608 : CollatzResearch.WordTrace tailWord_2823608 prefixEnd_2823608 1449868083880493854414469 := by
  unfold tailWord_2823608
  simp only [CollatzResearch.WordTrace]
  refine ⟨51492722177278962349455739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68656962903038616465940985 51492722177278962349455739)
  ·
    refine ⟨77239083265918443524183609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51492722177278962349455739 77239083265918443524183609)
    ·
      refine ⟨57929312449438832643137707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77239083265918443524183609 57929312449438832643137707)
      ·
        refine ⟨86893968674158248964706561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57929312449438832643137707 86893968674158248964706561)
        ·
          refine ⟨65170476505618686723529921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86893968674158248964706561 65170476505618686723529921)
          ·
            refine ⟨48877857379214015042647441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65170476505618686723529921 48877857379214015042647441)
            ·
              refine ⟨36658393034410511281985581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48877857379214015042647441 36658393034410511281985581)
              ·
                refine ⟨13746897387903941730744593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36658393034410511281985581 13746897387903941730744593)
                ·
                  refine ⟨10310173040927956298058445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13746897387903941730744593 10310173040927956298058445)
                  ·
                    refine ⟨3866314890347983611771917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10310173040927956298058445 3866314890347983611771917)
                    ·
                      refine ⟨1449868083880493854414469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3866314890347983611771917 1449868083880493854414469)
                      ·
                        rfl

theorem cell23_2823608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 2, 3, 3].length) (baseStart_2823608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823608 prefixEnd_2823608 := by exact prefixLift 2823608
  have htrace : WordTrace (prefixWord ++ tailWord_2823608) baseStart_2823608 baseEnd_2823608 := by
    simpa [prefixWord, tailWord_2823608, baseEnd_2823608] using wordTrace_append hprefix tailTrace_2823608
  have hstable : (prefixWord ++ tailWord_2823608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823608).length < 2 ^ (prefixWord ++ tailWord_2823608).sum := by decide
  have hdescent : baseEnd_2823608 < baseStart_2823608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823609 : List Nat := [1, 2, 1, 4, 4, 1, 1, 3, 2, 2, 2]
def baseStart_2823609 : Nat := 118140960795 + 2823609 * 2 ^ 59
def prefixEnd_2823609 : Nat := 4983230072969 + 3 ^ 40 * 2823609 * 2
def baseEnd_2823609 : Nat := 1449868597361148350501965

theorem tailTrace_2823609 : CollatzResearch.WordTrace tailWord_2823609 prefixEnd_2823609 1449868597361148350501965 := by
  unfold tailWord_2823609
  simp only [CollatzResearch.WordTrace]
  refine ⟨102985480827554301869697881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68656987218369534579798587 102985480827554301869697881)
  ·
    refine ⟨77239110620665726402273411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102985480827554301869697881 77239110620665726402273411)
    ·
      refine ⟨115858665930998589603410117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77239110620665726402273411 115858665930998589603410117)
      ·
        refine ⟨21723499862062235550639397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115858665930998589603410117 21723499862062235550639397)
        ·
          refine ⟨4073156224136669165744887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21723499862062235550639397 4073156224136669165744887)
          ·
            refine ⟨6109734336205003748617331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4073156224136669165744887 6109734336205003748617331)
            ·
              refine ⟨9164601504307505622925997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6109734336205003748617331 9164601504307505622925997)
              ·
                refine ⟨3436725564115314608597249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9164601504307505622925997 3436725564115314608597249)
                ·
                  refine ⟨2577544173086485956447937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3436725564115314608597249 2577544173086485956447937)
                  ·
                    refine ⟨1933158129814864467335953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2577544173086485956447937 1933158129814864467335953)
                    ·
                      refine ⟨1449868597361148350501965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1933158129814864467335953 1449868597361148350501965)
                      ·
                        rfl

theorem cell23_2823609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_2823609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823609 prefixEnd_2823609 := by exact prefixLift 2823609
  have htrace : WordTrace (prefixWord ++ tailWord_2823609) baseStart_2823609 baseEnd_2823609 := by
    simpa [prefixWord, tailWord_2823609, baseEnd_2823609] using wordTrace_append hprefix tailTrace_2823609
  have hstable : (prefixWord ++ tailWord_2823609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823609).length < 2 ^ (prefixWord ++ tailWord_2823609).sum := by decide
  have hdescent : baseEnd_2823609 < baseStart_2823609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823645 : List Nat := [1, 4, 3, 1, 1, 2, 2, 2, 2, 5]
def baseStart_2823645 : Nat := 118140960795 + 2823645 * 2 ^ 59
def prefixEnd_2823645 : Nat := 4983230072969 + 3 ^ 40 * 2823645 * 2
def baseEnd_2823645 : Nat := 483295694221570069883933

theorem tailTrace_2823645 : CollatzResearch.WordTrace tailWord_2823645 prefixEnd_2823645 483295694221570069883933 := by
  unfold tailWord_2823645
  simp only [CollatzResearch.WordTrace]
  refine ⟨102986793855423880018008389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68657862570282586678672259 102986793855423880018008389)
  ·
    refine ⟨19310023847891977503376573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102986793855423880018008389 19310023847891977503376573)
    ·
      refine ⟨7241258942959491563766215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19310023847891977503376573 7241258942959491563766215)
      ·
        refine ⟨10861888414439237345649323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7241258942959491563766215 10861888414439237345649323)
        ·
          refine ⟨16292832621658856018473985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10861888414439237345649323 16292832621658856018473985)
          ·
            refine ⟨12219624466244142013855489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16292832621658856018473985 12219624466244142013855489)
            ·
              refine ⟨9164718349683106510391617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12219624466244142013855489 9164718349683106510391617)
              ·
                refine ⟨6873538762262329882793713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9164718349683106510391617 6873538762262329882793713)
                ·
                  refine ⟨5155154071696747412095285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6873538762262329882793713 5155154071696747412095285)
                  ·
                    refine ⟨483295694221570069883933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5155154071696747412095285 483295694221570069883933)
                    ·
                      rfl

theorem cell23_2823645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_2823645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823645 prefixEnd_2823645 := by exact prefixLift 2823645
  have htrace : WordTrace (prefixWord ++ tailWord_2823645) baseStart_2823645 baseEnd_2823645 := by
    simpa [prefixWord, tailWord_2823645, baseEnd_2823645] using wordTrace_append hprefix tailTrace_2823645
  have hstable : (prefixWord ++ tailWord_2823645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823645).length < 2 ^ (prefixWord ++ tailWord_2823645).sum := by decide
  have hdescent : baseEnd_2823645 < baseStart_2823645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823648 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 4]
def baseStart_2823648 : Nat := 118140960795 + 2823648 * 2 ^ 59
def prefixEnd_2823648 : Nat := 4983230072969 + 3 ^ 40 * 2823648 * 2
def baseEnd_2823648 : Nat := 1449888623106673697914285

theorem tailTrace_2823648 : CollatzResearch.WordTrace tailWord_2823648 prefixEnd_2823648 1449888623106673697914285 := by
  unfold tailWord_2823648
  simp only [CollatzResearch.WordTrace]
  refine ⟨51493451637206505765183799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68657935516275341020245065 51493451637206505765183799)
  ·
    refine ⟨77240177455809758647775699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51493451637206505765183799 77240177455809758647775699)
    ·
      refine ⟨115860266183714637971663549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77240177455809758647775699 115860266183714637971663549)
      ·
        refine ⟨43447599818892989239373831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115860266183714637971663549 43447599818892989239373831)
        ·
          refine ⟨65171399728339483859060747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43447599818892989239373831 65171399728339483859060747)
          ·
            refine ⟨97757099592509225788591121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65171399728339483859060747 97757099592509225788591121)
            ·
              refine ⟨73317824694381919341443341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97757099592509225788591121 73317824694381919341443341)
              ·
                refine ⟨27494184260393219753041253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73317824694381919341443341 27494184260393219753041253)
                ·
                  refine ⟨5155159548823728703695235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27494184260393219753041253 5155159548823728703695235)
                  ·
                    refine ⟨7732739323235593055542853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5155159548823728703695235 7732739323235593055542853)
                    ·
                      refine ⟨1449888623106673697914285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7732739323235593055542853 1449888623106673697914285)
                      ·
                        rfl

theorem cell23_2823648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_2823648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823648 prefixEnd_2823648 := by exact prefixLift 2823648
  have htrace : WordTrace (prefixWord ++ tailWord_2823648) baseStart_2823648 baseEnd_2823648 := by
    simpa [prefixWord, tailWord_2823648, baseEnd_2823648] using wordTrace_append hprefix tailTrace_2823648
  have hstable : (prefixWord ++ tailWord_2823648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823648).length < 2 ^ (prefixWord ++ tailWord_2823648).sum := by decide
  have hdescent : baseEnd_2823648 < baseStart_2823648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823665 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 1, 6, 2]
def baseStart_2823665 : Nat := 118140960795 + 2823665 * 2 ^ 59
def prefixEnd_2823665 : Nat := 4983230072969 + 3 ^ 40 * 2823665 * 2
def baseEnd_2823665 : Nat := 1449897352277800131401707

theorem tailTrace_2823665 : CollatzResearch.WordTrace tailWord_2823665 prefixEnd_2823665 1449897352277800131401707 := by
  unfold tailWord_2823665
  simp only [CollatzResearch.WordTrace]
  refine ⟨102987523315351423433736449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68658348876900948955824299 102987523315351423433736449)
  ·
    refine ⟨77240642486513567575302337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102987523315351423433736449 77240642486513567575302337)
    ·
      refine ⟨57930481864885175681476753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77240642486513567575302337 57930481864885175681476753)
      ·
        refine ⟨43447861398663881761107565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57930481864885175681476753 43447861398663881761107565)
        ·
          refine ⟨16292948024498955660415337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43447861398663881761107565 16292948024498955660415337)
          ·
            refine ⟨12219711018374216745311503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16292948024498955660415337 12219711018374216745311503)
            ·
              refine ⟨18329566527561325117967255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12219711018374216745311503 18329566527561325117967255)
              ·
                refine ⟨27494349791341987676950883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18329566527561325117967255 27494349791341987676950883)
                ·
                  refine ⟨41241524687012981515426325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27494349791341987676950883 41241524687012981515426325)
                  ·
                    refine ⟨1933196469703733508535609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41241524687012981515426325 1933196469703733508535609)
                    ·
                      refine ⟨1449897352277800131401707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1933196469703733508535609 1449897352277800131401707)
                      ·
                        rfl

theorem cell23_2823665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 6, 2].length) (baseStart_2823665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823665 prefixEnd_2823665 := by exact prefixLift 2823665
  have htrace : WordTrace (prefixWord ++ tailWord_2823665) baseStart_2823665 baseEnd_2823665 := by
    simpa [prefixWord, tailWord_2823665, baseEnd_2823665] using wordTrace_append hprefix tailTrace_2823665
  have hstable : (prefixWord ++ tailWord_2823665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823665).length < 2 ^ (prefixWord ++ tailWord_2823665).sum := by decide
  have hdescent : baseEnd_2823665 < baseStart_2823665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823682 : List Nat := [3, 4, 1, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_2823682 : Nat := 118140960795 + 2823682 * 2 ^ 59
def prefixEnd_2823682 : Nat := 4983230072969 + 3 ^ 40 * 2823682 * 2
def baseEnd_2823682 : Nat := 1449906081448926564889129

theorem tailTrace_2823682 : CollatzResearch.WordTrace tailWord_2823682 prefixEnd_2823682 1449906081448926564889129 := by
  unfold tailWord_2823682
  simp only [CollatzResearch.WordTrace]
  refine ⟨25747035839072458834276325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68658762237526556891403533 25747035839072458834276325)
  ·
    refine ⟨4827569219826086031426811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25747035839072458834276325 4827569219826086031426811)
    ·
      refine ⟨7241353829739129047140217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4827569219826086031426811 7241353829739129047140217)
      ·
        refine ⟨5431015372304346785355163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7241353829739129047140217 5431015372304346785355163)
        ·
          refine ⟨8146523058456520178032745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5431015372304346785355163 8146523058456520178032745)
          ·
            refine ⟨6109892293842390133524559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8146523058456520178032745 6109892293842390133524559)
            ·
              refine ⟨9164838440763585200286839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6109892293842390133524559 9164838440763585200286839)
              ·
                refine ⟨13747257661145377800430259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9164838440763585200286839 13747257661145377800430259)
                ·
                  refine ⟨20620886491718066700645389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13747257661145377800430259 20620886491718066700645389)
                  ·
                    refine ⟨7732832434394275012742021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20620886491718066700645389 7732832434394275012742021)
                    ·
                      refine ⟨1449906081448926564889129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7732832434394275012742021 1449906081448926564889129)
                      ·
                        rfl

theorem cell23_2823682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_2823682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823682 prefixEnd_2823682 := by exact prefixLift 2823682
  have htrace : WordTrace (prefixWord ++ tailWord_2823682) baseStart_2823682 baseEnd_2823682 := by
    simpa [prefixWord, tailWord_2823682, baseEnd_2823682] using wordTrace_append hprefix tailTrace_2823682
  have hstable : (prefixWord ++ tailWord_2823682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823682).length < 2 ^ (prefixWord ++ tailWord_2823682).sum := by decide
  have hdescent : baseEnd_2823682 < baseStart_2823682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823708 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 1, 1, 8]
def baseStart_2823708 : Nat := 118140960795 + 2823708 * 2 ^ 59
def prefixEnd_2823708 : Nat := 4983230072969 + 3 ^ 40 * 2823708 * 2
def baseEnd_2823708 : Nat := 1449919431945943463164009

theorem tailTrace_2823708 : CollatzResearch.WordTrace tailWord_2823708 prefixEnd_2823708 1449919431945943463164009 := by
  unfold tailWord_2823708
  simp only [CollatzResearch.WordTrace]
  refine ⟨51494545827097820888775889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68659394436130427851701185 51494545827097820888775889)
  ·
    refine ⟨38620909370323365666581917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51494545827097820888775889 38620909370323365666581917)
    ·
      refine ⟨14482841013871262124968219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38620909370323365666581917 14482841013871262124968219)
      ·
        refine ⟨21724261520806893187452329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14482841013871262124968219 21724261520806893187452329)
        ·
          refine ⟨16293196140605169890589247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21724261520806893187452329 16293196140605169890589247)
          ·
            refine ⟨24439794210907754835883871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16293196140605169890589247 24439794210907754835883871)
            ·
              refine ⟨36659691316361632253825807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24439794210907754835883871 36659691316361632253825807)
              ·
                refine ⟨54989536974542448380738711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36659691316361632253825807 54989536974542448380738711)
                ·
                  refine ⟨82484305461813672571108067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54989536974542448380738711 82484305461813672571108067)
                  ·
                    refine ⟨123726458192720508856662101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82484305461813672571108067 123726458192720508856662101)
                    ·
                      refine ⟨1449919431945943463164009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 123726458192720508856662101 1449919431945943463164009)
                      ·
                        rfl

theorem cell23_2823708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_2823708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823708 prefixEnd_2823708 := by exact prefixLift 2823708
  have htrace : WordTrace (prefixWord ++ tailWord_2823708) baseStart_2823708 baseEnd_2823708 := by
    simpa [prefixWord, tailWord_2823708, baseEnd_2823708] using wordTrace_append hprefix tailTrace_2823708
  have hstable : (prefixWord ++ tailWord_2823708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823708).length < 2 ^ (prefixWord ++ tailWord_2823708).sum := by decide
  have hdescent : baseEnd_2823708 < baseStart_2823708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823722 : List Nat := [3, 1, 4, 1, 1, 1, 5, 1, 6]
def baseStart_2823722 : Nat := 118140960795 + 2823722 * 2 ^ 59
def prefixEnd_2823722 : Nat := 4983230072969 + 3 ^ 40 * 2823722 * 2
def baseEnd_2823722 : Nat := 161102957852789600932105

theorem tailTrace_2823722 : CollatzResearch.WordTrace tailWord_2823722 prefixEnd_2823722 161102957852789600932105 := by
  unfold tailWord_2823722
  simp only [CollatzResearch.WordTrace]
  refine ⟨25747400569036230542140355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68659734850763281445707613 25747400569036230542140355)
  ·
    refine ⟨38621100853554345813210533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25747400569036230542140355 38621100853554345813210533)
    ·
      refine ⟨7241456410041439839976975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38621100853554345813210533 7241456410041439839976975)
      ·
        refine ⟨10862184615062159759965463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7241456410041439839976975 10862184615062159759965463)
        ·
          refine ⟨16293276922593239639948195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10862184615062159759965463 16293276922593239639948195)
          ·
            refine ⟨24439915383889859459922293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16293276922593239639948195 24439915383889859459922293)
            ·
              refine ⟨2291242067239674324367715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24439915383889859459922293 2291242067239674324367715)
              ·
                refine ⟨3436863100859511486551573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2291242067239674324367715 3436863100859511486551573)
                ·
                  refine ⟨161102957852789600932105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3436863100859511486551573 161102957852789600932105)
                  ·
                    rfl

theorem cell23_2823722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 6].length) (baseStart_2823722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823722 prefixEnd_2823722 := by exact prefixLift 2823722
  have htrace : WordTrace (prefixWord ++ tailWord_2823722) baseStart_2823722 baseEnd_2823722 := by
    simpa [prefixWord, tailWord_2823722, baseEnd_2823722] using wordTrace_append hprefix tailTrace_2823722
  have hstable : (prefixWord ++ tailWord_2823722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823722).length < 2 ^ (prefixWord ++ tailWord_2823722).sum := by decide
  have hdescent : baseEnd_2823722 < baseStart_2823722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823735 : List Nat := [1, 1, 3, 1, 2, 4, 1, 4, 1, 5]
def baseStart_2823735 : Nat := 118140960795 + 2823735 * 2 ^ 59
def prefixEnd_2823735 : Nat := 4983230072969 + 3 ^ 40 * 2823735 * 2
def baseEnd_2823735 : Nat := 483311098641204952508795

theorem tailTrace_2823735 : CollatzResearch.WordTrace tailWord_2823735 prefixEnd_2823735 483311098641204952508795 := by
  unfold tailWord_2823735
  simp only [CollatzResearch.WordTrace]
  refine ⟨102990076425097825388784659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68660050950065216925856439 102990076425097825388784659)
  ·
    refine ⟨154485114637646738083176989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102990076425097825388784659 154485114637646738083176989)
    ·
      refine ⟨57931917989117526781191371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154485114637646738083176989 57931917989117526781191371)
      ·
        refine ⟨86897876983676290171787057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57931917989117526781191371 86897876983676290171787057)
        ·
          refine ⟨65173407737757217628840293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86897876983676290171787057 65173407737757217628840293)
          ·
            refine ⟨12220013950829478305407555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65173407737757217628840293 12220013950829478305407555)
            ·
              refine ⟨18330020926244217458111333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12220013950829478305407555 18330020926244217458111333)
              ·
                refine ⟨3436878923670790773395875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18330020926244217458111333 3436878923670790773395875)
                ·
                  refine ⟨5155318385506186160093813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3436878923670790773395875 5155318385506186160093813)
                  ·
                    refine ⟨483311098641204952508795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5155318385506186160093813 483311098641204952508795)
                    ·
                      rfl

theorem cell23_2823735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 5].length) (baseStart_2823735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823735 prefixEnd_2823735 := by exact prefixLift 2823735
  have htrace : WordTrace (prefixWord ++ tailWord_2823735) baseStart_2823735 baseEnd_2823735 := by
    simpa [prefixWord, tailWord_2823735, baseEnd_2823735] using wordTrace_append hprefix tailTrace_2823735
  have hstable : (prefixWord ++ tailWord_2823735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823735).length < 2 ^ (prefixWord ++ tailWord_2823735).sum := by decide
  have hdescent : baseEnd_2823735 < baseStart_2823735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823773 : List Nat := [1, 4, 4, 2, 2, 1, 2, 1, 6]
def baseStart_2823773 : Nat := 118140960795 + 2823773 * 2 ^ 59
def prefixEnd_2823773 : Nat := 4983230072969 + 3 ^ 40 * 2823773 * 2
def baseEnd_2823773 : Nat := 161105867576498412094579

theorem tailTrace_2823773 : CollatzResearch.WordTrace tailWord_2823773 prefixEnd_2823773 161105867576498412094579 := by
  unfold tailWord_2823773
  simp only [CollatzResearch.WordTrace]
  refine ⟨102991462398960157878667973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68660974932640105252445315 102991462398960157878667973)
  ·
    refine ⟨19310899199805029602250245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102991462398960157878667973 19310899199805029602250245)
    ·
      refine ⟨3620793599963443050421921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19310899199805029602250245 3620793599963443050421921)
      ·
        refine ⟨2715595199972582287816441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3620793599963443050421921 2715595199972582287816441)
        ·
          refine ⟨2036696399979436715862331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2715595199972582287816441 2036696399979436715862331)
          ·
            refine ⟨3055044599969155073793497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2036696399979436715862331 3055044599969155073793497)
            ·
              refine ⟨2291283449976866305345123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3055044599969155073793497 2291283449976866305345123)
              ·
                refine ⟨3436925174965299458017685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2291283449976866305345123 3436925174965299458017685)
                ·
                  refine ⟨161105867576498412094579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3436925174965299458017685 161105867576498412094579)
                  ·
                    rfl

theorem cell23_2823773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 6].length) (baseStart_2823773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823773 prefixEnd_2823773 := by exact prefixLift 2823773
  have htrace : WordTrace (prefixWord ++ tailWord_2823773) baseStart_2823773 baseEnd_2823773 := by
    simpa [prefixWord, tailWord_2823773, baseEnd_2823773] using wordTrace_append hprefix tailTrace_2823773
  have hstable : (prefixWord ++ tailWord_2823773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823773).length < 2 ^ (prefixWord ++ tailWord_2823773).sum := by decide
  have hdescent : baseEnd_2823773 < baseStart_2823773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823792 : List Nat := [2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 3]
def baseStart_2823792 : Nat := 118140960795 + 2823792 * 2 ^ 59
def prefixEnd_2823792 : Nat := 4983230072969 + 3 ^ 40 * 2823792 * 2
def baseEnd_2823792 : Nat := 1449962564320921134513623

theorem tailTrace_2823792 : CollatzResearch.WordTrace tailWord_2823792 prefixEnd_2823792 1449962564320921134513623 := by
  unfold tailWord_2823792
  simp only [CollatzResearch.WordTrace]
  refine ⟨51496077692945662061804815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68661436923927549415739753 51496077692945662061804815)
  ·
    refine ⟨77244116539418493092707223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51496077692945662061804815 77244116539418493092707223)
    ·
      refine ⟨115866174809127739639060835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77244116539418493092707223 115866174809127739639060835)
      ·
        refine ⟨173799262213691609458591253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115866174809127739639060835 173799262213691609458591253)
        ·
          refine ⟨8146840416266794193371465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 173799262213691609458591253 8146840416266794193371465)
          ·
            refine ⟨6110130312200095645028599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8146840416266794193371465 6110130312200095645028599)
            ·
              refine ⟨9165195468300143467542899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6110130312200095645028599 9165195468300143467542899)
              ·
                refine ⟨13747793202450215201314349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9165195468300143467542899 13747793202450215201314349)
                ·
                  refine ⟨5155422450918830700492881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13747793202450215201314349 5155422450918830700492881)
                  ·
                    refine ⟨3866566838189123025369661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5155422450918830700492881 3866566838189123025369661)
                    ·
                      refine ⟨1449962564320921134513623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3866566838189123025369661 1449962564320921134513623)
                      ·
                        rfl

theorem cell23_2823792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 3].length) (baseStart_2823792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823792 prefixEnd_2823792 := by exact prefixLift 2823792
  have htrace : WordTrace (prefixWord ++ tailWord_2823792) baseStart_2823792 baseEnd_2823792 := by
    simpa [prefixWord, tailWord_2823792, baseEnd_2823792] using wordTrace_append hprefix tailTrace_2823792
  have hstable : (prefixWord ++ tailWord_2823792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823792).length < 2 ^ (prefixWord ++ tailWord_2823792).sum := by decide
  have hdescent : baseEnd_2823792 < baseStart_2823792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823816 : List Nat := [2, 1, 3, 5, 1, 1, 2, 2, 2, 4]
def baseStart_2823816 : Nat := 118140960795 + 2823816 * 2 ^ 59
def prefixEnd_2823816 : Nat := 4983230072969 + 3 ^ 40 * 2823816 * 2
def baseEnd_2823816 : Nat := 483324962618876346871171

theorem tailTrace_2823816 : CollatzResearch.WordTrace tailWord_2823816 prefixEnd_2823816 483324962618876346871171 := by
  unfold tailWord_2823816
  simp only [CollatzResearch.WordTrace]
  refine ⟨51496515368902188111241651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68662020491869584148322201 51496515368902188111241651)
  ·
    refine ⟨77244773053353282166862477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51496515368902188111241651 77244773053353282166862477)
    ·
      refine ⟨28966789895007480812573429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77244773053353282166862477 28966789895007480812573429)
      ·
        refine ⟨2715636552656951326178759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28966789895007480812573429 2715636552656951326178759)
        ·
          refine ⟨4073454828985426989268139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2715636552656951326178759 4073454828985426989268139)
          ·
            refine ⟨6110182243478140483902209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4073454828985426989268139 6110182243478140483902209)
            ·
              refine ⟨4582636682608605362926657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6110182243478140483902209 4582636682608605362926657)
              ·
                refine ⟨3436977511956454022194993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4582636682608605362926657 3436977511956454022194993)
                ·
                  refine ⟨2577733133967340516646245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3436977511956454022194993 2577733133967340516646245)
                  ·
                    refine ⟨483324962618876346871171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2577733133967340516646245 483324962618876346871171)
                    ·
                      rfl

theorem cell23_2823816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_2823816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823816 prefixEnd_2823816 := by exact prefixLift 2823816
  have htrace : WordTrace (prefixWord ++ tailWord_2823816) baseStart_2823816 baseEnd_2823816 := by
    simpa [prefixWord, tailWord_2823816, baseEnd_2823816] using wordTrace_append hprefix tailTrace_2823816
  have hstable : (prefixWord ++ tailWord_2823816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823816).length < 2 ^ (prefixWord ++ tailWord_2823816).sum := by decide
  have hdescent : baseEnd_2823816 < baseStart_2823816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823865 : List Nat := [1, 2, 1, 4, 1, 1, 2, 3, 2, 1, 5]
def baseStart_2823865 : Nat := 118140960795 + 2823865 * 2 ^ 59
def prefixEnd_2823865 : Nat := 4983230072969 + 3 ^ 40 * 2823865 * 2
def baseEnd_2823865 : Nat := 1450000048408699348900787

theorem tailTrace_2823865 : CollatzResearch.WordTrace tailWord_2823865 prefixEnd_2823865 1450000048408699348900787 := by
  unfold tailWord_2823865
  simp only [CollatzResearch.WordTrace]
  refine ⟨102994817914626857591017049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68663211943084571727344699 102994817914626857591017049)
  ·
    refine ⟨77246113435970143193262787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102994817914626857591017049 77246113435970143193262787)
    ·
      refine ⟨115869170153955214789894181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77246113435970143193262787 115869170153955214789894181)
      ·
        refine ⟨21725469403866602773105159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115869170153955214789894181 21725469403866602773105159)
        ·
          refine ⟨32588204105799904159657739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21725469403866602773105159 32588204105799904159657739)
          ·
            refine ⟨48882306158699856239486609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32588204105799904159657739 48882306158699856239486609)
            ·
              refine ⟨36661729619024892179614957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48882306158699856239486609 36661729619024892179614957)
              ·
                refine ⟨13748148607134334567355609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36661729619024892179614957 13748148607134334567355609)
                ·
                  refine ⟨10311111455350750925516707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13748148607134334567355609 10311111455350750925516707)
                  ·
                    refine ⟨15466667183026126388275061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10311111455350750925516707 15466667183026126388275061)
                    ·
                      refine ⟨1450000048408699348900787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15466667183026126388275061 1450000048408699348900787)
                      ·
                        rfl

theorem cell23_2823865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_2823865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823865 prefixEnd_2823865 := by exact prefixLift 2823865
  have htrace : WordTrace (prefixWord ++ tailWord_2823865) baseStart_2823865 baseEnd_2823865 := by
    simpa [prefixWord, tailWord_2823865, baseEnd_2823865] using wordTrace_append hprefix tailTrace_2823865
  have hstable : (prefixWord ++ tailWord_2823865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823865).length < 2 ^ (prefixWord ++ tailWord_2823865).sum := by decide
  have hdescent : baseEnd_2823865 < baseStart_2823865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823866 : List Nat := [3, 1, 1, 1, 2, 4, 4, 1, 1, 3, 2]
def baseStart_2823866 : Nat := 118140960795 + 2823866 * 2 ^ 59
def prefixEnd_2823866 : Nat := 4983230072969 + 3 ^ 40 * 2823866 * 2
def baseEnd_2823866 : Nat := 1450000561889353844988283

theorem tailTrace_2823866 : CollatzResearch.WordTrace tailWord_2823866 prefixEnd_2823866 1450000561889353844988283 := by
  unfold tailWord_2823866
  simp only [CollatzResearch.WordTrace]
  refine ⟨25748713596905808690450863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68663236258415489841202301 25748713596905808690450863)
  ·
    refine ⟨38623070395358713035676295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25748713596905808690450863 38623070395358713035676295)
    ·
      refine ⟨57934605593038069553514443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38623070395358713035676295 57934605593038069553514443)
      ·
        refine ⟨86901908389557104330271665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57934605593038069553514443 86901908389557104330271665)
        ·
          refine ⟨65176431292167828247703749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86901908389557104330271665 65176431292167828247703749)
          ·
            refine ⟨12220580867281467796444453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65176431292167828247703749 12220580867281467796444453)
            ·
              refine ⟨2291358912615275211833335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12220580867281467796444453 2291358912615275211833335)
              ·
                refine ⟨3437038368922912817750003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2291358912615275211833335 3437038368922912817750003)
                ·
                  refine ⟨5155557553384369226625005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3437038368922912817750003 5155557553384369226625005)
                  ·
                    refine ⟨1933334082519138459984377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5155557553384369226625005 1933334082519138459984377)
                    ·
                      refine ⟨1450000561889353844988283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1933334082519138459984377 1450000561889353844988283)
                      ·
                        rfl

theorem cell23_2823866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 1, 3, 2].length) (baseStart_2823866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823866 prefixEnd_2823866 := by exact prefixLift 2823866
  have htrace : WordTrace (prefixWord ++ tailWord_2823866) baseStart_2823866 baseEnd_2823866 := by
    simpa [prefixWord, tailWord_2823866, baseEnd_2823866] using wordTrace_append hprefix tailTrace_2823866
  have hstable : (prefixWord ++ tailWord_2823866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823866).length < 2 ^ (prefixWord ++ tailWord_2823866).sum := by decide
  have hdescent : baseEnd_2823866 < baseStart_2823866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823879 : List Nat := [1, 1, 4, 1, 1, 1, 5, 1, 4, 2, 2]
def baseStart_2823879 : Nat := 118140960795 + 2823879 * 2 ^ 59
def prefixEnd_2823879 : Nat := 4983230072969 + 3 ^ 40 * 2823879 * 2
def baseEnd_2823879 : Nat := 1450007237137862294125723

theorem tailTrace_2823879 : CollatzResearch.WordTrace tailWord_2823879 prefixEnd_2823879 1450007237137862294125723 := by
  unfold tailWord_2823879
  simp only [CollatzResearch.WordTrace]
  refine ⟨102995328536576137982026691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68663552357717425321351127 102995328536576137982026691)
  ·
    refine ⟨154492992804864206973040037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102995328536576137982026691 154492992804864206973040037)
    ·
      refine ⟨28967436150912038807445007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154492992804864206973040037 28967436150912038807445007)
      ·
        refine ⟨43451154226368058211167511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28967436150912038807445007 43451154226368058211167511)
        ·
          refine ⟨65176731339552087316751267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43451154226368058211167511 65176731339552087316751267)
          ·
            refine ⟨97765097009328130975126901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65176731339552087316751267 97765097009328130975126901)
            ·
              refine ⟨9165477844624512278918147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97765097009328130975126901 9165477844624512278918147)
              ·
                refine ⟨13748216766936768418377221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9165477844624512278918147 13748216766936768418377221)
                ·
                  refine ⟨2577790643800644078445729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13748216766936768418377221 2577790643800644078445729)
                  ·
                    refine ⟨1933342982850483058834297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2577790643800644078445729 1933342982850483058834297)
                    ·
                      refine ⟨1450007237137862294125723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1933342982850483058834297 1450007237137862294125723)
                      ·
                        rfl

theorem cell23_2823879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 4, 2, 2].length) (baseStart_2823879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823879 prefixEnd_2823879 := by exact prefixLift 2823879
  have htrace : WordTrace (prefixWord ++ tailWord_2823879) baseStart_2823879 baseEnd_2823879 := by
    simpa [prefixWord, tailWord_2823879, baseEnd_2823879] using wordTrace_append hprefix tailTrace_2823879
  have hstable : (prefixWord ++ tailWord_2823879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823879).length < 2 ^ (prefixWord ++ tailWord_2823879).sum := by decide
  have hdescent : baseEnd_2823879 < baseStart_2823879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823915 : List Nat := [1, 1, 1, 1, 2, 4, 4, 1, 1, 7]
def baseStart_2823915 : Nat := 118140960795 + 2823915 * 2 ^ 59
def prefixEnd_2823915 : Nat := 4983230072969 + 3 ^ 40 * 2823915 * 2
def baseEnd_2823915 : Nat := 483341907480474717758519

theorem tailTrace_2823915 : CollatzResearch.WordTrace tailWord_2823915 prefixEnd_2823915 483341907480474717758519 := by
  unfold tailWord_2823915
  simp only [CollatzResearch.WordTrace]
  refine ⟨102996641564445716130337199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68664427709630477420224799 102996641564445716130337199)
  ·
    refine ⟨154494962346668574195505799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102996641564445716130337199 154494962346668574195505799)
    ·
      refine ⟨231742443520002861293258699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154494962346668574195505799 231742443520002861293258699)
      ·
        refine ⟨347613665280004291939888049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231742443520002861293258699 347613665280004291939888049)
        ·
          refine ⟨260710248960003218954916037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347613665280004291939888049 260710248960003218954916037)
          ·
            refine ⟨48883171680000603554046757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 260710248960003218954916037 48883171680000603554046757)
            ·
              refine ⟨9165594690000113166383767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48883171680000603554046757 9165594690000113166383767)
              ·
                refine ⟨13748392035000169749575651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9165594690000113166383767 13748392035000169749575651)
                ·
                  refine ⟨20622588052500254624363477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13748392035000169749575651 20622588052500254624363477)
                  ·
                    refine ⟨483341907480474717758519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20622588052500254624363477 483341907480474717758519)
                    ·
                      rfl

theorem cell23_2823915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 7].length) (baseStart_2823915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823915 prefixEnd_2823915 := by exact prefixLift 2823915
  have htrace : WordTrace (prefixWord ++ tailWord_2823915) baseStart_2823915 baseEnd_2823915 := by
    simpa [prefixWord, tailWord_2823915, baseEnd_2823915] using wordTrace_append hprefix tailTrace_2823915
  have hstable : (prefixWord ++ tailWord_2823915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823915).length < 2 ^ (prefixWord ++ tailWord_2823915).sum := by decide
  have hdescent : baseEnd_2823915 < baseStart_2823915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823932 : List Nat := [2, 2, 2, 1, 3, 1, 3, 2, 2, 5]
def baseStart_2823932 : Nat := 118140960795 + 2823932 * 2 ^ 59
def prefixEnd_2823932 : Nat := 4983230072969 + 3 ^ 40 * 2823932 * 2
def baseEnd_2823932 : Nat := 483344817204183528920993

theorem tailTrace_2823932 : CollatzResearch.WordTrace tailWord_2823932 prefixEnd_2823932 483344817204183528920993 := by
  unfold tailWord_2823932
  simp only [CollatzResearch.WordTrace]
  refine ⟨51498630802692064016853025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68664841070256085355804033 51498630802692064016853025)
  ·
    refine ⟨38623973102019048012639769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51498630802692064016853025 38623973102019048012639769)
    ·
      refine ⟨28967979826514286009479827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38623973102019048012639769 28967979826514286009479827)
      ·
        refine ⟨43451969739771429014219741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28967979826514286009479827 43451969739771429014219741)
        ·
          refine ⟨16294488652414285880332403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43451969739771429014219741 16294488652414285880332403)
          ·
            refine ⟨24441732978621428820498605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16294488652414285880332403 24441732978621428820498605)
            ·
              refine ⟨9165649866983035807686977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24441732978621428820498605 9165649866983035807686977)
              ·
                refine ⟨6874237400237276855765233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9165649866983035807686977 6874237400237276855765233)
                ·
                  refine ⟨5155678050177957641823925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6874237400237276855765233 5155678050177957641823925)
                  ·
                    refine ⟨483344817204183528920993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5155678050177957641823925 483344817204183528920993)
                    ·
                      rfl

theorem cell23_2823932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_2823932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823932 prefixEnd_2823932 := by exact prefixLift 2823932
  have htrace : WordTrace (prefixWord ++ tailWord_2823932) baseStart_2823932 baseEnd_2823932 := by
    simpa [prefixWord, tailWord_2823932, baseEnd_2823932] using wordTrace_append hprefix tailTrace_2823932
  have hstable : (prefixWord ++ tailWord_2823932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823932).length < 2 ^ (prefixWord ++ tailWord_2823932).sum := by decide
  have hdescent : baseEnd_2823932 < baseStart_2823932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823969 : List Nat := [1, 2, 3, 2, 1, 4, 2, 1, 2, 1, 4]
def baseStart_2823969 : Nat := 118140960795 + 2823969 * 2 ^ 59
def prefixEnd_2823969 : Nat := 4983230072969 + 3 ^ 40 * 2823969 * 2
def baseEnd_2823969 : Nat := 1450053450396766942000309

theorem tailTrace_2823969 : CollatzResearch.WordTrace tailWord_2823969 prefixEnd_2823969 1450053450396766942000309 := by
  unfold tailWord_2823969
  simp only [CollatzResearch.WordTrace]
  refine ⟨102998611106250083352802961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68665740737500055568535307 102998611106250083352802961)
  ·
    refine ⟨77248958329687562514602221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102998611106250083352802961 77248958329687562514602221)
    ·
      refine ⟨28968359373632835942975833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77248958329687562514602221 28968359373632835942975833)
      ·
        refine ⟨21726269530224626957231875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28968359373632835942975833 21726269530224626957231875)
        ·
          refine ⟨32589404295336940435847813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21726269530224626957231875 32589404295336940435847813)
          ·
            refine ⟨6110513305375676331721465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32589404295336940435847813 6110513305375676331721465)
            ·
              refine ⟨4582884979031757248791099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6110513305375676331721465 4582884979031757248791099)
              ·
                refine ⟨6874327468547635873186649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4582884979031757248791099 6874327468547635873186649)
                ·
                  refine ⟨5155745601410726904889987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6874327468547635873186649 5155745601410726904889987)
                  ·
                    refine ⟨7733618402116090357334981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5155745601410726904889987 7733618402116090357334981)
                    ·
                      refine ⟨1450053450396766942000309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7733618402116090357334981 1450053450396766942000309)
                      ·
                        rfl

theorem cell23_2823969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_2823969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823969 prefixEnd_2823969 := by exact prefixLift 2823969
  have htrace : WordTrace (prefixWord ++ tailWord_2823969) baseStart_2823969 baseEnd_2823969 := by
    simpa [prefixWord, tailWord_2823969, baseEnd_2823969] using wordTrace_append hprefix tailTrace_2823969
  have hstable : (prefixWord ++ tailWord_2823969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823969).length < 2 ^ (prefixWord ++ tailWord_2823969).sum := by decide
  have hdescent : baseEnd_2823969 < baseStart_2823969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2823992 : List Nat := [2, 1, 2, 1, 3, 3, 1, 4, 6]
def baseStart_2823992 : Nat := 118140960795 + 2823992 * 2 ^ 59
def prefixEnd_2823992 : Nat := 4983230072969 + 3 ^ 40 * 2823992 * 2
def baseEnd_2823992 : Nat := 161118362272424483556967

theorem tailTrace_2823992 : CollatzResearch.WordTrace tailWord_2823992 prefixEnd_2823992 161118362272424483556967 := by
  unfold tailWord_2823992
  simp only [CollatzResearch.WordTrace]
  refine ⟨51499724992583379140445115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68666299990111172187260153 51499724992583379140445115)
  ·
    refine ⟨77249587488875068710667673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51499724992583379140445115 77249587488875068710667673)
    ·
      refine ⟨57937190616656301533000755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77249587488875068710667673 57937190616656301533000755)
      ·
        refine ⟨86905785924984452299501133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57937190616656301533000755 86905785924984452299501133)
        ·
          refine ⟨32589669721869169612312925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86905785924984452299501133 32589669721869169612312925)
          ·
            refine ⟨12221126145700938604617347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32589669721869169612312925 12221126145700938604617347)
            ·
              refine ⟨18331689218551407906926021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12221126145700938604617347 18331689218551407906926021)
              ·
                refine ⟨3437191728478388982548629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18331689218551407906926021 3437191728478388982548629)
                ·
                  refine ⟨161118362272424483556967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3437191728478388982548629 161118362272424483556967)
                  ·
                    rfl

theorem cell23_2823992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 6].length) (baseStart_2823992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2823992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2823992 prefixEnd_2823992 := by exact prefixLift 2823992
  have htrace : WordTrace (prefixWord ++ tailWord_2823992) baseStart_2823992 baseEnd_2823992 := by
    simpa [prefixWord, tailWord_2823992, baseEnd_2823992] using wordTrace_append hprefix tailTrace_2823992
  have hstable : (prefixWord ++ tailWord_2823992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2823992).length < 2 ^ (prefixWord ++ tailWord_2823992).sum := by decide
  have hdescent : baseEnd_2823992 < baseStart_2823992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2823992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824023 : List Nat := [1, 1, 3, 2, 6, 1, 1, 1, 2, 2, 3]
def baseStart_2824023 : Nat := 118140960795 + 2824023 * 2 ^ 59
def prefixEnd_2824023 : Nat := 4983230072969 + 3 ^ 40 * 2824023 * 2
def baseEnd_2824023 : Nat := 1450081178352109730725061

theorem tailTrace_2824023 : CollatzResearch.WordTrace tailWord_2824023 prefixEnd_2824023 1450081178352109730725061 := by
  unfold tailWord_2824023
  simp only [CollatzResearch.WordTrace]
  refine ⟨103000580648054450575268723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68667053765369633716845815 103000580648054450575268723)
  ·
    refine ⟨154500870972081675862903085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103000580648054450575268723 154500870972081675862903085)
    ·
      refine ⟨57937826614530628448588657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154500870972081675862903085 57937826614530628448588657)
      ·
        refine ⟨43453369960897971336441493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57937826614530628448588657 43453369960897971336441493)
        ·
          refine ⟨2036876716917092406395695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 43453369960897971336441493 2036876716917092406395695)
          ·
            refine ⟨3055315075375638609593543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2036876716917092406395695 3055315075375638609593543)
            ·
              refine ⟨4582972613063457914390315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3055315075375638609593543 4582972613063457914390315)
              ·
                refine ⟨6874458919595186871585473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4582972613063457914390315 6874458919595186871585473)
                ·
                  refine ⟨5155844189696390153689105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6874458919595186871585473 5155844189696390153689105)
                  ·
                    refine ⟨3866883142272292615266829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5155844189696390153689105 3866883142272292615266829)
                    ·
                      refine ⟨1450081178352109730725061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3866883142272292615266829 1450081178352109730725061)
                      ·
                        rfl

theorem cell23_2824023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 2, 2, 3].length) (baseStart_2824023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824023 prefixEnd_2824023 := by exact prefixLift 2824023
  have htrace : WordTrace (prefixWord ++ tailWord_2824023) baseStart_2824023 baseEnd_2824023 := by
    simpa [prefixWord, tailWord_2824023, baseEnd_2824023] using wordTrace_append hprefix tailTrace_2824023
  have hstable : (prefixWord ++ tailWord_2824023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824023).length < 2 ^ (prefixWord ++ tailWord_2824023).sum := by decide
  have hdescent : baseEnd_2824023 < baseStart_2824023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824039 : List Nat := [1, 1, 5, 1, 2, 1, 3, 3, 1, 5]
def baseStart_2824039 : Nat := 118140960795 + 2824039 * 2 ^ 59
def prefixEnd_2824039 : Nat := 4983230072969 + 3 ^ 40 * 2824039 * 2
def baseEnd_2824039 : Nat := 483363131347527222708329

theorem tailTrace_2824039 : CollatzResearch.WordTrace tailWord_2824039 prefixEnd_2824039 483363131347527222708329 := by
  unfold tailWord_2824039
  simp only [CollatzResearch.WordTrace]
  refine ⟨103001164215996485307851171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68667442810664323538567447 103001164215996485307851171)
  ·
    refine ⟨154501746323994727961776757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103001164215996485307851171 154501746323994727961776757)
    ·
      refine ⟨14484538717874505746416571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 154501746323994727961776757 14484538717874505746416571)
      ·
        refine ⟨21726808076811758619624857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14484538717874505746416571 21726808076811758619624857)
        ·
          refine ⟨16295106057608818964718643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21726808076811758619624857 16295106057608818964718643)
          ·
            refine ⟨24442659086413228447077965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16295106057608818964718643 24442659086413228447077965)
            ·
              refine ⟨9165997157404960667654237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24442659086413228447077965 9165997157404960667654237)
              ·
                refine ⟨3437248934026860250370339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9165997157404960667654237 3437248934026860250370339)
                ·
                  refine ⟨5155873401040290375555509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3437248934026860250370339 5155873401040290375555509)
                  ·
                    refine ⟨483363131347527222708329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5155873401040290375555509 483363131347527222708329)
                    ·
                      rfl

theorem cell23_2824039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_2824039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824039 prefixEnd_2824039 := by exact prefixLift 2824039
  have htrace : WordTrace (prefixWord ++ tailWord_2824039) baseStart_2824039 baseEnd_2824039 := by
    simpa [prefixWord, tailWord_2824039, baseEnd_2824039] using wordTrace_append hprefix tailTrace_2824039
  have hstable : (prefixWord ++ tailWord_2824039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824039).length < 2 ^ (prefixWord ++ tailWord_2824039).sum := by decide
  have hdescent : baseEnd_2824039 < baseStart_2824039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824053 : List Nat := [1, 3, 4, 1, 1, 1, 1, 6, 1, 1, 3]
def baseStart_2824053 : Nat := 118140960795 + 2824053 * 2 ^ 59
def prefixEnd_2824053 : Nat := 4983230072969 + 3 ^ 40 * 2824053 * 2
def baseEnd_2824053 : Nat := 1450096582771744613349923

theorem tailTrace_2824053 : CollatzResearch.WordTrace tailWord_2824053 prefixEnd_2824053 1450096582771744613349923 := by
  unfold tailWord_2824053
  simp only [CollatzResearch.WordTrace]
  refine ⟨103001674837945765698860813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68667783225297177132573875 103001674837945765698860813)
  ·
    refine ⟨38625628064229662137072805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103001674837945765698860813 38625628064229662137072805)
    ·
      refine ⟨7242305262043061650701151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38625628064229662137072805 7242305262043061650701151)
      ·
        refine ⟨10863457893064592476051727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7242305262043061650701151 10863457893064592476051727)
        ·
          refine ⟨16295186839596888714077591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10863457893064592476051727 16295186839596888714077591)
          ·
            refine ⟨24442780259395333071116387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16295186839596888714077591 24442780259395333071116387)
            ·
              refine ⟨36664170389092999606674581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24442780259395333071116387 36664170389092999606674581)
              ·
                refine ⟨1718632986988734356562871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36664170389092999606674581 1718632986988734356562871)
                ·
                  refine ⟨2577949480483101534844307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1718632986988734356562871 2577949480483101534844307)
                  ·
                    refine ⟨3866924220724652302266461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2577949480483101534844307 3866924220724652302266461)
                    ·
                      refine ⟨1450096582771744613349923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3866924220724652302266461 1450096582771744613349923)
                      ·
                        rfl

theorem cell23_2824053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_2824053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824053 prefixEnd_2824053 := by exact prefixLift 2824053
  have htrace : WordTrace (prefixWord ++ tailWord_2824053) baseStart_2824053 baseEnd_2824053 := by
    simpa [prefixWord, tailWord_2824053, baseEnd_2824053] using wordTrace_append hprefix tailTrace_2824053
  have hstable : (prefixWord ++ tailWord_2824053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824053).length < 2 ^ (prefixWord ++ tailWord_2824053).sum := by decide
  have hdescent : baseEnd_2824053 < baseStart_2824053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824104 : List Nat := [2, 1, 6, 2, 1, 1, 3, 2, 1, 1, 3]
def baseStart_2824104 : Nat := 118140960795 + 2824104 * 2 ^ 59
def prefixEnd_2824104 : Nat := 4983230072969 + 3 ^ 40 * 2824104 * 2
def baseEnd_2824104 : Nat := 1450122770285123913812189

theorem tailTrace_2824104 : CollatzResearch.WordTrace tailWord_2824104 prefixEnd_2824104 1450122770285123913812189 := by
  unfold tailWord_2824104
  simp only [CollatzResearch.WordTrace]
  refine ⟨51501767480380500704483683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68669023307174000939311577 51501767480380500704483683)
  ·
    refine ⟨77252651220570751056725525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51501767480380500704483683 77252651220570751056725525)
    ·
      refine ⟨3621218025964253955784009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 77252651220570751056725525 3621218025964253955784009)
      ·
        refine ⟨2715913519473190466838007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3621218025964253955784009 2715913519473190466838007)
        ·
          refine ⟨4073870279209785700257011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2715913519473190466838007 4073870279209785700257011)
          ·
            refine ⟨6110805418814678550385517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4073870279209785700257011 6110805418814678550385517)
            ·
              refine ⟨2291552032055504456394569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6110805418814678550385517 2291552032055504456394569)
              ·
                refine ⟨1718664024041628342295927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2291552032055504456394569 1718664024041628342295927)
                ·
                  refine ⟨2577996036062442513443891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1718664024041628342295927 2577996036062442513443891)
                  ·
                    refine ⟨3866994054093663770165837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2577996036062442513443891 3866994054093663770165837)
                    ·
                      refine ⟨1450122770285123913812189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3866994054093663770165837 1450122770285123913812189)
                      ·
                        rfl

theorem cell23_2824104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_2824104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824104 prefixEnd_2824104 := by exact prefixLift 2824104
  have htrace : WordTrace (prefixWord ++ tailWord_2824104) baseStart_2824104 baseEnd_2824104 := by
    simpa [prefixWord, tailWord_2824104, baseEnd_2824104] using wordTrace_append hprefix tailTrace_2824104
  have hstable : (prefixWord ++ tailWord_2824104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824104).length < 2 ^ (prefixWord ++ tailWord_2824104).sum := by decide
  have hdescent : baseEnd_2824104 < baseStart_2824104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824119 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 2, 7, 2]
def baseStart_2824119 : Nat := 118140960795 + 2824119 * 2 ^ 59
def prefixEnd_2824119 : Nat := 4983230072969 + 3 ^ 40 * 2824119 * 2
def baseEnd_2824119 : Nat := 1450130472494941355124619

theorem tailTrace_2824119 : CollatzResearch.WordTrace tailWord_2824119 prefixEnd_2824119 1450130472494941355124619 := by
  unfold tailWord_2824119
  simp only [CollatzResearch.WordTrace]
  refine ⟨103004082055706658970763411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68669388037137772647175607 103004082055706658970763411)
  ·
    refine ⟨154506123083559988456145117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103004082055706658970763411 154506123083559988456145117)
    ·
      refine ⟨57939796156334995671054419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154506123083559988456145117 57939796156334995671054419)
      ·
        refine ⟨86909694234502493506581629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57939796156334995671054419 86909694234502493506581629)
        ·
          refine ⟨32591135337938435064968111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86909694234502493506581629 32591135337938435064968111)
          ·
            refine ⟨48886703006907652597452167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32591135337938435064968111 48886703006907652597452167)
            ·
              refine ⟨73330054510361478896178251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48886703006907652597452167 73330054510361478896178251)
              ·
                refine ⟨109995081765542218344267377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73330054510361478896178251 109995081765542218344267377)
                ·
                  refine ⟨82496311324156663758200533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109995081765542218344267377 82496311324156663758200533)
                  ·
                    refine ⟨1933507296659921806832825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 82496311324156663758200533 1933507296659921806832825)
                    ·
                      refine ⟨1450130472494941355124619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1933507296659921806832825 1450130472494941355124619)
                      ·
                        rfl

theorem cell23_2824119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 7, 2].length) (baseStart_2824119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824119 prefixEnd_2824119 := by exact prefixLift 2824119
  have htrace : WordTrace (prefixWord ++ tailWord_2824119) baseStart_2824119 baseEnd_2824119 := by
    simpa [prefixWord, tailWord_2824119, baseEnd_2824119] using wordTrace_append hprefix tailTrace_2824119
  have hstable : (prefixWord ++ tailWord_2824119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824119).length < 2 ^ (prefixWord ++ tailWord_2824119).sum := by decide
  have hdescent : baseEnd_2824119 < baseStart_2824119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824122 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 1, 4, 5]
def baseStart_2824122 : Nat := 118140960795 + 2824122 * 2 ^ 59
def prefixEnd_2824122 : Nat := 4983230072969 + 3 ^ 40 * 2824122 * 2
def baseEnd_2824122 : Nat := 1450132012936904843387105

theorem tailTrace_2824122 : CollatzResearch.WordTrace tailWord_2824122 prefixEnd_2824122 1450132012936904843387105 := by
  unfold tailWord_2824122
  simp only [CollatzResearch.WordTrace]
  refine ⟨25751047868673947620780655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68669460983130526988748413 25751047868673947620780655)
  ·
    refine ⟨38626571803010921431170983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25751047868673947620780655 38626571803010921431170983)
    ·
      refine ⟨57939857704516382146756475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38626571803010921431170983 57939857704516382146756475)
      ·
        refine ⟨86909786556774573220134713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57939857704516382146756475 86909786556774573220134713)
        ·
          refine ⟨65182339917580929915101035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86909786556774573220134713 65182339917580929915101035)
          ·
            refine ⟨97773509876371394872651553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65182339917580929915101035 97773509876371394872651553)
            ·
              refine ⟨73330132407278546154488665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97773509876371394872651553 73330132407278546154488665)
              ·
                refine ⟨54997599305458909615866499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73330132407278546154488665 54997599305458909615866499)
                ·
                  refine ⟨82496398958188364423799749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54997599305458909615866499 82496398958188364423799749)
                  ·
                    refine ⟨15468074804660318329462453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82496398958188364423799749 15468074804660318329462453)
                    ·
                      refine ⟨1450132012936904843387105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15468074804660318329462453 1450132012936904843387105)
                      ·
                        rfl

theorem cell23_2824122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_2824122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824122 prefixEnd_2824122 := by exact prefixLift 2824122
  have htrace : WordTrace (prefixWord ++ tailWord_2824122) baseStart_2824122 baseEnd_2824122 := by
    simpa [prefixWord, tailWord_2824122, baseEnd_2824122] using wordTrace_append hprefix tailTrace_2824122
  have hstable : (prefixWord ++ tailWord_2824122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824122).length < 2 ^ (prefixWord ++ tailWord_2824122).sum := by decide
  have hdescent : baseEnd_2824122 < baseStart_2824122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824172 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 11]
def baseStart_2824172 : Nat := 118140960795 + 2824172 * 2 ^ 59
def prefixEnd_2824172 : Nat := 4983230072969 + 3 ^ 40 * 2824172 * 2
def baseEnd_2824172 : Nat := 161128631885514405306875

theorem tailTrace_2824172 : CollatzResearch.WordTrace tailWord_2824172 prefixEnd_2824172 161128631885514405306875 := by
  unfold tailWord_2824172
  simp only [CollatzResearch.WordTrace]
  refine ⟨51503007562257324511221385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68670676749676432681628513 51503007562257324511221385)
  ·
    refine ⟨38627255671692993383416039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51503007562257324511221385 38627255671692993383416039)
    ·
      refine ⟨57940883507539490075124059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38627255671692993383416039 57940883507539490075124059)
      ·
        refine ⟨86911325261309235112686089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57940883507539490075124059 86911325261309235112686089)
        ·
          refine ⟨65183493945981926334514567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86911325261309235112686089 65183493945981926334514567)
          ·
            refine ⟨97775240918972889501771851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65183493945981926334514567 97775240918972889501771851)
            ·
              refine ⟨146662861378459334252657777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97775240918972889501771851 146662861378459334252657777)
              ·
                refine ⟨109997146033844500689493333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146662861378459334252657777 109997146033844500689493333)
                ·
                  refine ⟨161128631885514405306875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 109997146033844500689493333 161128631885514405306875)
                  ·
                    rfl

theorem cell23_2824172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 11].length) (baseStart_2824172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824172 prefixEnd_2824172 := by exact prefixLift 2824172
  have htrace : WordTrace (prefixWord ++ tailWord_2824172) baseStart_2824172 baseEnd_2824172 := by
    simpa [prefixWord, tailWord_2824172, baseEnd_2824172] using wordTrace_append hprefix tailTrace_2824172
  have hstable : (prefixWord ++ tailWord_2824172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824172).length < 2 ^ (prefixWord ++ tailWord_2824172).sum := by decide
  have hdescent : baseEnd_2824172 < baseStart_2824172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824198 : List Nat := [6, 2, 1, 2, 2, 1, 2, 1, 1, 2, 3]
def baseStart_2824198 : Nat := 118140960795 + 2824198 * 2 ^ 59
def prefixEnd_2824198 : Nat := 4983230072969 + 3 ^ 40 * 2824198 * 2
def baseEnd_2824198 : Nat := 1450171037466646546036757

theorem tailTrace_2824198 : CollatzResearch.WordTrace tailWord_2824198 prefixEnd_2824198 1450171037466646546036757 := by
  unfold tailWord_2824198
  simp only [CollatzResearch.WordTrace]
  refine ⟨3218967606950639233215289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 68671308948280303641926165 3218967606950639233215289)
  ·
    refine ⟨2414225705212979424911467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3218967606950639233215289 2414225705212979424911467)
    ·
      refine ⟨3621338557819469137367201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2414225705212979424911467 3621338557819469137367201)
      ·
        refine ⟨2716003918364601853025401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3621338557819469137367201 2716003918364601853025401)
        ·
          refine ⟨2037002938773451389769051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2716003918364601853025401 2037002938773451389769051)
          ·
            refine ⟨3055504408160177084653577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2037002938773451389769051 3055504408160177084653577)
            ·
              refine ⟨2291628306120132813490183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3055504408160177084653577 2291628306120132813490183)
              ·
                refine ⟨3437442459180199220235275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2291628306120132813490183 3437442459180199220235275)
                ·
                  refine ⟨5156163688770298830352913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3437442459180199220235275 5156163688770298830352913)
                  ·
                    refine ⟨3867122766577724122764685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5156163688770298830352913 3867122766577724122764685)
                    ·
                      refine ⟨1450171037466646546036757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3867122766577724122764685 1450171037466646546036757)
                      ·
                        rfl

theorem cell23_2824198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_2824198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824198 prefixEnd_2824198 := by exact prefixLift 2824198
  have htrace : WordTrace (prefixWord ++ tailWord_2824198) baseStart_2824198 baseEnd_2824198 := by
    simpa [prefixWord, tailWord_2824198, baseEnd_2824198] using wordTrace_append hprefix tailTrace_2824198
  have hstable : (prefixWord ++ tailWord_2824198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824198).length < 2 ^ (prefixWord ++ tailWord_2824198).sum := by decide
  have hdescent : baseEnd_2824198 < baseStart_2824198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824239 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 4]
def baseStart_2824239 : Nat := 118140960795 + 2824239 * 2 ^ 59
def prefixEnd_2824239 : Nat := 4983230072969 + 3 ^ 40 * 2824239 * 2
def baseEnd_2824239 : Nat := 1450192090173480885624067

theorem tailTrace_2824239 : CollatzResearch.WordTrace tailWord_2824239 prefixEnd_2824239 1450192090173480885624067 := by
  unfold tailWord_2824239
  simp only [CollatzResearch.WordTrace]
  refine ⟨103008458815271919465131771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68672305876847946310087847 103008458815271919465131771)
  ·
    refine ⟨154512688222907879197697657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103008458815271919465131771 154512688222907879197697657)
    ·
      refine ⟨115884516167180909398273243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154512688222907879197697657 115884516167180909398273243)
      ·
        refine ⟨173826774250771364097409865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115884516167180909398273243 173826774250771364097409865)
        ·
          refine ⟨130370080688078523073057399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173826774250771364097409865 130370080688078523073057399)
          ·
            refine ⟨195555121032117784609586099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130370080688078523073057399 195555121032117784609586099)
            ·
              refine ⟨293332681548176676914379149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195555121032117784609586099 293332681548176676914379149)
              ·
                refine ⟨109999755580566253842892181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 293332681548176676914379149 109999755580566253842892181)
                ·
                  refine ⟨5156238542839043148885571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 109999755580566253842892181 5156238542839043148885571)
                  ·
                    refine ⟨7734357814258564723328357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5156238542839043148885571 7734357814258564723328357)
                    ·
                      refine ⟨1450192090173480885624067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7734357814258564723328357 1450192090173480885624067)
                      ·
                        rfl

theorem cell23_2824239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 4].length) (baseStart_2824239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824239 prefixEnd_2824239 := by exact prefixLift 2824239
  have htrace : WordTrace (prefixWord ++ tailWord_2824239) baseStart_2824239 baseEnd_2824239 := by
    simpa [prefixWord, tailWord_2824239, baseEnd_2824239] using wordTrace_append hprefix tailTrace_2824239
  have hstable : (prefixWord ++ tailWord_2824239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824239).length < 2 ^ (prefixWord ++ tailWord_2824239).sum := by decide
  have hdescent : baseEnd_2824239 < baseStart_2824239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824279 : List Nat := [1, 1, 3, 2, 2, 1, 4, 1, 8]
def baseStart_2824279 : Nat := 118140960795 + 2824279 * 2 ^ 59
def prefixEnd_2824279 : Nat := 4983230072969 + 3 ^ 40 * 2824279 * 2
def baseEnd_2824279 : Nat := 161134736599962303235987

theorem tailTrace_2824279 : CollatzResearch.WordTrace tailWord_2824279 prefixEnd_2824279 161134736599962303235987 := by
  unfold tailWord_2824279
  simp only [CollatzResearch.WordTrace]
  refine ⟨103009917735127006296587891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68673278490084670864391927 103009917735127006296587891)
  ·
    refine ⟨154514876602690509444881837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103009917735127006296587891 154514876602690509444881837)
    ·
      refine ⟨57943078726008941041830689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154514876602690509444881837 57943078726008941041830689)
      ·
        refine ⟨43457309044506705781373017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57943078726008941041830689 43457309044506705781373017)
        ·
          refine ⟨32592981783380029336029763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43457309044506705781373017 32592981783380029336029763)
          ·
            refine ⟨48889472675070044004044645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32592981783380029336029763 48889472675070044004044645)
            ·
              refine ⟨9166776126575633250758371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48889472675070044004044645 9166776126575633250758371)
              ·
                refine ⟨13750164189863449876137557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9166776126575633250758371 13750164189863449876137557)
                ·
                  refine ⟨161134736599962303235987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13750164189863449876137557 161134736599962303235987)
                  ·
                    rfl

theorem cell23_2824279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 8].length) (baseStart_2824279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824279 prefixEnd_2824279 := by exact prefixLift 2824279
  have htrace : WordTrace (prefixWord ++ tailWord_2824279) baseStart_2824279 baseEnd_2824279 := by
    simpa [prefixWord, tailWord_2824279, baseEnd_2824279] using wordTrace_append hprefix tailTrace_2824279
  have hstable : (prefixWord ++ tailWord_2824279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824279).length < 2 ^ (prefixWord ++ tailWord_2824279).sum := by decide
  have hdescent : baseEnd_2824279 < baseStart_2824279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824310 : List Nat := [5, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3]
def baseStart_2824310 : Nat := 118140960795 + 2824310 * 2 ^ 59
def prefixEnd_2824310 : Nat := 4983230072969 + 3 ^ 40 * 2824310 * 2
def baseEnd_2824310 : Nat := 1450228547299950107836241

theorem tailTrace_2824310 : CollatzResearch.WordTrace tailWord_2824310 prefixEnd_2824310 1450228547299950107836241 := by
  unfold tailWord_2824310
  simp only [CollatzResearch.WordTrace]
  refine ⟨6438190524875918661935399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68674032265343132393977589 6438190524875918661935399)
  ·
    refine ⟨9657285787313877992903099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6438190524875918661935399 9657285787313877992903099)
    ·
      refine ⟨14485928680970816989354649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9657285787313877992903099 14485928680970816989354649)
      ·
        refine ⟨10864446510728112742015987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14485928680970816989354649 10864446510728112742015987)
        ·
          refine ⟨16296669766092169113023981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10864446510728112742015987 16296669766092169113023981)
          ·
            refine ⟨6111251162284563417383993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16296669766092169113023981 6111251162284563417383993)
            ·
              refine ⟨4583438371713422563037995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6111251162284563417383993 4583438371713422563037995)
              ·
                refine ⟨6875157557570133844556993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4583438371713422563037995 6875157557570133844556993)
                ·
                  refine ⟨5156368168177600383417745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6875157557570133844556993 5156368168177600383417745)
                  ·
                    refine ⟨3867276126133200287563309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5156368168177600383417745 3867276126133200287563309)
                    ·
                      refine ⟨1450228547299950107836241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3867276126133200287563309 1450228547299950107836241)
                      ·
                        rfl

theorem cell23_2824310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_2824310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824310 prefixEnd_2824310 := by exact prefixLift 2824310
  have htrace : WordTrace (prefixWord ++ tailWord_2824310) baseStart_2824310 baseEnd_2824310 := by
    simpa [prefixWord, tailWord_2824310, baseEnd_2824310] using wordTrace_append hprefix tailTrace_2824310
  have hstable : (prefixWord ++ tailWord_2824310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824310).length < 2 ^ (prefixWord ++ tailWord_2824310).sum := by decide
  have hdescent : baseEnd_2824310 < baseStart_2824310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824334 : List Nat := [4, 1, 1, 3, 3, 2, 2, 2, 1, 4]
def baseStart_2824334 : Nat := 118140960795 + 2824334 * 2 ^ 59
def prefixEnd_2824334 : Nat := 4983230072969 + 3 ^ 40 * 2824334 * 2
def baseEnd_2824334 : Nat := 483413623611886004645377

theorem tailTrace_2824334 : CollatzResearch.WordTrace tailWord_2824334 prefixEnd_2824334 483413623611886004645377 := by
  unfold tailWord_2824334
  simp only [CollatzResearch.WordTrace]
  refine ⟨12876490468740968836230007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68674615833285167126560037 12876490468740968836230007)
  ·
    refine ⟨19314735703111453254345011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12876490468740968836230007 19314735703111453254345011)
    ·
      refine ⟨28972103554667179881517517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19314735703111453254345011 28972103554667179881517517)
      ·
        refine ⟨10864538833000192455569069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28972103554667179881517517 10864538833000192455569069)
        ·
          refine ⟨4074202062375072170838401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10864538833000192455569069 4074202062375072170838401)
          ·
            refine ⟨3055651546781304128128801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4074202062375072170838401 3055651546781304128128801)
            ·
              refine ⟨2291738660085978096096601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3055651546781304128128801 2291738660085978096096601)
              ·
                refine ⟨1718803995064483572072451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2291738660085978096096601 1718803995064483572072451)
                ·
                  refine ⟨2578205992596725358108677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1718803995064483572072451 2578205992596725358108677)
                  ·
                    refine ⟨483413623611886004645377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2578205992596725358108677 483413623611886004645377)
                    ·
                      rfl

theorem cell23_2824334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_2824334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824334 prefixEnd_2824334 := by exact prefixLift 2824334
  have htrace : WordTrace (prefixWord ++ tailWord_2824334) baseStart_2824334 baseEnd_2824334 := by
    simpa [prefixWord, tailWord_2824334, baseEnd_2824334] using wordTrace_append hprefix tailTrace_2824334
  have hstable : (prefixWord ++ tailWord_2824334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824334).length < 2 ^ (prefixWord ++ tailWord_2824334).sum := by decide
  have hdescent : baseEnd_2824334 < baseStart_2824334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824339 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 5, 6]
def baseStart_2824339 : Nat := 118140960795 + 2824339 * 2 ^ 59
def prefixEnd_2824339 : Nat := 4983230072969 + 3 ^ 40 * 2824339 * 2
def baseEnd_2824339 : Nat := 483414479412976831457869

theorem tailTrace_2824339 : CollatzResearch.WordTrace tailWord_2824339 prefixEnd_2824339 483414479412976831457869 := by
  unfold tailWord_2824339
  simp only [CollatzResearch.WordTrace]
  refine ⟨103012106114909636543772071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68674737409939757695848047 103012106114909636543772071)
  ·
    refine ⟨154518159172364454815658107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103012106114909636543772071 154518159172364454815658107)
    ·
      refine ⟨231777238758546682223487161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154518159172364454815658107 231777238758546682223487161)
      ·
        refine ⟨173832929068910011667615371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231777238758546682223487161 173832929068910011667615371)
        ·
          refine ⟨260749393603365017501423057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173832929068910011667615371 260749393603365017501423057)
          ·
            refine ⟨195562045202523763126067293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260749393603365017501423057 195562045202523763126067293)
            ·
              refine ⟨73335766950946411172275235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 195562045202523763126067293 73335766950946411172275235)
              ·
                refine ⟨110003650426419616758412853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73335766950946411172275235 110003650426419616758412853)
                ·
                  refine ⟨10312842227476839071101205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110003650426419616758412853 10312842227476839071101205)
                  ·
                    refine ⟨483414479412976831457869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10312842227476839071101205 483414479412976831457869)
                    ·
                      rfl

theorem cell23_2824339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 6].length) (baseStart_2824339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824339 prefixEnd_2824339 := by exact prefixLift 2824339
  have htrace : WordTrace (prefixWord ++ tailWord_2824339) baseStart_2824339 baseEnd_2824339 := by
    simpa [prefixWord, tailWord_2824339, baseEnd_2824339] using wordTrace_append hprefix tailTrace_2824339
  have hstable : (prefixWord ++ tailWord_2824339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824339).length < 2 ^ (prefixWord ++ tailWord_2824339).sum := by decide
  have hdescent : baseEnd_2824339 < baseStart_2824339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824376 : List Nat := [2, 1, 2, 1, 2, 1, 3, 4, 1, 2, 4]
def baseStart_2824376 : Nat := 118140960795 + 2824376 * 2 ^ 59
def prefixEnd_2824376 : Nat := 4983230072969 + 3 ^ 40 * 2824376 * 2
def baseEnd_2824376 : Nat := 1450262437023146849610937

theorem tailTrace_2824376 : CollatzResearch.WordTrace tailWord_2824376 prefixEnd_2824376 1450262437023146849610937 := by
  unfold tailWord_2824376
  simp only [CollatzResearch.WordTrace]
  refine ⟨51506727807887795931434491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68675637077183727908579321 51506727807887795931434491)
  ·
    refine ⟨77260091711831693897151737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51506727807887795931434491 77260091711831693897151737)
    ·
      refine ⟨57945068783873770422863803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77260091711831693897151737 57945068783873770422863803)
      ·
        refine ⟨86917603175810655634295705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57945068783873770422863803 86917603175810655634295705)
        ·
          refine ⟨65188202381857991725721779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86917603175810655634295705 65188202381857991725721779)
          ·
            refine ⟨97782303572786987588582669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65188202381857991725721779 97782303572786987588582669)
            ·
              refine ⟨36668363839795120345718501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97782303572786987588582669 36668363839795120345718501)
              ·
                refine ⟨6875318219961585064822219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36668363839795120345718501 6875318219961585064822219)
                ·
                  refine ⟨10312977329942377597233329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6875318219961585064822219 10312977329942377597233329)
                  ·
                    refine ⟨7734732997456783197924997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10312977329942377597233329 7734732997456783197924997)
                    ·
                      refine ⟨1450262437023146849610937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7734732997456783197924997 1450262437023146849610937)
                      ·
                        rfl

theorem cell23_2824376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_2824376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824376 prefixEnd_2824376 := by exact prefixLift 2824376
  have htrace : WordTrace (prefixWord ++ tailWord_2824376) baseStart_2824376 baseEnd_2824376 := by
    simpa [prefixWord, tailWord_2824376, baseEnd_2824376] using wordTrace_append hprefix tailTrace_2824376
  have hstable : (prefixWord ++ tailWord_2824376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824376).length < 2 ^ (prefixWord ++ tailWord_2824376).sum := by decide
  have hdescent : baseEnd_2824376 < baseStart_2824376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824380 : List Nat := [2, 2, 2, 3, 3, 1, 1, 3, 1, 1, 4]
def baseStart_2824380 : Nat := 118140960795 + 2824380 * 2 ^ 59
def prefixEnd_2824380 : Nat := 4983230072969 + 3 ^ 40 * 2824380 * 2
def baseEnd_2824380 : Nat := 1450264490945764833960919

theorem tailTrace_2824380 : CollatzResearch.WordTrace tailWord_2824380 prefixEnd_2824380 1450264490945764833960919 := by
  unfold tailWord_2824380
  simp only [CollatzResearch.WordTrace]
  refine ⟨51506800753880550273007297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68675734338507400364009729 51506800753880550273007297)
  ·
    refine ⟨38630100565410412704755473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51506800753880550273007297 38630100565410412704755473)
    ·
      refine ⟨28972575424057809528566605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38630100565410412704755473 28972575424057809528566605)
      ·
        refine ⟨10864715784021678573212477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28972575424057809528566605 10864715784021678573212477)
        ·
          refine ⟨4074268419008129464954679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10864715784021678573212477 4074268419008129464954679)
          ·
            refine ⟨6111402628512194197432019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4074268419008129464954679 6111402628512194197432019)
            ·
              refine ⟨9167103942768291296148029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6111402628512194197432019 9167103942768291296148029)
              ·
                refine ⟨3437663978538109236055511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9167103942768291296148029 3437663978538109236055511)
                ·
                  refine ⟨5156495967807163854083267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3437663978538109236055511 5156495967807163854083267)
                  ·
                    refine ⟨7734743951710745781124901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5156495967807163854083267 7734743951710745781124901)
                    ·
                      refine ⟨1450264490945764833960919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7734743951710745781124901 1450264490945764833960919)
                      ·
                        rfl

theorem cell23_2824380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_2824380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824380 prefixEnd_2824380 := by exact prefixLift 2824380
  have htrace : WordTrace (prefixWord ++ tailWord_2824380) baseStart_2824380 baseEnd_2824380 := by
    simpa [prefixWord, tailWord_2824380, baseEnd_2824380] using wordTrace_append hprefix tailTrace_2824380
  have hstable : (prefixWord ++ tailWord_2824380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824380).length < 2 ^ (prefixWord ++ tailWord_2824380).sum := by decide
  have hdescent : baseEnd_2824380 < baseStart_2824380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824426 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 1, 4, 5]
def baseStart_2824426 : Nat := 118140960795 + 2824426 * 2 ^ 59
def prefixEnd_2824426 : Nat := 4983230072969 + 3 ^ 40 * 2824426 * 2
def baseEnd_2824426 : Nat := 1450288111055871653985707

theorem tailTrace_2824426 : CollatzResearch.WordTrace tailWord_2824426 prefixEnd_2824426 1450288111055871653985707 := by
  unfold tailWord_2824426
  simp only [CollatzResearch.WordTrace]
  refine ⟨25753819816398612600547283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68676852843729633601459421 25753819816398612600547283)
  ·
    refine ⟨38630729724597918900820925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25753819816398612600547283 38630729724597918900820925)
    ·
      refine ⟨14486523646724219587807847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38630729724597918900820925 14486523646724219587807847)
      ·
        refine ⟨21729785470086329381711771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14486523646724219587807847 21729785470086329381711771)
        ·
          refine ⟨32594678205129494072567657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21729785470086329381711771 32594678205129494072567657)
          ·
            refine ⟨24446008653847120554425743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32594678205129494072567657 24446008653847120554425743)
            ·
              refine ⟨36669012980770680831638615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24446008653847120554425743 36669012980770680831638615)
              ·
                refine ⟨55003519471156021247457923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36669012980770680831638615 55003519471156021247457923)
                ·
                  refine ⟨82505279206734031871186885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55003519471156021247457923 82505279206734031871186885)
                  ·
                    refine ⟨15469739851262630975847541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82505279206734031871186885 15469739851262630975847541)
                    ·
                      refine ⟨1450288111055871653985707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15469739851262630975847541 1450288111055871653985707)
                      ·
                        rfl

theorem cell23_2824426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_2824426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824426 prefixEnd_2824426 := by exact prefixLift 2824426
  have htrace : WordTrace (prefixWord ++ tailWord_2824426) baseStart_2824426 baseEnd_2824426 := by
    simpa [prefixWord, tailWord_2824426, baseEnd_2824426] using wordTrace_append hprefix tailTrace_2824426
  have hstable : (prefixWord ++ tailWord_2824426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824426).length < 2 ^ (prefixWord ++ tailWord_2824426).sum := by decide
  have hdescent : baseEnd_2824426 < baseStart_2824426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824453 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 5, 4, 2]
def baseStart_2824453 : Nat := 118140960795 + 2824453 * 2 ^ 59
def prefixEnd_2824453 : Nat := 4983230072969 + 3 ^ 40 * 2824453 * 2
def baseEnd_2824453 : Nat := 1450301975033543048348083

theorem tailTrace_2824453 : CollatzResearch.WordTrace tailWord_2824453 prefixEnd_2824453 1450301975033543048348083 := by
  unfold tailWord_2824453
  simp only [CollatzResearch.WordTrace]
  refine ⟨103016264036496634013422013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68677509357664422675614675 103016264036496634013422013)
  ·
    refine ⟨38631099013686237755033255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103016264036496634013422013 38631099013686237755033255)
    ·
      refine ⟨57946648520529356632549883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38631099013686237755033255 57946648520529356632549883)
      ·
        refine ⟨86919972780794034948824825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57946648520529356632549883 86919972780794034948824825)
        ·
          refine ⟨65189979585595526211618619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86919972780794034948824825 65189979585595526211618619)
          ·
            refine ⟨97784969378393289317427929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65189979585595526211618619 97784969378393289317427929)
            ·
              refine ⟨73338727033794966988070947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97784969378393289317427929 73338727033794966988070947)
              ·
                refine ⟨110008090550692450482106421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73338727033794966988070947 110008090550692450482106421)
                ·
                  refine ⟨10313258489127417232697477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110008090550692450482106421 10313258489127417232697477)
                  ·
                    refine ⟨1933735966711390731130777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10313258489127417232697477 1933735966711390731130777)
                    ·
                      refine ⟨1450301975033543048348083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1933735966711390731130777 1450301975033543048348083)
                      ·
                        rfl

theorem cell23_2824453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 4, 2].length) (baseStart_2824453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824453 prefixEnd_2824453 := by exact prefixLift 2824453
  have htrace : WordTrace (prefixWord ++ tailWord_2824453) baseStart_2824453 baseEnd_2824453 := by
    simpa [prefixWord, tailWord_2824453, baseEnd_2824453] using wordTrace_append hprefix tailTrace_2824453
  have hstable : (prefixWord ++ tailWord_2824453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824453).length < 2 ^ (prefixWord ++ tailWord_2824453).sum := by decide
  have hdescent : baseEnd_2824453 < baseStart_2824453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824474 : List Nat := [3, 1, 1, 3, 4, 2, 1, 2, 1, 3, 2]
def baseStart_2824474 : Nat := 118140960795 + 2824474 * 2 ^ 59
def prefixEnd_2824474 : Nat := 4983230072969 + 3 ^ 40 * 2824474 * 2
def baseEnd_2824474 : Nat := 1450312758127287466185487

theorem tailTrace_2824474 : CollatzResearch.WordTrace tailWord_2824474 prefixEnd_2824474 1450312758127287466185487 := by
  unfold tailWord_2824474
  simp only [CollatzResearch.WordTrace]
  refine ⟨25754257492355138649984119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68678019979613703066624317 25754257492355138649984119)
  ·
    refine ⟨38631386238532707974976179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25754257492355138649984119 38631386238532707974976179)
    ·
      refine ⟨57947079357799061962464269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38631386238532707974976179 57947079357799061962464269)
      ·
        refine ⟨21730154759174648235924101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57947079357799061962464269 21730154759174648235924101)
        ·
          refine ⟨4074404017345246544235769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21730154759174648235924101 4074404017345246544235769)
          ·
            refine ⟨3055803013008934908176827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4074404017345246544235769 3055803013008934908176827)
            ·
              refine ⟨4583704519513402362265241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3055803013008934908176827 4583704519513402362265241)
              ·
                refine ⟨3437778389635051771698931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4583704519513402362265241 3437778389635051771698931)
                ·
                  refine ⟨5156667584452577657548397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3437778389635051771698931 5156667584452577657548397)
                  ·
                    refine ⟨1933750344169716621580649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5156667584452577657548397 1933750344169716621580649)
                    ·
                      refine ⟨1450312758127287466185487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1933750344169716621580649 1450312758127287466185487)
                      ·
                        rfl

theorem cell23_2824474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_2824474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824474 prefixEnd_2824474 := by exact prefixLift 2824474
  have htrace : WordTrace (prefixWord ++ tailWord_2824474) baseStart_2824474 baseEnd_2824474 := by
    simpa [prefixWord, tailWord_2824474, baseEnd_2824474] using wordTrace_append hprefix tailTrace_2824474
  have hstable : (prefixWord ++ tailWord_2824474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824474).length < 2 ^ (prefixWord ++ tailWord_2824474).sum := by decide
  have hdescent : baseEnd_2824474 < baseStart_2824474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824476 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 9]
def baseStart_2824476 : Nat := 118140960795 + 2824476 * 2 ^ 59
def prefixEnd_2824476 : Nat := 4983230072969 + 3 ^ 40 * 2824476 * 2
def baseEnd_2824476 : Nat := 161145976120955162040053

theorem tailTrace_2824476 : CollatzResearch.WordTrace tailWord_2824476 prefixEnd_2824476 161145976120955162040053 := by
  unfold tailWord_2824476
  simp only [CollatzResearch.WordTrace]
  refine ⟨51508551457706654470754641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68678068610275539294339521 51508551457706654470754641)
  ·
    refine ⟨38631413593279990853065981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51508551457706654470754641 38631413593279990853065981)
    ·
      refine ⟨14486780097479996569899743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38631413593279990853065981 14486780097479996569899743)
      ·
        refine ⟨21730170146219994854849615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14486780097479996569899743 21730170146219994854849615)
        ·
          refine ⟨32595255219329992282274423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21730170146219994854849615 32595255219329992282274423)
          ·
            refine ⟨48892882828994988423411635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32595255219329992282274423 48892882828994988423411635)
            ·
              refine ⟨73339324243492482635117453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48892882828994988423411635 73339324243492482635117453)
              ·
                refine ⟨27502246591309680988169045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73339324243492482635117453 27502246591309680988169045)
                ·
                  refine ⟨161145976120955162040053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27502246591309680988169045 161145976120955162040053)
                  ·
                    rfl

theorem cell23_2824476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 9].length) (baseStart_2824476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824476 prefixEnd_2824476 := by exact prefixLift 2824476
  have htrace : WordTrace (prefixWord ++ tailWord_2824476) baseStart_2824476 baseEnd_2824476 := by
    simpa [prefixWord, tailWord_2824476, baseEnd_2824476] using wordTrace_append hprefix tailTrace_2824476
  have hstable : (prefixWord ++ tailWord_2824476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824476).length < 2 ^ (prefixWord ++ tailWord_2824476).sum := by decide
  have hdescent : baseEnd_2824476 < baseStart_2824476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824536 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 1, 10]
def baseStart_2824536 : Nat := 118140960795 + 2824536 * 2 ^ 59
def prefixEnd_2824536 : Nat := 4983230072969 + 3 ^ 40 * 2824536 * 2
def baseEnd_2824536 : Nat := 483448197975955407870067

theorem tailTrace_2824536 : CollatzResearch.WordTrace tailWord_2824536 prefixEnd_2824536 483448197975955407870067 := by
  unfold tailWord_2824536
  simp only [CollatzResearch.WordTrace]
  refine ⟨51509645647597969594346731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68679527530130626125795641 51509645647597969594346731)
  ·
    refine ⟨77264468471396954391520097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51509645647597969594346731 77264468471396954391520097)
    ·
      refine ⟨57948351353547715793640073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77264468471396954391520097 57948351353547715793640073)
      ·
        refine ⟨43461263515160786845230055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57948351353547715793640073 43461263515160786845230055)
        ·
          refine ⟨65191895272741180267845083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43461263515160786845230055 65191895272741180267845083)
          ·
            refine ⟨97787842909111770401767625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65191895272741180267845083 97787842909111770401767625)
            ·
              refine ⟨73340882181833827801325719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97787842909111770401767625 73340882181833827801325719)
              ·
                refine ⟨110011323272750741701988579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73340882181833827801325719 110011323272750741701988579)
                ·
                  refine ⟨165016984909126112552982869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110011323272750741701988579 165016984909126112552982869)
                  ·
                    refine ⟨483448197975955407870067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 165016984909126112552982869 483448197975955407870067)
                    ·
                      rfl

theorem cell23_2824536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 10].length) (baseStart_2824536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824536 prefixEnd_2824536 := by exact prefixLift 2824536
  have htrace : WordTrace (prefixWord ++ tailWord_2824536) baseStart_2824536 baseEnd_2824536 := by
    simpa [prefixWord, tailWord_2824536, baseEnd_2824536] using wordTrace_append hprefix tailTrace_2824536
  have hstable : (prefixWord ++ tailWord_2824536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824536).length < 2 ^ (prefixWord ++ tailWord_2824536).sum := by decide
  have hdescent : baseEnd_2824536 < baseStart_2824536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824542 : List Nat := [4, 4, 2, 1, 1, 2, 2, 1, 1, 3, 2]
def baseStart_2824542 : Nat := 118140960795 + 2824542 * 2 ^ 59
def prefixEnd_2824542 : Nat := 4983230072969 + 3 ^ 40 * 2824542 * 2
def baseEnd_2824542 : Nat := 1450347674811793200135175

theorem tailTrace_2824542 : CollatzResearch.WordTrace tailWord_2824542 prefixEnd_2824542 1450347674811793200135175 := by
  unfold tailWord_2824542
  simp only [CollatzResearch.WordTrace]
  refine ⟨12877438766646775276676485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68679673422116134808941253 12877438766646775276676485)
  ·
    refine ⟨2414519768746270364376841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12877438766646775276676485 2414519768746270364376841)
    ·
      refine ⟨1810889826559702773282631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2414519768746270364376841 1810889826559702773282631)
      ·
        refine ⟨2716334739839554159923947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1810889826559702773282631 2716334739839554159923947)
        ·
          refine ⟨4074502109759331239885921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2716334739839554159923947 4074502109759331239885921)
          ·
            refine ⟨3055876582319498429914441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4074502109759331239885921 3055876582319498429914441)
            ·
              refine ⟨2291907436739623822435831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3055876582319498429914441 2291907436739623822435831)
              ·
                refine ⟨3437861155109435733653747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2291907436739623822435831 3437861155109435733653747)
                ·
                  refine ⟨5156791732664153600480621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3437861155109435733653747 5156791732664153600480621)
                  ·
                    refine ⟨1933796899749057600180233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5156791732664153600480621 1933796899749057600180233)
                    ·
                      refine ⟨1450347674811793200135175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1933796899749057600180233 1450347674811793200135175)
                      ·
                        rfl

theorem cell23_2824542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_2824542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824542 prefixEnd_2824542 := by exact prefixLift 2824542
  have htrace : WordTrace (prefixWord ++ tailWord_2824542) baseStart_2824542 baseEnd_2824542 := by
    simpa [prefixWord, tailWord_2824542, baseEnd_2824542] using wordTrace_append hprefix tailTrace_2824542
  have hstable : (prefixWord ++ tailWord_2824542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824542).length < 2 ^ (prefixWord ++ tailWord_2824542).sum := by decide
  have hdescent : baseEnd_2824542 < baseStart_2824542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824553 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 5, 4]
def baseStart_2824553 : Nat := 118140960795 + 2824553 * 2 ^ 59
def prefixEnd_2824553 : Nat := 4983230072969 + 3 ^ 40 * 2824553 * 2
def baseEnd_2824553 : Nat := 483451107699664219032541

theorem tailTrace_2824553 : CollatzResearch.WordTrace tailWord_2824553 prefixEnd_2824553 483451107699664219032541 := by
  unfold tailWord_2824553
  simp only [CollatzResearch.WordTrace]
  refine ⟨103019911336134351092062313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68679940890756234061374875 103019911336134351092062313)
  ·
    refine ⟨77264933502100763319046735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103019911336134351092062313 77264933502100763319046735)
    ·
      refine ⟨115897400253151144978570103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77264933502100763319046735 115897400253151144978570103)
      ·
        refine ⟨173846100379726717467855155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115897400253151144978570103 173846100379726717467855155)
        ·
          refine ⟨260769150569590076201782733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173846100379726717467855155 260769150569590076201782733)
          ·
            refine ⟨97788431463596278575668525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260769150569590076201782733 97788431463596278575668525)
            ·
              refine ⟨36670661798848604465875697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97788431463596278575668525 36670661798848604465875697)
              ·
                refine ⟨27502996349136453349406773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36670661798848604465875697 27502996349136453349406773)
                ·
                  refine ⟨2578405907731542501506885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27502996349136453349406773 2578405907731542501506885)
                  ·
                    refine ⟨483451107699664219032541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2578405907731542501506885 483451107699664219032541)
                    ·
                      rfl

theorem cell23_2824553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 5, 4].length) (baseStart_2824553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824553 prefixEnd_2824553 := by exact prefixLift 2824553
  have htrace : WordTrace (prefixWord ++ tailWord_2824553) baseStart_2824553 baseEnd_2824553 := by
    simpa [prefixWord, tailWord_2824553, baseEnd_2824553] using wordTrace_append hprefix tailTrace_2824553
  have hstable : (prefixWord ++ tailWord_2824553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824553).length < 2 ^ (prefixWord ++ tailWord_2824553).sum := by decide
  have hdescent : baseEnd_2824553 < baseStart_2824553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824560 : List Nat := [2, 1, 1, 1, 4, 3, 1, 2, 2, 4, 2]
def baseStart_2824560 : Nat := 118140960795 + 2824560 * 2 ^ 59
def prefixEnd_2824560 : Nat := 4983230072969 + 3 ^ 40 * 2824560 * 2
def baseEnd_2824560 : Nat := 1450356917463574129710091

theorem tailTrace_2824560 : CollatzResearch.WordTrace tailWord_2824560 prefixEnd_2824560 1450356917463574129710091 := by
  unfold tailWord_2824560
  simp only [CollatzResearch.WordTrace]
  refine ⟨51510083323554495643783567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68680111098072660858378089 51510083323554495643783567)
  ·
    refine ⟨77265124985331743465675351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51510083323554495643783567 77265124985331743465675351)
    ·
      refine ⟨115897687477997615198513027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77265124985331743465675351 115897687477997615198513027)
      ·
        refine ⟨173846531216996422797769541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115897687477997615198513027 173846531216996422797769541)
        ·
          refine ⟨32596224603186829274581789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173846531216996422797769541 32596224603186829274581789)
          ·
            refine ⟨12223584226195060977968171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32596224603186829274581789 12223584226195060977968171)
            ·
              refine ⟨18335376339292591466952257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12223584226195060977968171 18335376339292591466952257)
              ·
                refine ⟨13751532254469443600214193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18335376339292591466952257 13751532254469443600214193)
                ·
                  refine ⟨10313649190852082700160645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13751532254469443600214193 10313649190852082700160645)
                  ·
                    refine ⟨1933809223284765506280121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10313649190852082700160645 1933809223284765506280121)
                    ·
                      refine ⟨1450356917463574129710091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1933809223284765506280121 1450356917463574129710091)
                      ·
                        rfl

theorem cell23_2824560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 2, 4, 2].length) (baseStart_2824560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824560 prefixEnd_2824560 := by exact prefixLift 2824560
  have htrace : WordTrace (prefixWord ++ tailWord_2824560) baseStart_2824560 baseEnd_2824560 := by
    simpa [prefixWord, tailWord_2824560, baseEnd_2824560] using wordTrace_append hprefix tailTrace_2824560
  have hstable : (prefixWord ++ tailWord_2824560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824560).length < 2 ^ (prefixWord ++ tailWord_2824560).sum := by decide
  have hdescent : baseEnd_2824560 < baseStart_2824560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824577 : List Nat := [1, 2, 4, 3, 1, 1, 2, 1, 2, 4, 2]
def baseStart_2824577 : Nat := 118140960795 + 2824577 * 2 ^ 59
def prefixEnd_2824577 : Nat := 4983230072969 + 3 ^ 40 * 2824577 * 2
def baseEnd_2824577 : Nat := 1450365646634700563197513

theorem tailTrace_2824577 : CollatzResearch.WordTrace tailWord_2824577 prefixEnd_2824577 1450365646634700563197513 := by
  unfold tailWord_2824577
  simp only [CollatzResearch.WordTrace]
  refine ⟨103020786688047403190935985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68680524458698268793957323 103020786688047403190935985)
  ·
    refine ⟨77265590016035552393201989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103020786688047403190935985 77265590016035552393201989)
    ·
      refine ⟨14487298128006666073725373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77265590016035552393201989 14487298128006666073725373)
      ·
        refine ⟨5432736798002499777647015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14487298128006666073725373 5432736798002499777647015)
        ·
          refine ⟨8149105197003749666470523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5432736798002499777647015 8149105197003749666470523)
          ·
            refine ⟨12223657795505624499705785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8149105197003749666470523 12223657795505624499705785)
            ·
              refine ⟨9167743346629218374779339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12223657795505624499705785 9167743346629218374779339)
              ·
                refine ⟨13751615019943827562169009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9167743346629218374779339 13751615019943827562169009)
                ·
                  refine ⟨10313711264957870671626757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13751615019943827562169009 10313711264957870671626757)
                  ·
                    refine ⟨1933820862179600750930017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10313711264957870671626757 1933820862179600750930017)
                    ·
                      refine ⟨1450365646634700563197513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1933820862179600750930017 1450365646634700563197513)
                      ·
                        rfl

theorem cell23_2824577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_2824577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824577 prefixEnd_2824577 := by exact prefixLift 2824577
  have htrace : WordTrace (prefixWord ++ tailWord_2824577) baseStart_2824577 baseEnd_2824577 := by
    simpa [prefixWord, tailWord_2824577, baseEnd_2824577] using wordTrace_append hprefix tailTrace_2824577
  have hstable : (prefixWord ++ tailWord_2824577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824577).length < 2 ^ (prefixWord ++ tailWord_2824577).sum := by decide
  have hdescent : baseEnd_2824577 < baseStart_2824577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824621 : List Nat := [1, 5, 2, 2, 3, 1, 1, 1, 3, 4]
def baseStart_2824621 : Nat := 118140960795 + 2824621 * 2 ^ 59
def prefixEnd_2824621 : Nat := 4983230072969 + 3 ^ 40 * 2824621 * 2
def baseEnd_2824621 : Nat := 483462746594499463682437

theorem tailTrace_2824621 : CollatzResearch.WordTrace tailWord_2824621 prefixEnd_2824621 483462746594499463682437 := by
  unfold tailWord_2824621
  simp only [CollatzResearch.WordTrace]
  refine ⟨103022391499887998705537717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68681594333258665803691811 103022391499887998705537717)
  ·
    refine ⟨9658349203114499878644161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103022391499887998705537717 9658349203114499878644161)
    ·
      refine ⟨7243761902335874908983121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9658349203114499878644161 7243761902335874908983121)
      ·
        refine ⟨5432821426751906181737341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7243761902335874908983121 5432821426751906181737341)
        ·
          refine ⟨2037308035031964818151503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5432821426751906181737341 2037308035031964818151503)
          ·
            refine ⟨3055962052547947227227255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2037308035031964818151503 3055962052547947227227255)
            ·
              refine ⟨4583943078821920840840883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3055962052547947227227255 4583943078821920840840883)
              ·
                refine ⟨6875914618232881261261325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4583943078821920840840883 6875914618232881261261325)
                ·
                  refine ⟨2578467981837330472972997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6875914618232881261261325 2578467981837330472972997)
                  ·
                    refine ⟨483462746594499463682437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2578467981837330472972997 483462746594499463682437)
                    ·
                      rfl

theorem cell23_2824621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_2824621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824621 prefixEnd_2824621 := by exact prefixLift 2824621
  have htrace : WordTrace (prefixWord ++ tailWord_2824621) baseStart_2824621 baseEnd_2824621 := by
    simpa [prefixWord, tailWord_2824621, baseEnd_2824621] using wordTrace_append hprefix tailTrace_2824621
  have hstable : (prefixWord ++ tailWord_2824621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824621).length < 2 ^ (prefixWord ++ tailWord_2824621).sum := by decide
  have hdescent : baseEnd_2824621 < baseStart_2824621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824643 : List Nat := [1, 1, 1, 3, 1, 1, 3, 5, 1, 6]
def baseStart_2824643 : Nat := 118140960795 + 2824643 * 2 ^ 59
def prefixEnd_2824643 : Nat := 4983230072969 + 3 ^ 40 * 2824643 * 2
def baseEnd_2824643 : Nat := 483466512119299101657403

theorem tailTrace_2824643 : CollatzResearch.WordTrace tailWord_2824643 prefixEnd_2824643 483466512119299101657403 := by
  unfold tailWord_2824643
  simp only [CollatzResearch.WordTrace]
  refine ⟨103023193905808296462838583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68682129270538864308559055 103023193905808296462838583)
  ·
    refine ⟨154534790858712444694257875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103023193905808296462838583 154534790858712444694257875)
    ·
      refine ⟨231802186288068667041386813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154534790858712444694257875 231802186288068667041386813)
      ·
        refine ⟨86925819858025750140520055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231802186288068667041386813 86925819858025750140520055)
        ·
          refine ⟨130388729787038625210780083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86925819858025750140520055 130388729787038625210780083)
          ·
            refine ⟨195583094680557937816170125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130388729787038625210780083 195583094680557937816170125)
            ·
              refine ⟨73343660505209226681063797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 195583094680557937816170125 73343660505209226681063797)
              ·
                refine ⟨6875968172363365001349731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73343660505209226681063797 6875968172363365001349731)
                ·
                  refine ⟨10313952258545047502024597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6875968172363365001349731 10313952258545047502024597)
                  ·
                    refine ⟨483466512119299101657403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10313952258545047502024597 483466512119299101657403)
                    ·
                      rfl

theorem cell23_2824643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 6].length) (baseStart_2824643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824643 prefixEnd_2824643 := by exact prefixLift 2824643
  have htrace : WordTrace (prefixWord ++ tailWord_2824643) baseStart_2824643 baseEnd_2824643 := by
    simpa [prefixWord, tailWord_2824643, baseEnd_2824643] using wordTrace_append hprefix tailTrace_2824643
  have hstable : (prefixWord ++ tailWord_2824643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824643).length < 2 ^ (prefixWord ++ tailWord_2824643).sum := by decide
  have hdescent : baseEnd_2824643 < baseStart_2824643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824647 : List Nat := [1, 1, 4, 1, 1, 6, 1, 2, 1, 5]
def baseStart_2824647 : Nat := 118140960795 + 2824647 * 2 ^ 59
def prefixEnd_2824647 : Nat := 4983230072969 + 3 ^ 40 * 2824647 * 2
def baseEnd_2824647 : Nat := 483467196760171763107397

theorem tailTrace_2824647 : CollatzResearch.WordTrace tailWord_2824647 prefixEnd_2824647 483467196760171763107397 := by
  unfold tailWord_2824647
  simp only [CollatzResearch.WordTrace]
  refine ⟨103023339797793805145984195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68682226531862536763989463 103023339797793805145984195)
  ·
    refine ⟨154535009696690707718976293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103023339797793805145984195 154535009696690707718976293)
    ·
      refine ⟨28975314318129507697308055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 154535009696690707718976293 28975314318129507697308055)
      ·
        refine ⟨43462971477194261545962083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28975314318129507697308055 43462971477194261545962083)
        ·
          refine ⟨65194457215791392318943125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43462971477194261545962083 65194457215791392318943125)
          ·
            refine ⟨3055990181990221514950459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65194457215791392318943125 3055990181990221514950459)
            ·
              refine ⟨4583985272985332272425689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3055990181990221514950459 4583985272985332272425689)
              ·
                refine ⟨3437988954738999204319267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4583985272985332272425689 3437988954738999204319267)
                ·
                  refine ⟨5156983432108498806478901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3437988954738999204319267 5156983432108498806478901)
                  ·
                    refine ⟨483467196760171763107397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5156983432108498806478901 483467196760171763107397)
                    ·
                      rfl

theorem cell23_2824647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_2824647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824647 prefixEnd_2824647 := by exact prefixLift 2824647
  have htrace : WordTrace (prefixWord ++ tailWord_2824647) baseStart_2824647 baseEnd_2824647 := by
    simpa [prefixWord, tailWord_2824647, baseEnd_2824647] using wordTrace_append hprefix tailTrace_2824647
  have hstable : (prefixWord ++ tailWord_2824647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824647).length < 2 ^ (prefixWord ++ tailWord_2824647).sum := by decide
  have hdescent : baseEnd_2824647 < baseStart_2824647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824650 : List Nat := [3, 1, 2, 1, 2, 2, 3, 1, 3, 1, 4]
def baseStart_2824650 : Nat := 118140960795 + 2824650 * 2 ^ 59
def prefixEnd_2824650 : Nat := 4983230072969 + 3 ^ 40 * 2824650 * 2
def baseEnd_2824650 : Nat := 1450403130722478777584677

theorem tailTrace_2824650 : CollatzResearch.WordTrace tailWord_2824650 prefixEnd_2824650 1450403130722478777584677 := by
  unfold tailWord_2824650
  simp only [CollatzResearch.WordTrace]
  refine ⟨25755862304195734164585851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68682299477855291105562269 25755862304195734164585851)
  ·
    refine ⟨38633793456293601246878777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25755862304195734164585851 38633793456293601246878777)
    ·
      refine ⟨28975345092220200935159083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38633793456293601246878777 28975345092220200935159083)
      ·
        refine ⟨43463017638330301402738625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28975345092220200935159083 43463017638330301402738625)
        ·
          refine ⟨32597263228747726052053969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43463017638330301402738625 32597263228747726052053969)
          ·
            refine ⟨24447947421560794539040477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32597263228747726052053969 24447947421560794539040477)
            ·
              refine ⟨9167980283085297952140179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24447947421560794539040477 9167980283085297952140179)
              ·
                refine ⟨13751970424627946928210269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9167980283085297952140179 13751970424627946928210269)
                ·
                  refine ⟨5156988909235480098078851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13751970424627946928210269 5156988909235480098078851)
                  ·
                    refine ⟨7735483363853220147118277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5156988909235480098078851 7735483363853220147118277)
                    ·
                      refine ⟨1450403130722478777584677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7735483363853220147118277 1450403130722478777584677)
                      ·
                        rfl

theorem cell23_2824650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_2824650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824650 prefixEnd_2824650 := by exact prefixLift 2824650
  have htrace : WordTrace (prefixWord ++ tailWord_2824650) baseStart_2824650 baseEnd_2824650 := by
    simpa [prefixWord, tailWord_2824650, baseEnd_2824650] using wordTrace_append hprefix tailTrace_2824650
  have hstable : (prefixWord ++ tailWord_2824650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824650).length < 2 ^ (prefixWord ++ tailWord_2824650).sum := by decide
  have hdescent : baseEnd_2824650 < baseStart_2824650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824660 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 3, 6]
def baseStart_2824660 : Nat := 118140960795 + 2824660 * 2 ^ 59
def prefixEnd_2824660 : Nat := 4983230072969 + 3 ^ 40 * 2824660 * 2
def baseEnd_2824660 : Nat := 483469421843007912819877

theorem tailTrace_2824660 : CollatzResearch.WordTrace tailWord_2824660 prefixEnd_2824660 483469421843007912819877 := by
  unfold tailWord_2824660
  simp only [CollatzResearch.WordTrace]
  refine ⟨51511906973373354183103717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68682542631164472244138289 51511906973373354183103717)
  ·
    refine ⟨9658482557507503909331947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51511906973373354183103717 9658482557507503909331947)
    ·
      refine ⟨14487723836261255863997921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9658482557507503909331947 14487723836261255863997921)
      ·
        refine ⟨10865792877195941897998441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14487723836261255863997921 10865792877195941897998441)
        ·
          refine ⟨8149344657896956423498831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10865792877195941897998441 8149344657896956423498831)
          ·
            refine ⟨12224016986845434635248247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8149344657896956423498831 12224016986845434635248247)
            ·
              refine ⟨18336025480268151952872371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12224016986845434635248247 18336025480268151952872371)
              ·
                refine ⟨27504038220402227929308557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18336025480268151952872371 27504038220402227929308557)
                ·
                  refine ⟨10314014332650835473490709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27504038220402227929308557 10314014332650835473490709)
                  ·
                    refine ⟨483469421843007912819877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10314014332650835473490709 483469421843007912819877)
                    ·
                      rfl

theorem cell23_2824660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_2824660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824660 prefixEnd_2824660 := by exact prefixLift 2824660
  have htrace : WordTrace (prefixWord ++ tailWord_2824660) baseStart_2824660 baseEnd_2824660 := by
    simpa [prefixWord, tailWord_2824660, baseEnd_2824660] using wordTrace_append hprefix tailTrace_2824660
  have hstable : (prefixWord ++ tailWord_2824660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824660).length < 2 ^ (prefixWord ++ tailWord_2824660).sum := by decide
  have hdescent : baseEnd_2824660 < baseStart_2824660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824703 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 2, 7]
def baseStart_2824703 : Nat := 118140960795 + 2824703 * 2 ^ 59
def prefixEnd_2824703 : Nat := 4983230072969 + 3 ^ 40 * 2824703 * 2
def baseEnd_2824703 : Nat := 483476781732389023407311

theorem tailTrace_2824703 : CollatzResearch.WordTrace tailWord_2824703 prefixEnd_2824703 483476781732389023407311 := by
  unfold tailWord_2824703
  simp only [CollatzResearch.WordTrace]
  refine ⟨103025382285590926710022763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68683588190393951140015175 103025382285590926710022763)
  ·
    refine ⟨154538073428386390065034145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103025382285590926710022763 154538073428386390065034145)
    ·
      refine ⟨115903555071289792548775609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154538073428386390065034145 115903555071289792548775609)
      ·
        refine ⟨86927666303467344411581707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115903555071289792548775609 86927666303467344411581707)
        ·
          refine ⟨130391499455201016617372561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86927666303467344411581707 130391499455201016617372561)
          ·
            refine ⟨97793624591400762463029421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130391499455201016617372561 97793624591400762463029421)
            ·
              refine ⟨36672609221775285923636033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97793624591400762463029421 36672609221775285923636033)
              ·
                refine ⟨27504456916331464442727025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36672609221775285923636033 27504456916331464442727025)
                ·
                  refine ⟨20628342687248598332045269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27504456916331464442727025 20628342687248598332045269)
                  ·
                    refine ⟨483476781732389023407311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20628342687248598332045269 483476781732389023407311)
                    ·
                      rfl

theorem cell23_2824703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 7].length) (baseStart_2824703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824703 prefixEnd_2824703 := by exact prefixLift 2824703
  have htrace : WordTrace (prefixWord ++ tailWord_2824703) baseStart_2824703 baseEnd_2824703 := by
    simpa [prefixWord, tailWord_2824703, baseEnd_2824703] using wordTrace_append hprefix tailTrace_2824703
  have hstable : (prefixWord ++ tailWord_2824703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824703).length < 2 ^ (prefixWord ++ tailWord_2824703).sum := by decide
  have hdescent : baseEnd_2824703 < baseStart_2824703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824718 : List Nat := [4, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2]
def baseStart_2824718 : Nat := 118140960795 + 2824718 * 2 ^ 59
def prefixEnd_2824718 : Nat := 4983230072969 + 3 ^ 40 * 2824718 * 2
def baseEnd_2824718 : Nat := 1450438047406984511534365

theorem tailTrace_2824718 : CollatzResearch.WordTrace tailWord_2824718 prefixEnd_2824718 1450438047406984511534365 := by
  unfold tailWord_2824718
  simp only [CollatzResearch.WordTrace]
  refine ⟨12878241172567073033977351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68683952920357722847879205 12878241172567073033977351)
  ·
    refine ⟨19317361758850609550966027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12878241172567073033977351 19317361758850609550966027)
    ·
      refine ⟨28976042638275914326449041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19317361758850609550966027 28976042638275914326449041)
      ·
        refine ⟨21732031978706935744836781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28976042638275914326449041 21732031978706935744836781)
        ·
          refine ⟨8149511992015100904313793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21732031978706935744836781 8149511992015100904313793)
          ·
            refine ⟨6112133994011325678235345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8149511992015100904313793 6112133994011325678235345)
            ·
              refine ⟨4584100495508494258676509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6112133994011325678235345 4584100495508494258676509)
              ·
                refine ⟨1719037685815685347003691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4584100495508494258676509 1719037685815685347003691)
                ·
                  refine ⟨2578556528723528020505537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1719037685815685347003691 2578556528723528020505537)
                  ·
                    refine ⟨1933917396542646015379153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2578556528723528020505537 1933917396542646015379153)
                    ·
                      refine ⟨1450438047406984511534365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1933917396542646015379153 1450438047406984511534365)
                      ·
                        rfl

theorem cell23_2824718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_2824718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824718 prefixEnd_2824718 := by exact prefixLift 2824718
  have htrace : WordTrace (prefixWord ++ tailWord_2824718) baseStart_2824718 baseEnd_2824718 := by
    simpa [prefixWord, tailWord_2824718, baseEnd_2824718] using wordTrace_append hprefix tailTrace_2824718
  have hstable : (prefixWord ++ tailWord_2824718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824718).length < 2 ^ (prefixWord ++ tailWord_2824718).sum := by decide
  have hdescent : baseEnd_2824718 < baseStart_2824718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824760 : List Nat := [2, 1, 2, 1, 4, 1, 2, 2, 2, 1, 5]
def baseStart_2824760 : Nat := 118140960795 + 2824760 * 2 ^ 59
def prefixEnd_2824760 : Nat := 4983230072969 + 3 ^ 40 * 2824760 * 2
def baseEnd_2824760 : Nat := 1450459613594473347209171

theorem tailTrace_2824760 : CollatzResearch.WordTrace tailWord_2824760 prefixEnd_2824760 1450459613594473347209171 := by
  unfold tailWord_2824760
  simp only [CollatzResearch.WordTrace]
  refine ⟨51513730623192212722423867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68684974164256283629898489 51513730623192212722423867)
  ·
    refine ⟨77270595934788319083635801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51513730623192212722423867 77270595934788319083635801)
    ·
      refine ⟨57952946951091239312726851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77270595934788319083635801 57952946951091239312726851)
      ·
        refine ⟨86929420426636858969090277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57952946951091239312726851 86929420426636858969090277)
        ·
          refine ⟨16299266329994411056704427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86929420426636858969090277 16299266329994411056704427)
          ·
            refine ⟨24448899494991616585056641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16299266329994411056704427 24448899494991616585056641)
            ·
              refine ⟨18336674621243712438792481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24448899494991616585056641 18336674621243712438792481)
              ·
                refine ⟨13752505965932784329094361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18336674621243712438792481 13752505965932784329094361)
                ·
                  refine ⟨10314379474449588246820771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13752505965932784329094361 10314379474449588246820771)
                  ·
                    refine ⟨15471569211674382370231157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10314379474449588246820771 15471569211674382370231157)
                    ·
                      refine ⟨1450459613594473347209171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15471569211674382370231157 1450459613594473347209171)
                      ·
                        rfl

theorem cell23_2824760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_2824760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824760 prefixEnd_2824760 := by exact prefixLift 2824760
  have htrace : WordTrace (prefixWord ++ tailWord_2824760) baseStart_2824760 baseEnd_2824760 := by
    simpa [prefixWord, tailWord_2824760, baseEnd_2824760] using wordTrace_append hprefix tailTrace_2824760
  have hstable : (prefixWord ++ tailWord_2824760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824760).length < 2 ^ (prefixWord ++ tailWord_2824760).sum := by decide
  have hdescent : baseEnd_2824760 < baseStart_2824760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824763 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 13]
def baseStart_2824763 : Nat := 118140960795 + 2824763 * 2 ^ 59
def prefixEnd_2824763 : Nat := 4983230072969 + 3 ^ 40 * 2824763 * 2
def baseEnd_2824763 : Nat := 161162350448492981719073

theorem tailTrace_2824763 : CollatzResearch.WordTrace tailWord_2824763 prefixEnd_2824763 161162350448492981719073 := by
  unfold tailWord_2824763
  simp only [CollatzResearch.WordTrace]
  refine ⟨103027570665373556957206943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68685047110249037971471295 103027570665373556957206943)
  ·
    refine ⟨154541355998060335435810415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103027570665373556957206943 154541355998060335435810415)
    ·
      refine ⟨231812033997090503153715623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154541355998060335435810415 231812033997090503153715623)
      ·
        refine ⟨347718050995635754730573435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231812033997090503153715623 347718050995635754730573435)
        ·
          refine ⟨521577076493453632095860153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347718050995635754730573435 521577076493453632095860153)
          ·
            refine ⟨391182807370090224071895115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 521577076493453632095860153 391182807370090224071895115)
            ·
              refine ⟨586774211055135336107842673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391182807370090224071895115 586774211055135336107842673)
              ·
                refine ⟨440080658291351502080882005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 586774211055135336107842673 440080658291351502080882005)
                ·
                  refine ⟨161162350448492981719073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 440080658291351502080882005 161162350448492981719073)
                  ·
                    rfl

theorem cell23_2824763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 13].length) (baseStart_2824763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824763 prefixEnd_2824763 := by exact prefixLift 2824763
  have htrace : WordTrace (prefixWord ++ tailWord_2824763) baseStart_2824763 baseEnd_2824763 := by
    simpa [prefixWord, tailWord_2824763, baseEnd_2824763] using wordTrace_append hprefix tailTrace_2824763
  have hstable : (prefixWord ++ tailWord_2824763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824763).length < 2 ^ (prefixWord ++ tailWord_2824763).sum := by decide
  have hdescent : baseEnd_2824763 < baseStart_2824763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824802 : List Nat := [3, 3, 2, 3, 2, 1, 2, 1, 2, 1, 3]
def baseStart_2824802 : Nat := 118140960795 + 2824802 * 2 ^ 59
def prefixEnd_2824802 : Nat := 4983230072969 + 3 ^ 40 * 2824802 * 2
def baseEnd_2824802 : Nat := 1450481179781962182883979

theorem tailTrace_2824802 : CollatzResearch.WordTrace tailWord_2824802 prefixEnd_2824802 1450481179781962182883979 := by
  unfold tailWord_2824802
  simp only [CollatzResearch.WordTrace]
  refine ⟨25757248278058066654469165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68685995408154844411917773 25757248278058066654469165)
  ·
    refine ⟨9658968104271774995425937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25757248278058066654469165 9658968104271774995425937)
    ·
      refine ⟨7244226078203831246569453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9658968104271774995425937 7244226078203831246569453)
      ·
        refine ⟨2716584779326436717463545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7244226078203831246569453 2716584779326436717463545)
        ·
          refine ⟨2037438584494827538097659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2716584779326436717463545 2037438584494827538097659)
          ·
            refine ⟨3056157876742241307146489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2037438584494827538097659 3056157876742241307146489)
            ·
              refine ⟨2292118407556680980359867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3056157876742241307146489 2292118407556680980359867)
              ·
                refine ⟨3438177611335021470539801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2292118407556680980359867 3438177611335021470539801)
                ·
                  refine ⟨2578633208501266102904851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3438177611335021470539801 2578633208501266102904851)
                  ·
                    refine ⟨3867949812751899154357277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2578633208501266102904851 3867949812751899154357277)
                    ·
                      refine ⟨1450481179781962182883979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3867949812751899154357277 1450481179781962182883979)
                      ·
                        rfl

theorem cell23_2824802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_2824802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824802 prefixEnd_2824802 := by exact prefixLift 2824802
  have htrace : WordTrace (prefixWord ++ tailWord_2824802) baseStart_2824802 baseEnd_2824802 := by
    simpa [prefixWord, tailWord_2824802, baseEnd_2824802] using wordTrace_append hprefix tailTrace_2824802
  have hstable : (prefixWord ++ tailWord_2824802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824802).length < 2 ^ (prefixWord ++ tailWord_2824802).sum := by decide
  have hdescent : baseEnd_2824802 < baseStart_2824802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824808 : List Nat := [2, 1, 4, 3, 2, 1, 1, 3, 2, 2, 2]
def baseStart_2824808 : Nat := 118140960795 + 2824808 * 2 ^ 59
def prefixEnd_2824808 : Nat := 4983230072969 + 3 ^ 40 * 2824808 * 2
def baseEnd_2824808 : Nat := 1450484260665889159408951

theorem tailTrace_2824808 : CollatzResearch.WordTrace tailWord_2824808 prefixEnd_2824808 1450484260665889159408951 := by
  unfold tailWord_2824808
  simp only [CollatzResearch.WordTrace]
  refine ⟨51514605975105264821297539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68686141300140353095063385 51514605975105264821297539)
  ·
    refine ⟨77271908962657897231946309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51514605975105264821297539 77271908962657897231946309)
    ·
      refine ⟨14488482930498355730989933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77271908962657897231946309 14488482930498355730989933)
      ·
        refine ⟨5433181098936883399121225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14488482930498355730989933 5433181098936883399121225)
        ·
          refine ⟨4074885824202662549340919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5433181098936883399121225 4074885824202662549340919)
          ·
            refine ⟨6112328736303993824011379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4074885824202662549340919 6112328736303993824011379)
            ·
              refine ⟨9168493104455990736017069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6112328736303993824011379 9168493104455990736017069)
              ·
                refine ⟨3438184914170996526006401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9168493104455990736017069 3438184914170996526006401)
                ·
                  refine ⟨2578638685628247394504801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3438184914170996526006401 2578638685628247394504801)
                  ·
                    refine ⟨1933979014221185545878601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2578638685628247394504801 1933979014221185545878601)
                    ·
                      refine ⟨1450484260665889159408951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1933979014221185545878601 1450484260665889159408951)
                      ·
                        rfl

theorem cell23_2824808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_2824808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824808 prefixEnd_2824808 := by exact prefixLift 2824808
  have htrace : WordTrace (prefixWord ++ tailWord_2824808) baseStart_2824808 baseEnd_2824808 := by
    simpa [prefixWord, tailWord_2824808, baseEnd_2824808] using wordTrace_append hprefix tailTrace_2824808
  have hstable : (prefixWord ++ tailWord_2824808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824808).length < 2 ^ (prefixWord ++ tailWord_2824808).sum := by decide
  have hdescent : baseEnd_2824808 < baseStart_2824808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824847 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 4, 4, 2]
def baseStart_2824847 : Nat := 118140960795 + 2824847 * 2 ^ 59
def prefixEnd_2824847 : Nat := 4983230072969 + 3 ^ 40 * 2824847 * 2
def baseEnd_2824847 : Nat := 1450504286411414506821271

theorem tailTrace_2824847 : CollatzResearch.WordTrace tailWord_2824847 prefixEnd_2824847 1450504286411414506821271 := by
  unfold tailWord_2824847
  simp only [CollatzResearch.WordTrace]
  refine ⟨103030634397069239303264795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68687089598046159535509863 103030634397069239303264795)
  ·
    refine ⟨154545951595603858954897193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103030634397069239303264795 154545951595603858954897193)
    ·
      refine ⟨115909463696702894216172895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154545951595603858954897193 115909463696702894216172895)
      ·
        refine ⟨173864195545054341324259343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115909463696702894216172895 173864195545054341324259343)
        ·
          refine ⟨260796293317581511986389015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173864195545054341324259343 260796293317581511986389015)
          ·
            refine ⟨391194439976372267979583523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260796293317581511986389015 391194439976372267979583523)
            ·
              refine ⟨586791659964558401969375285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391194439976372267979583523 586791659964558401969375285)
              ·
                refine ⟨55011718121677350184628933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 586791659964558401969375285 55011718121677350184628933)
                ·
                  refine ⟨10314697147814503159617925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55011718121677350184628933 10314697147814503159617925)
                  ·
                    refine ⟨1934005715215219342428361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10314697147814503159617925 1934005715215219342428361)
                    ·
                      refine ⟨1450504286411414506821271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1934005715215219342428361 1450504286411414506821271)
                      ·
                        rfl

theorem cell23_2824847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 4, 2].length) (baseStart_2824847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824847 prefixEnd_2824847 := by exact prefixLift 2824847
  have htrace : WordTrace (prefixWord ++ tailWord_2824847) baseStart_2824847 baseEnd_2824847 := by
    simpa [prefixWord, tailWord_2824847, baseEnd_2824847] using wordTrace_append hprefix tailTrace_2824847
  have hstable : (prefixWord ++ tailWord_2824847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824847).length < 2 ^ (prefixWord ++ tailWord_2824847).sum := by decide
  have hdescent : baseEnd_2824847 < baseStart_2824847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824857 : List Nat := [1, 2, 1, 2, 1, 2, 4, 3, 3, 4]
def baseStart_2824857 : Nat := 118140960795 + 2824857 * 2 ^ 59
def prefixEnd_2824857 : Nat := 4983230072969 + 3 ^ 40 * 2824857 * 2
def baseEnd_2824857 : Nat := 483503140405986489232075

theorem tailTrace_2824857 : CollatzResearch.WordTrace tailWord_2824857 prefixEnd_2824857 483503140405986489232075 := by
  unfold tailWord_2824857
  simp only [CollatzResearch.WordTrace]
  refine ⟨103030999127033011011128825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68687332751355340674085883 103030999127033011011128825)
  ·
    refine ⟨77273249345274758258346619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103030999127033011011128825 77273249345274758258346619)
    ·
      refine ⟨115909874017912137387519929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77273249345274758258346619 115909874017912137387519929)
      ·
        refine ⟨86932405513434103040639947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115909874017912137387519929 86932405513434103040639947)
        ·
          refine ⟨130398608270151154560959921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86932405513434103040639947 130398608270151154560959921)
          ·
            refine ⟨97798956202613365920719941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130398608270151154560959921 97798956202613365920719941)
            ·
              refine ⟨18337304287990006110134989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97798956202613365920719941 18337304287990006110134989)
              ·
                refine ⟨6876489107996252291300621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18337304287990006110134989 6876489107996252291300621)
                ·
                  refine ⟨2578683415498594609237733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6876489107996252291300621 2578683415498594609237733)
                  ·
                    refine ⟨483503140405986489232075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2578683415498594609237733 483503140405986489232075)
                    ·
                      rfl

theorem cell23_2824857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 3, 4].length) (baseStart_2824857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824857 prefixEnd_2824857 := by exact prefixLift 2824857
  have htrace : WordTrace (prefixWord ++ tailWord_2824857) baseStart_2824857 baseEnd_2824857 := by
    simpa [prefixWord, tailWord_2824857, baseEnd_2824857] using wordTrace_append hprefix tailTrace_2824857
  have hstable : (prefixWord ++ tailWord_2824857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824857).length < 2 ^ (prefixWord ++ tailWord_2824857).sum := by decide
  have hdescent : baseEnd_2824857 < baseStart_2824857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824904 : List Nat := [2, 1, 3, 1, 2, 5, 1, 2, 6]
def baseStart_2824904 : Nat := 118140960795 + 2824904 * 2 ^ 59
def prefixEnd_2824904 : Nat := 4983230072969 + 3 ^ 40 * 2824904 * 2
def baseEnd_2824904 : Nat := 161170394978746753756501

theorem tailTrace_2824904 : CollatzResearch.WordTrace tailWord_2824904 prefixEnd_2824904 161170394978746753756501 := by
  unfold tailWord_2824904
  simp only [CollatzResearch.WordTrace]
  refine ⟨51516356678931369019044883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68688475571908492025393177 51516356678931369019044883)
  ·
    refine ⟨77274535018397053528567325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51516356678931369019044883 77274535018397053528567325)
    ·
      refine ⟨28977950631898895073212747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77274535018397053528567325 28977950631898895073212747)
      ·
        refine ⟨43466925947848342609819121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28977950631898895073212747 43466925947848342609819121)
        ·
          refine ⟨32600194460886256957364341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43466925947848342609819121 32600194460886256957364341)
          ·
            refine ⟨3056268230708086589752907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32600194460886256957364341 3056268230708086589752907)
            ·
              refine ⟨4584402346062129884629361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3056268230708086589752907 4584402346062129884629361)
              ·
                refine ⟨3438301759546597413472021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4584402346062129884629361 3438301759546597413472021)
                ·
                  refine ⟨161170394978746753756501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3438301759546597413472021 161170394978746753756501)
                  ·
                    rfl

theorem cell23_2824904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 6].length) (baseStart_2824904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824904 prefixEnd_2824904 := by exact prefixLift 2824904
  have htrace : WordTrace (prefixWord ++ tailWord_2824904) baseStart_2824904 baseEnd_2824904 := by
    simpa [prefixWord, tailWord_2824904, baseEnd_2824904] using wordTrace_append hprefix tailTrace_2824904
  have hstable : (prefixWord ++ tailWord_2824904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824904).length < 2 ^ (prefixWord ++ tailWord_2824904).sum := by decide
  have hdescent : baseEnd_2824904 < baseStart_2824904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824931 : List Nat := [1, 1, 1, 7, 1, 1, 2, 2, 3, 1, 3]
def baseStart_2824931 : Nat := 118140960795 + 2824931 * 2 ^ 59
def prefixEnd_2824931 : Nat := 4983230072969 + 3 ^ 40 * 2824931 * 2
def baseEnd_2824931 : Nat := 1450547418786392178170885

theorem tailTrace_2824931 : CollatzResearch.WordTrace tailWord_2824931 prefixEnd_2824931 1450547418786392178170885 := by
  unfold tailWord_2824931
  simp only [CollatzResearch.WordTrace]
  refine ⟨103033698128764921649322647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68689132085843281099548431 103033698128764921649322647)
  ·
    refine ⟨154550547193147382473983971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103033698128764921649322647 154550547193147382473983971)
    ·
      refine ⟨231825820789721073710975957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154550547193147382473983971 231825820789721073710975957)
      ·
        refine ⟨5433417674759087665100999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 231825820789721073710975957 5433417674759087665100999)
        ·
          refine ⟨8150126512138631497651499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5433417674759087665100999 8150126512138631497651499)
          ·
            refine ⟨12225189768207947246477249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8150126512138631497651499 12225189768207947246477249)
            ·
              refine ⟨9168892326155960434857937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12225189768207947246477249 9168892326155960434857937)
              ·
                refine ⟨6876669244616970326143453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9168892326155960434857937 6876669244616970326143453)
                ·
                  refine ⟨2578750966731363872303795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6876669244616970326143453 2578750966731363872303795)
                  ·
                    refine ⟨3868126450097045808455693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2578750966731363872303795 3868126450097045808455693)
                    ·
                      refine ⟨1450547418786392178170885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3868126450097045808455693 1450547418786392178170885)
                      ·
                        rfl

theorem cell23_2824931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_2824931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824931 prefixEnd_2824931 := by exact prefixLift 2824931
  have htrace : WordTrace (prefixWord ++ tailWord_2824931) baseStart_2824931 baseEnd_2824931 := by
    simpa [prefixWord, tailWord_2824931, baseEnd_2824931] using wordTrace_append hprefix tailTrace_2824931
  have hstable : (prefixWord ++ tailWord_2824931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824931).length < 2 ^ (prefixWord ++ tailWord_2824931).sum := by decide
  have hdescent : baseEnd_2824931 < baseStart_2824931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824937 : List Nat := [1, 2, 1, 1, 1, 2, 4, 3, 3, 1, 4]
def baseStart_2824937 : Nat := 118140960795 + 2824937 * 2 ^ 59
def prefixEnd_2824937 : Nat := 4983230072969 + 3 ^ 40 * 2824937 * 2
def baseEnd_2824937 : Nat := 1450550499670319154695857

theorem tailTrace_2824937 : CollatzResearch.WordTrace tailWord_2824937 prefixEnd_2824937 1450550499670319154695857 := by
  unfold tailWord_2824937
  simp only [CollatzResearch.WordTrace]
  refine ⟨103033916966743184674041065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68689277977828789782694043 103033916966743184674041065)
  ·
    refine ⟨77275437725057388505530799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103033916966743184674041065 77275437725057388505530799)
    ·
      refine ⟨115913156587586082758296199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77275437725057388505530799 115913156587586082758296199)
      ·
        refine ⟨173869734881379124137444299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115913156587586082758296199 173869734881379124137444299)
        ·
          refine ⟨260804602322068686206166449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173869734881379124137444299 260804602322068686206166449)
          ·
            refine ⟨195603451741551514654624837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260804602322068686206166449 195603451741551514654624837)
            ·
              refine ⟨36675647201540908997742157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 195603451741551514654624837 36675647201540908997742157)
              ·
                refine ⟨13753367700577840874153309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36675647201540908997742157 13753367700577840874153309)
                ·
                  refine ⟨5157512887716690327807491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13753367700577840874153309 5157512887716690327807491)
                  ·
                    refine ⟨7736269331575035491711237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5157512887716690327807491 7736269331575035491711237)
                    ·
                      refine ⟨1450550499670319154695857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7736269331575035491711237 1450550499670319154695857)
                      ·
                        rfl

theorem cell23_2824937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 1, 4].length) (baseStart_2824937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824937 prefixEnd_2824937 := by exact prefixLift 2824937
  have htrace : WordTrace (prefixWord ++ tailWord_2824937) baseStart_2824937 baseEnd_2824937 := by
    simpa [prefixWord, tailWord_2824937, baseEnd_2824937] using wordTrace_append hprefix tailTrace_2824937
  have hstable : (prefixWord ++ tailWord_2824937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824937).length < 2 ^ (prefixWord ++ tailWord_2824937).sum := by decide
  have hdescent : baseEnd_2824937 < baseStart_2824937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824941 : List Nat := [1, 5, 1, 2, 1, 1, 2, 3, 2, 3, 2]
def baseStart_2824941 : Nat := 118140960795 + 2824941 * 2 ^ 59
def prefixEnd_2824941 : Nat := 4983230072969 + 3 ^ 40 * 2824941 * 2
def baseEnd_2824941 : Nat := 1450552553592937139045839

theorem tailTrace_2824941 : CollatzResearch.WordTrace tailWord_2824941 prefixEnd_2824941 1450552553592937139045839 := by
  unfold tailWord_2824941
  simp only [CollatzResearch.WordTrace]
  refine ⟨103034062858728693357186677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68689375239152462238124451 103034062858728693357186677)
  ·
    refine ⟨9659443393005815002236251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103034062858728693357186677 9659443393005815002236251)
    ·
      refine ⟨14489165089508722503354377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9659443393005815002236251 14489165089508722503354377)
      ·
        refine ⟨10866873817131541877515783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14489165089508722503354377 10866873817131541877515783)
        ·
          refine ⟨16300310725697312816273675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10866873817131541877515783 16300310725697312816273675)
          ·
            refine ⟨24450466088545969224410513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16300310725697312816273675 24450466088545969224410513)
            ·
              refine ⟨18337849566409476918307885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24450466088545969224410513 18337849566409476918307885)
              ·
                refine ⟨6876693587403553844365457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18337849566409476918307885 6876693587403553844365457)
                ·
                  refine ⟨5157520190552665383274093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6876693587403553844365457 5157520190552665383274093)
                  ·
                    refine ⟨1934070071457249518727785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5157520190552665383274093 1934070071457249518727785)
                    ·
                      refine ⟨1450552553592937139045839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1934070071457249518727785 1450552553592937139045839)
                      ·
                        rfl

theorem cell23_2824941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_2824941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824941 prefixEnd_2824941 := by exact prefixLift 2824941
  have htrace : WordTrace (prefixWord ++ tailWord_2824941) baseStart_2824941 baseEnd_2824941 := by
    simpa [prefixWord, tailWord_2824941, baseEnd_2824941] using wordTrace_append hprefix tailTrace_2824941
  have hstable : (prefixWord ++ tailWord_2824941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824941).length < 2 ^ (prefixWord ++ tailWord_2824941).sum := by decide
  have hdescent : baseEnd_2824941 < baseStart_2824941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824954 : List Nat := [3, 1, 1, 1, 1, 3, 4, 3, 1, 1, 4]
def baseStart_2824954 : Nat := 118140960795 + 2824954 * 2 ^ 59
def prefixEnd_2824954 : Nat := 4983230072969 + 3 ^ 40 * 2824954 * 2
def baseEnd_2824954 : Nat := 1450559228841445588183279

theorem tailTrace_2824954 : CollatzResearch.WordTrace tailWord_2824954 prefixEnd_2824954 1450559228841445588183279 := by
  unfold tailWord_2824954
  simp only [CollatzResearch.WordTrace]
  refine ⟨25758634251920399144352479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68689691338454397718273277 25758634251920399144352479)
  ·
    refine ⟨38637951377880598716528719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25758634251920399144352479 38637951377880598716528719)
    ·
      refine ⟨57956927066820898074793079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38637951377880598716528719 57956927066820898074793079)
      ·
        refine ⟨86935390600231347112189619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57956927066820898074793079 86935390600231347112189619)
        ·
          refine ⟨130403085900347020668284429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86935390600231347112189619 130403085900347020668284429)
          ·
            refine ⟨48901157212630132750606661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130403085900347020668284429 48901157212630132750606661)
            ·
              refine ⟨9168966977368149890738749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48901157212630132750606661 9168966977368149890738749)
              ·
                refine ⟨3438362616513056209027031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9168966977368149890738749 3438362616513056209027031)
                ·
                  refine ⟨5157543924769584313540547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3438362616513056209027031 5157543924769584313540547)
                  ·
                    refine ⟨7736315887154376470310821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5157543924769584313540547 7736315887154376470310821)
                    ·
                      refine ⟨1450559228841445588183279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7736315887154376470310821 1450559228841445588183279)
                      ·
                        rfl

theorem cell23_2824954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 1, 1, 4].length) (baseStart_2824954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824954 prefixEnd_2824954 := by exact prefixLift 2824954
  have htrace : WordTrace (prefixWord ++ tailWord_2824954) baseStart_2824954 baseEnd_2824954 := by
    simpa [prefixWord, tailWord_2824954, baseEnd_2824954] using wordTrace_append hprefix tailTrace_2824954
  have hstable : (prefixWord ++ tailWord_2824954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824954).length < 2 ^ (prefixWord ++ tailWord_2824954).sum := by decide
  have hdescent : baseEnd_2824954 < baseStart_2824954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824958 : List Nat := [4, 2, 2, 1, 2, 2, 1, 2, 2, 3, 2]
def baseStart_2824958 : Nat := 118140960795 + 2824958 * 2 ^ 59
def prefixEnd_2824958 : Nat := 4983230072969 + 3 ^ 40 * 2824958 * 2
def baseEnd_2824958 : Nat := 1450561282764063572533261

theorem tailTrace_2824958 : CollatzResearch.WordTrace tailWord_2824958 prefixEnd_2824958 1450561282764063572533261 := by
  unfold tailWord_2824958
  simp only [CollatzResearch.WordTrace]
  refine ⟨12879335362458388157569441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68689788599778070173703685 12879335362458388157569441)
  ·
    refine ⟨9659501521843791118177081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12879335362458388157569441 9659501521843791118177081)
    ·
      refine ⟨7244626141382843338632811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9659501521843791118177081 7244626141382843338632811)
      ·
        refine ⟨10866939212074265007949217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7244626141382843338632811 10866939212074265007949217)
        ·
          refine ⟨8150204409055698755961913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10866939212074265007949217 8150204409055698755961913)
          ·
            refine ⟨6112653306791774066971435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8150204409055698755961913 6112653306791774066971435)
            ·
              refine ⟨9168979960187661100457153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6112653306791774066971435 9168979960187661100457153)
              ·
                refine ⟨6876734970140745825342865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9168979960187661100457153 6876734970140745825342865)
                ·
                  refine ⟨5157551227605559369007149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6876734970140745825342865 5157551227605559369007149)
                  ·
                    refine ⟨1934081710352084763377681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5157551227605559369007149 1934081710352084763377681)
                    ·
                      refine ⟨1450561282764063572533261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1934081710352084763377681 1450561282764063572533261)
                      ·
                        rfl

theorem cell23_2824958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_2824958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824958 prefixEnd_2824958 := by exact prefixLift 2824958
  have htrace : WordTrace (prefixWord ++ tailWord_2824958) baseStart_2824958 baseEnd_2824958 := by
    simpa [prefixWord, tailWord_2824958, baseEnd_2824958] using wordTrace_append hprefix tailTrace_2824958
  have hstable : (prefixWord ++ tailWord_2824958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824958).length < 2 ^ (prefixWord ++ tailWord_2824958).sum := by decide
  have hdescent : baseEnd_2824958 < baseStart_2824958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824964 : List Nat := [2, 3, 2, 2, 1, 1, 1, 3, 4, 4]
def baseStart_2824964 : Nat := 118140960795 + 2824964 * 2 ^ 59
def prefixEnd_2824964 : Nat := 4983230072969 + 3 ^ 40 * 2824964 * 2
def baseEnd_2824964 : Nat := 483521454549330183019411

theorem tailTrace_2824964 : CollatzResearch.WordTrace tailWord_2824964 prefixEnd_2824964 483521454549330183019411 := by
  unfold tailWord_2824964
  simp only [CollatzResearch.WordTrace]
  refine ⟨51517450868822684142636973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68689934491763578856849297 51517450868822684142636973)
  ·
    refine ⟨19319044075808506553488865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51517450868822684142636973 19319044075808506553488865)
    ·
      refine ⟨14489283056856379915116649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19319044075808506553488865 14489283056856379915116649)
      ·
        refine ⟨10866962292642284936337487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14489283056856379915116649 10866962292642284936337487)
        ·
          refine ⟨16300443438963427404506231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10866962292642284936337487 16300443438963427404506231)
          ·
            refine ⟨24450665158445141106759347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16300443438963427404506231 24450665158445141106759347)
            ·
              refine ⟨36675997737667711660139021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24450665158445141106759347 36675997737667711660139021)
              ·
                refine ⟨13753499151625391872552133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36675997737667711660139021 13753499151625391872552133)
                ·
                  refine ⟨2578781090929760976103525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13753499151625391872552133 2578781090929760976103525)
                  ·
                    refine ⟨483521454549330183019411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2578781090929760976103525 483521454549330183019411)
                    ·
                      rfl

theorem cell23_2824964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_2824964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824964 prefixEnd_2824964 := by exact prefixLift 2824964
  have htrace : WordTrace (prefixWord ++ tailWord_2824964) baseStart_2824964 baseEnd_2824964 := by
    simpa [prefixWord, tailWord_2824964, baseEnd_2824964] using wordTrace_append hprefix tailTrace_2824964
  have hstable : (prefixWord ++ tailWord_2824964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824964).length < 2 ^ (prefixWord ++ tailWord_2824964).sum := by decide
  have hdescent : baseEnd_2824964 < baseStart_2824964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824974 : List Nat := [4, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3]
def baseStart_2824974 : Nat := 118140960795 + 2824974 * 2 ^ 59
def prefixEnd_2824974 : Nat := 4983230072969 + 3 ^ 40 * 2824974 * 2
def baseEnd_2824974 : Nat := 1450569498454535509933187

theorem tailTrace_2824974 : CollatzResearch.WordTrace tailWord_2824974 prefixEnd_2824974 1450569498454535509933187 := by
  unfold tailWord_2824974
  simp only [CollatzResearch.WordTrace]
  refine ⟨12879408308451142499142247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68690177645072759995425317 12879408308451142499142247)
  ·
    refine ⟨19319112462676713748713371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12879408308451142499142247 19319112462676713748713371)
    ·
      refine ⟨28978668694015070623070057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19319112462676713748713371 28978668694015070623070057)
      ·
        refine ⟨21734001520511302967302543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28978668694015070623070057 21734001520511302967302543)
        ·
          refine ⟨32601002280766954450953815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21734001520511302967302543 32601002280766954450953815)
          ·
            refine ⟨48901503421150431676430723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32601002280766954450953815 48901503421150431676430723)
            ·
              refine ⟨73352255131725647514646085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48901503421150431676430723 73352255131725647514646085)
              ·
                refine ⟨13753547837198558908996141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73352255131725647514646085 13753547837198558908996141)
                ·
                  refine ⟨5157580438949459590873553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13753547837198558908996141 5157580438949459590873553)
                  ·
                    refine ⟨3868185329212094693155165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5157580438949459590873553 3868185329212094693155165)
                    ·
                      refine ⟨1450569498454535509933187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3868185329212094693155165 1450569498454535509933187)
                      ·
                        rfl

theorem cell23_2824974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_2824974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824974 prefixEnd_2824974 := by exact prefixLift 2824974
  have htrace : WordTrace (prefixWord ++ tailWord_2824974) baseStart_2824974 baseEnd_2824974 := by
    simpa [prefixWord, tailWord_2824974, baseEnd_2824974] using wordTrace_append hprefix tailTrace_2824974
  have hstable : (prefixWord ++ tailWord_2824974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824974).length < 2 ^ (prefixWord ++ tailWord_2824974).sum := by decide
  have hdescent : baseEnd_2824974 < baseStart_2824974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2824991 : List Nat := [1, 1, 2, 4, 2, 2, 3, 2, 1, 2, 3]
def baseStart_2824991 : Nat := 118140960795 + 2824991 * 2 ^ 59
def prefixEnd_2824991 : Nat := 4983230072969 + 3 ^ 40 * 2824991 * 2
def baseEnd_2824991 : Nat := 1450578227625661943420609

theorem tailTrace_2824991 : CollatzResearch.WordTrace tailWord_2824991 prefixEnd_2824991 1450578227625661943420609 := by
  unfold tailWord_2824991
  simp only [CollatzResearch.WordTrace]
  refine ⟨103035886508547551896506827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68690591005698367931004551 103035886508547551896506827)
  ·
    refine ⟨154553829762821327844760241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103035886508547551896506827 154553829762821327844760241)
    ·
      refine ⟨115915372322115995883570181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154553829762821327844760241 115915372322115995883570181)
      ·
        refine ⟨21734132310396749228169409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115915372322115995883570181 21734132310396749228169409)
        ·
          refine ⟨16300599232797561921127057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21734132310396749228169409 16300599232797561921127057)
          ·
            refine ⟨12225449424598171440845293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16300599232797561921127057 12225449424598171440845293)
            ·
              refine ⟨4584543534224314290316985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12225449424598171440845293 4584543534224314290316985)
              ·
                refine ⟨3438407650668235717737739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4584543534224314290316985 3438407650668235717737739)
                ·
                  refine ⟨5157611476002353576606609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3438407650668235717737739 5157611476002353576606609)
                  ·
                    refine ⟨3868208607001765182454957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5157611476002353576606609 3868208607001765182454957)
                    ·
                      refine ⟨1450578227625661943420609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3868208607001765182454957 1450578227625661943420609)
                      ·
                        rfl

theorem cell23_2824991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_2824991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2824991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2824991 prefixEnd_2824991 := by exact prefixLift 2824991
  have htrace : WordTrace (prefixWord ++ tailWord_2824991) baseStart_2824991 baseEnd_2824991 := by
    simpa [prefixWord, tailWord_2824991, baseEnd_2824991] using wordTrace_append hprefix tailTrace_2824991
  have hstable : (prefixWord ++ tailWord_2824991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2824991).length < 2 ^ (prefixWord ++ tailWord_2824991).sum := by decide
  have hdescent : baseEnd_2824991 < baseStart_2824991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2824991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825004 : List Nat := [2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 3]
def baseStart_2825004 : Nat := 118140960795 + 2825004 * 2 ^ 59
def prefixEnd_2825004 : Nat := 4983230072969 + 3 ^ 40 * 2825004 * 2
def baseEnd_2825004 : Nat := 1450584902874170392558049

theorem tailTrace_2825004 : CollatzResearch.WordTrace tailWord_2825004 prefixEnd_2825004 1450584902874170392558049 := by
  unfold tailWord_2825004
  simp only [CollatzResearch.WordTrace]
  refine ⟨51518180328750227558365033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68690907105000303411153377 51518180328750227558365033)
  ·
    refine ⟨38638635246562670668773775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51518180328750227558365033 38638635246562670668773775)
    ·
      refine ⟨57957952869844006003160663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38638635246562670668773775 57957952869844006003160663)
      ·
        refine ⟨86936929304766009004740995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57957952869844006003160663 86936929304766009004740995)
        ·
          refine ⟨130405393957149013507111493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86936929304766009004740995 130405393957149013507111493)
          ·
            refine ⟨24451011366965440032583405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130405393957149013507111493 24451011366965440032583405)
            ·
              refine ⟨9169129262612040012218777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24451011366965440032583405 9169129262612040012218777)
              ·
                refine ⟨6876846946959030009164083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9169129262612040012218777 6876846946959030009164083)
                ·
                  refine ⟨10315270420438545013746125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6876846946959030009164083 10315270420438545013746125)
                  ·
                    refine ⟨3868226407664454380154797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10315270420438545013746125 3868226407664454380154797)
                    ·
                      refine ⟨1450584902874170392558049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3868226407664454380154797 1450584902874170392558049)
                      ·
                        rfl

theorem cell23_2825004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 3].length) (baseStart_2825004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825004 prefixEnd_2825004 := by exact prefixLift 2825004
  have htrace : WordTrace (prefixWord ++ tailWord_2825004) baseStart_2825004 baseEnd_2825004 := by
    simpa [prefixWord, tailWord_2825004, baseEnd_2825004] using wordTrace_append hprefix tailTrace_2825004
  have hstable : (prefixWord ++ tailWord_2825004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825004).length < 2 ^ (prefixWord ++ tailWord_2825004).sum := by decide
  have hdescent : baseEnd_2825004 < baseStart_2825004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825022 : List Nat := [4, 2, 1, 2, 3, 1, 1, 4, 1, 2, 2]
def baseStart_2825022 : Nat := 118140960795 + 2825022 * 2 ^ 59
def prefixEnd_2825022 : Nat := 4983230072969 + 3 ^ 40 * 2825022 * 2
def baseEnd_2825022 : Nat := 1450594145525951322132967

theorem tailTrace_2825022 : CollatzResearch.WordTrace tailWord_2825022 prefixEnd_2825022 1450594145525951322132967 := by
  unfold tailWord_2825022
  simp only [CollatzResearch.WordTrace]
  refine ⟨12879627146429405523860665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68691344780956829460590213 12879627146429405523860665)
  ·
    refine ⟨9659720359822054142895499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12879627146429405523860665 9659720359822054142895499)
    ·
      refine ⟨14489580539733081214343249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9659720359822054142895499 14489580539733081214343249)
      ·
        refine ⟨10867185404799810910757437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14489580539733081214343249 10867185404799810910757437)
        ·
          refine ⟨4075194526799929091534039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10867185404799810910757437 4075194526799929091534039)
          ·
            refine ⟨6112791790199893637301059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4075194526799929091534039 6112791790199893637301059)
            ·
              refine ⟨9169187685299840455951589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6112791790199893637301059 9169187685299840455951589)
              ·
                refine ⟨1719222690993720085490923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9169187685299840455951589 1719222690993720085490923)
                ·
                  refine ⟨2578834036490580128236385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1719222690993720085490923 2578834036490580128236385)
                  ·
                    refine ⟨1934125527367935096177289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2578834036490580128236385 1934125527367935096177289)
                    ·
                      refine ⟨1450594145525951322132967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1934125527367935096177289 1450594145525951322132967)
                      ·
                        rfl

theorem cell23_2825022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_2825022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825022 prefixEnd_2825022 := by exact prefixLift 2825022
  have htrace : WordTrace (prefixWord ++ tailWord_2825022) baseStart_2825022 baseEnd_2825022 := by
    simpa [prefixWord, tailWord_2825022, baseEnd_2825022] using wordTrace_append hprefix tailTrace_2825022
  have hstable : (prefixWord ++ tailWord_2825022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825022).length < 2 ^ (prefixWord ++ tailWord_2825022).sum := by decide
  have hdescent : baseEnd_2825022 < baseStart_2825022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825027 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 4]
def baseStart_2825027 : Nat := 118140960795 + 2825027 * 2 ^ 59
def prefixEnd_2825027 : Nat := 4983230072969 + 3 ^ 40 * 2825027 * 2
def baseEnd_2825027 : Nat := 1450596712929223802570443

theorem tailTrace_2825027 : CollatzResearch.WordTrace tailWord_2825027 prefixEnd_2825027 1450596712929223802570443 := by
  unfold tailWord_2825027
  simp only [CollatzResearch.WordTrace]
  refine ⟨103037199536417130044817335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68691466357611420029878223 103037199536417130044817335)
  ·
    refine ⟨154555799304625695067226003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103037199536417130044817335 154555799304625695067226003)
    ·
      refine ⟨231833698956938542600839005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154555799304625695067226003 231833698956938542600839005)
      ·
        refine ⟨86937637108851953475314627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231833698956938542600839005 86937637108851953475314627)
        ·
          refine ⟨130406455663277930212971941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86937637108851953475314627 130406455663277930212971941)
          ·
            refine ⟨24451210436864611914932239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130406455663277930212971941 24451210436864611914932239)
            ·
              refine ⟨36676815655296917872398359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24451210436864611914932239 36676815655296917872398359)
              ·
                refine ⟨55015223482945376808597539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36676815655296917872398359 55015223482945376808597539)
                ·
                  refine ⟨82522835224418065212896309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55015223482945376808597539 82522835224418065212896309)
                  ·
                    refine ⟨7736515802289193613709029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82522835224418065212896309 7736515802289193613709029)
                    ·
                      refine ⟨1450596712929223802570443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7736515802289193613709029 1450596712929223802570443)
                      ·
                        rfl

theorem cell23_2825027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_2825027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825027 prefixEnd_2825027 := by exact prefixLift 2825027
  have htrace : WordTrace (prefixWord ++ tailWord_2825027) baseStart_2825027 baseEnd_2825027 := by
    simpa [prefixWord, tailWord_2825027, baseEnd_2825027] using wordTrace_append hprefix tailTrace_2825027
  have hstable : (prefixWord ++ tailWord_2825027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825027).length < 2 ^ (prefixWord ++ tailWord_2825027).sum := by decide
  have hdescent : baseEnd_2825027 < baseStart_2825027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825028 : List Nat := [2, 3, 4, 2, 1, 2, 1, 8]
def baseStart_2825028 : Nat := 118140960795 + 2825028 * 2 ^ 59
def prefixEnd_2825028 : Nat := 4983230072969 + 3 ^ 40 * 2825028 * 2
def baseEnd_2825028 : Nat := 53725823200365862913257

theorem tailTrace_2825028 : CollatzResearch.WordTrace tailWord_2825028 prefixEnd_2825028 53725823200365862913257 := by
  unfold tailWord_2825028
  simp only [CollatzResearch.WordTrace]
  refine ⟨51518618004706753607801869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68691490672942338143735825 51518618004706753607801869)
  ·
    refine ⟨19319481751765032602925701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51518618004706753607801869 19319481751765032602925701)
    ·
      refine ⟨3622402828455943613048569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19319481751765032602925701 3622402828455943613048569)
      ·
        refine ⟨2716802121341957709786427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3622402828455943613048569 2716802121341957709786427)
        ·
          refine ⟨4075203182012936564679641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2716802121341957709786427 4075203182012936564679641)
          ·
            refine ⟨3056402386509702423509731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4075203182012936564679641 3056402386509702423509731)
            ·
              refine ⟨4584603579764553635264597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3056402386509702423509731 4584603579764553635264597)
              ·
                refine ⟨53725823200365862913257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4584603579764553635264597 53725823200365862913257)
                ·
                  rfl

theorem cell23_2825028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 8].length) (baseStart_2825028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825028 prefixEnd_2825028 := by exact prefixLift 2825028
  have htrace : WordTrace (prefixWord ++ tailWord_2825028) baseStart_2825028 baseEnd_2825028 := by
    simpa [prefixWord, tailWord_2825028, baseEnd_2825028] using wordTrace_append hprefix tailTrace_2825028
  have hstable : (prefixWord ++ tailWord_2825028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825028).length < 2 ^ (prefixWord ++ tailWord_2825028).sum := by decide
  have hdescent : baseEnd_2825028 < baseStart_2825028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825061 : List Nat := [1, 3, 1, 3, 1, 1, 4, 2, 1, 4, 2]
def baseStart_2825061 : Nat := 118140960795 + 2825061 * 2 ^ 59
def prefixEnd_2825061 : Nat := 4983230072969 + 3 ^ 40 * 2825061 * 2
def baseEnd_2825061 : Nat := 1450614171271476669545287

theorem tailTrace_2825061 : CollatzResearch.WordTrace tailWord_2825061 prefixEnd_2825061 1450614171271476669545287 := by
  unfold tailWord_2825061
  simp only [CollatzResearch.WordTrace]
  refine ⟨103038439618293953851555037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68692293078862635901036691 103038439618293953851555037)
  ·
    refine ⟨38639414856860232694333139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103038439618293953851555037 38639414856860232694333139)
    ·
      refine ⟨57959122285290349041499709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38639414856860232694333139 57959122285290349041499709)
      ·
        refine ⟨21734670856983880890562391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57959122285290349041499709 21734670856983880890562391)
        ·
          refine ⟨32602006285475821335843587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21734670856983880890562391 32602006285475821335843587)
          ·
            refine ⟨48903009428213732003765381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32602006285475821335843587 48903009428213732003765381)
            ·
              refine ⟨9169314267790074750706009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48903009428213732003765381 9169314267790074750706009)
              ·
                refine ⟨6876985700842556063029507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9169314267790074750706009 6876985700842556063029507)
                ·
                  refine ⟨10315478551263834094544261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6876985700842556063029507 10315478551263834094544261)
                  ·
                    refine ⟨1934152228361968892727049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10315478551263834094544261 1934152228361968892727049)
                    ·
                      refine ⟨1450614171271476669545287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1934152228361968892727049 1450614171271476669545287)
                      ·
                        rfl

theorem cell23_2825061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_2825061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825061 prefixEnd_2825061 := by exact prefixLift 2825061
  have htrace : WordTrace (prefixWord ++ tailWord_2825061) baseStart_2825061 baseEnd_2825061 := by
    simpa [prefixWord, tailWord_2825061, baseEnd_2825061] using wordTrace_append hprefix tailTrace_2825061
  have hstable : (prefixWord ++ tailWord_2825061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825061).length < 2 ^ (prefixWord ++ tailWord_2825061).sum := by decide
  have hdescent : baseEnd_2825061 < baseStart_2825061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825074 : List Nat := [3, 2, 1, 2, 1, 1, 3, 2, 2, 2, 4]
def baseStart_2825074 : Nat := 118140960795 + 2825074 * 2 ^ 59
def prefixEnd_2825074 : Nat := 4983230072969 + 3 ^ 40 * 2825074 * 2
def baseEnd_2825074 : Nat := 1450620846519985118682727

theorem tailTrace_2825074 : CollatzResearch.WordTrace tailWord_2825074 prefixEnd_2825074 1450620846519985118682727 := by
  unfold tailWord_2825074
  simp only [CollatzResearch.WordTrace]
  refine ⟨25759728441811714267944569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68692609178164571381185517 25759728441811714267944569)
  ·
    refine ⟨19319796331358785700958427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25759728441811714267944569 19319796331358785700958427)
    ·
      refine ⟨28979694497038178551437641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19319796331358785700958427 28979694497038178551437641)
      ·
        refine ⟨21734770872778633913578231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28979694497038178551437641 21734770872778633913578231)
        ·
          refine ⟨32602156309167950870367347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21734770872778633913578231 32602156309167950870367347)
          ·
            refine ⟨48903234463751926305551021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32602156309167950870367347 48903234463751926305551021)
            ·
              refine ⟨18338712923906972364581633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48903234463751926305551021 18338712923906972364581633)
              ·
                refine ⟨13754034692930229273436225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18338712923906972364581633 13754034692930229273436225)
                ·
                  refine ⟨10315526019697671955077169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13754034692930229273436225 10315526019697671955077169)
                  ·
                    refine ⟨7736644514773253966307877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10315526019697671955077169 7736644514773253966307877)
                    ·
                      refine ⟨1450620846519985118682727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7736644514773253966307877 1450620846519985118682727)
                      ·
                        rfl

theorem cell23_2825074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_2825074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825074 prefixEnd_2825074 := by exact prefixLift 2825074
  have htrace : WordTrace (prefixWord ++ tailWord_2825074) baseStart_2825074 baseEnd_2825074 := by
    simpa [prefixWord, tailWord_2825074, baseEnd_2825074] using wordTrace_append hprefix tailTrace_2825074
  have hstable : (prefixWord ++ tailWord_2825074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825074).length < 2 ^ (prefixWord ++ tailWord_2825074).sum := by decide
  have hdescent : baseEnd_2825074 < baseStart_2825074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825107 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 7]
def baseStart_2825107 : Nat := 118140960795 + 2825107 * 2 ^ 59
def prefixEnd_2825107 : Nat := 4983230072969 + 3 ^ 40 * 2825107 * 2
def baseEnd_2825107 : Nat := 1450637791381583489570075

theorem tailTrace_2825107 : CollatzResearch.WordTrace tailWord_2825107 prefixEnd_2825107 1450637791381583489570075 := by
  unfold tailWord_2825107
  simp only [CollatzResearch.WordTrace]
  refine ⟨103040117376127303707729575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68693411584084869138486383 103040117376127303707729575)
  ·
    refine ⟨154560176064190955561594363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103040117376127303707729575 154560176064190955561594363)
    ·
      refine ⟨231840264096286433342391545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154560176064190955561594363 231840264096286433342391545)
      ·
        refine ⟨173880198072214825006793659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231840264096286433342391545 173880198072214825006793659)
        ·
          refine ⟨260820297108322237510190489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173880198072214825006793659 260820297108322237510190489)
          ·
            refine ⟨195615222831241678132642867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260820297108322237510190489 195615222831241678132642867)
            ·
              refine ⟨293422834246862517198964301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195615222831241678132642867 293422834246862517198964301)
              ·
                refine ⟨110033562842573443949611613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 293422834246862517198964301 110033562842573443949611613)
                ·
                  refine ⟨41262586065965041481104355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110033562842573443949611613 41262586065965041481104355)
                  ·
                    refine ⟨61893879098947562221656533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41262586065965041481104355 61893879098947562221656533)
                    ·
                      refine ⟨1450637791381583489570075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 61893879098947562221656533 1450637791381583489570075)
                      ·
                        rfl

theorem cell23_2825107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 7].length) (baseStart_2825107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825107 prefixEnd_2825107 := by exact prefixLift 2825107
  have htrace : WordTrace (prefixWord ++ tailWord_2825107) baseStart_2825107 baseEnd_2825107 := by
    simpa [prefixWord, tailWord_2825107, baseEnd_2825107] using wordTrace_append hprefix tailTrace_2825107
  have hstable : (prefixWord ++ tailWord_2825107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825107).length < 2 ^ (prefixWord ++ tailWord_2825107).sum := by decide
  have hdescent : baseEnd_2825107 < baseStart_2825107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825124 : List Nat := [2, 3, 1, 2, 1, 2, 2, 2, 1, 2, 5]
def baseStart_2825124 : Nat := 118140960795 + 2825124 * 2 ^ 59
def prefixEnd_2825124 : Nat := 4983230072969 + 3 ^ 40 * 2825124 * 2
def baseEnd_2825124 : Nat := 1450646520552709923057497

theorem tailTrace_2825124 : CollatzResearch.WordTrace tailWord_2825124 prefixEnd_2825124 1450646520552709923057497 := by
  unfold tailWord_2825124
  simp only [CollatzResearch.WordTrace]
  refine ⟨51520368708532857805549213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68693824944710477074065617 51520368708532857805549213)
  ·
    refine ⟨19320138265699821677080955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51520368708532857805549213 19320138265699821677080955)
    ·
      refine ⟨28980207398549732515621433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19320138265699821677080955 28980207398549732515621433)
      ·
        refine ⟨21735155548912299386716075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28980207398549732515621433 21735155548912299386716075)
        ·
          refine ⟨32602733323368449080074113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21735155548912299386716075 32602733323368449080074113)
          ·
            refine ⟨24452049992526336810055585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32602733323368449080074113 24452049992526336810055585)
            ·
              refine ⟨18339037494394752607541689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24452049992526336810055585 18339037494394752607541689)
              ·
                refine ⟨13754278120796064455656267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18339037494394752607541689 13754278120796064455656267)
                ·
                  refine ⟨20631417181194096683484401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13754278120796064455656267 20631417181194096683484401)
                  ·
                    refine ⟨15473562885895572512613301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20631417181194096683484401 15473562885895572512613301)
                    ·
                      refine ⟨1450646520552709923057497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15473562885895572512613301 1450646520552709923057497)
                      ·
                        rfl

theorem cell23_2825124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_2825124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825124 prefixEnd_2825124 := by exact prefixLift 2825124
  have htrace : WordTrace (prefixWord ++ tailWord_2825124) baseStart_2825124 baseEnd_2825124 := by
    simpa [prefixWord, tailWord_2825124, baseEnd_2825124] using wordTrace_append hprefix tailTrace_2825124
  have hstable : (prefixWord ++ tailWord_2825124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825124).length < 2 ^ (prefixWord ++ tailWord_2825124).sum := by decide
  have hdescent : baseEnd_2825124 < baseStart_2825124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825191 : List Nat := [1, 1, 5, 2, 2, 1, 1, 4, 6]
def baseStart_2825191 : Nat := 118140960795 + 2825191 * 2 ^ 59
def prefixEnd_2825191 : Nat := 4983230072969 + 3 ^ 40 * 2825191 * 2
def baseEnd_2825191 : Nat := 161186769306284573435521

theorem tailTrace_2825191 : CollatzResearch.WordTrace tailWord_2825191 prefixEnd_2825191 161186769306284573435521 := by
  unfold tailWord_2825191
  simp only [CollatzResearch.WordTrace]
  refine ⟨103043181107822986053787427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68695454071881990702524951 103043181107822986053787427)
  ·
    refine ⟨154564771661734479080681141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103043181107822986053787427 154564771661734479080681141)
    ·
      refine ⟨14490447343287607413813857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 154564771661734479080681141 14490447343287607413813857)
      ·
        refine ⟨10867835507465705560360393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14490447343287607413813857 10867835507465705560360393)
        ·
          refine ⟨8150876630599279170270295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10867835507465705560360393 8150876630599279170270295)
          ·
            refine ⟨12226314945898918755405443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8150876630599279170270295 12226314945898918755405443)
            ·
              refine ⟨18339472418848378133108165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12226314945898918755405443 18339472418848378133108165)
              ·
                refine ⟨3438651078534070899957781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18339472418848378133108165 3438651078534070899957781)
                ·
                  refine ⟨161186769306284573435521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3438651078534070899957781 161186769306284573435521)
                  ·
                    rfl

theorem cell23_2825191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 6].length) (baseStart_2825191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825191 prefixEnd_2825191 := by exact prefixLift 2825191
  have htrace : WordTrace (prefixWord ++ tailWord_2825191) baseStart_2825191 baseEnd_2825191 := by
    simpa [prefixWord, tailWord_2825191, baseEnd_2825191] using wordTrace_append hprefix tailTrace_2825191
  have hstable : (prefixWord ++ tailWord_2825191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825191).length < 2 ^ (prefixWord ++ tailWord_2825191).sum := by decide
  have hdescent : baseEnd_2825191 < baseStart_2825191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825211 : List Nat := [1, 1, 1, 1, 1, 3, 3, 4, 1, 5, 2]
def baseStart_2825211 : Nat := 118140960795 + 2825211 * 2 ^ 59
def prefixEnd_2825211 : Nat := 4983230072969 + 3 ^ 40 * 2825211 * 2
def baseEnd_2825211 : Nat := 1450691193369651082669597

theorem tailTrace_2825211 : CollatzResearch.WordTrace tailWord_2825211 prefixEnd_2825211 1450691193369651082669597 := by
  unfold tailWord_2825211
  simp only [CollatzResearch.WordTrace]
  refine ⟨103043910567750529469515487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68695940378500352979676991 103043910567750529469515487)
  ·
    refine ⟨154565865851625794204273231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103043910567750529469515487 154565865851625794204273231)
    ·
      refine ⟨231848798777438691306409847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154565865851625794204273231 231848798777438691306409847)
      ·
        refine ⟨347773198166158036959614771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231848798777438691306409847 347773198166158036959614771)
        ·
          refine ⟨521659797249237055439422157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347773198166158036959614771 521659797249237055439422157)
          ·
            refine ⟨195622423968463895789783309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 521659797249237055439422157 195622423968463895789783309)
            ·
              refine ⟨73358408988173960921168741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 195622423968463895789783309 73358408988173960921168741)
              ·
                refine ⟨13754701685282617672719139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73358408988173960921168741 13754701685282617672719139)
                ·
                  refine ⟨20632052527923926509078709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13754701685282617672719139 20632052527923926509078709)
                  ·
                    refine ⟨1934254924492868110226129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20632052527923926509078709 1934254924492868110226129)
                    ·
                      refine ⟨1450691193369651082669597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1934254924492868110226129 1450691193369651082669597)
                      ·
                        rfl

theorem cell23_2825211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 5, 2].length) (baseStart_2825211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825211 prefixEnd_2825211 := by exact prefixLift 2825211
  have htrace : WordTrace (prefixWord ++ tailWord_2825211) baseStart_2825211 baseEnd_2825211 := by
    simpa [prefixWord, tailWord_2825211, baseEnd_2825211] using wordTrace_append hprefix tailTrace_2825211
  have hstable : (prefixWord ++ tailWord_2825211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825211).length < 2 ^ (prefixWord ++ tailWord_2825211).sum := by decide
  have hdescent : baseEnd_2825211 < baseStart_2825211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825221 : List Nat := [1, 3, 1, 1, 2, 3, 2, 4, 1, 5]
def baseStart_2825221 : Nat := 118140960795 + 2825221 * 2 ^ 59
def prefixEnd_2825221 : Nat := 4983230072969 + 3 ^ 40 * 2825221 * 2
def baseEnd_2825221 : Nat := 483565442725398681181517

theorem tailTrace_2825221 : CollatzResearch.WordTrace tailWord_2825221 prefixEnd_2825221 483565442725398681181517 := by
  unfold tailWord_2825221
  simp only [CollatzResearch.WordTrace]
  refine ⟨103044275297714301177379517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68696183531809534118253011 103044275297714301177379517)
  ·
    refine ⟨38641603236642862941517319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103044275297714301177379517 38641603236642862941517319)
    ·
      refine ⟨57962404854964294412275979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38641603236642862941517319 57962404854964294412275979)
      ·
        refine ⟨86943607282446441618413969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57962404854964294412275979 86943607282446441618413969)
        ·
          refine ⟨65207705461834831213810477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86943607282446441618413969 65207705461834831213810477)
          ·
            refine ⟨24452889548188061705178929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65207705461834831213810477 24452889548188061705178929)
            ·
              refine ⟨18339667161141046278884197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24452889548188061705178929 18339667161141046278884197)
              ·
                refine ⟨3438687592713946177290787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18339667161141046278884197 3438687592713946177290787)
                ·
                  refine ⟨5158031389070919265936181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3438687592713946177290787 5158031389070919265936181)
                  ·
                    refine ⟨483565442725398681181517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5158031389070919265936181 483565442725398681181517)
                    ·
                      rfl

theorem cell23_2825221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 5].length) (baseStart_2825221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825221 prefixEnd_2825221 := by exact prefixLift 2825221
  have htrace : WordTrace (prefixWord ++ tailWord_2825221) baseStart_2825221 baseEnd_2825221 := by
    simpa [prefixWord, tailWord_2825221, baseEnd_2825221] using wordTrace_append hprefix tailTrace_2825221
  have hstable : (prefixWord ++ tailWord_2825221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825221).length < 2 ^ (prefixWord ++ tailWord_2825221).sum := by decide
  have hdescent : baseEnd_2825221 < baseStart_2825221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825228 : List Nat := [2, 2, 1, 2, 3, 3, 1, 1, 1, 5, 2]
def baseStart_2825228 : Nat := 118140960795 + 2825228 * 2 ^ 59
def prefixEnd_2825228 : Nat := 4983230072969 + 3 ^ 40 * 2825228 * 2
def baseEnd_2825228 : Nat := 1450699922540777516157019

theorem tailTrace_2825228 : CollatzResearch.WordTrace tailWord_2825228 prefixEnd_2825228 1450699922540777516157019 := by
  unfold tailWord_2825228
  simp only [CollatzResearch.WordTrace]
  refine ⟨51522265304344470686442169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68696353739125960915256225 51522265304344470686442169)
  ·
    refine ⟨38641698978258353014831627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51522265304344470686442169 38641698978258353014831627)
    ·
      refine ⟨57962548467387529522247441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38641698978258353014831627 57962548467387529522247441)
      ·
        refine ⟨43471911350540647141685581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57962548467387529522247441 43471911350540647141685581)
        ·
          refine ⟨16301966756452742678132093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43471911350540647141685581 16301966756452742678132093)
          ·
            refine ⟨6113237533669778504299535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16301966756452742678132093 6113237533669778504299535)
            ·
              refine ⟨9169856300504667756449303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6113237533669778504299535 9169856300504667756449303)
              ·
                refine ⟨13754784450757001634673955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9169856300504667756449303 13754784450757001634673955)
                ·
                  refine ⟨20632176676135502452010933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13754784450757001634673955 20632176676135502452010933)
                  ·
                    refine ⟨1934266563387703354876025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20632176676135502452010933 1934266563387703354876025)
                    ·
                      refine ⟨1450699922540777516157019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1934266563387703354876025 1450699922540777516157019)
                      ·
                        rfl

theorem cell23_2825228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 1, 5, 2].length) (baseStart_2825228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825228 prefixEnd_2825228 := by exact prefixLift 2825228
  have htrace : WordTrace (prefixWord ++ tailWord_2825228) baseStart_2825228 baseEnd_2825228 := by
    simpa [prefixWord, tailWord_2825228, baseEnd_2825228] using wordTrace_append hprefix tailTrace_2825228
  have hstable : (prefixWord ++ tailWord_2825228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825228).length < 2 ^ (prefixWord ++ tailWord_2825228).sum := by decide
  have hdescent : baseEnd_2825228 < baseStart_2825228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825252 : List Nat := [2, 3, 1, 4, 1, 1, 2, 4, 1, 1, 3]
def baseStart_2825252 : Nat := 118140960795 + 2825252 * 2 ^ 59
def prefixEnd_2825252 : Nat := 4983230072969 + 3 ^ 40 * 2825252 * 2
def baseEnd_2825252 : Nat := 1450712246076485422256909

theorem tailTrace_2825252 : CollatzResearch.WordTrace tailWord_2825252 prefixEnd_2825252 1450712246076485422256909 := by
  unfold tailWord_2825252
  simp only [CollatzResearch.WordTrace]
  refine ⟨51522702980300996735879005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68696937307067995647838673 51522702980300996735879005)
  ·
    refine ⟨19321013617612873775954627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51522702980300996735879005 19321013617612873775954627)
    ·
      refine ⟨28981520426419310663931941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19321013617612873775954627 28981520426419310663931941)
      ·
        refine ⟨5434035079953620749487239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28981520426419310663931941 5434035079953620749487239)
        ·
          refine ⟨8151052619930431124230859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5434035079953620749487239 8151052619930431124230859)
          ·
            refine ⟨12226578929895646686346289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8151052619930431124230859 12226578929895646686346289)
            ·
              refine ⟨9169934197421735014759717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12226578929895646686346289 9169934197421735014759717)
              ·
                refine ⟨1719362662016575315267447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9169934197421735014759717 1719362662016575315267447)
                ·
                  refine ⟨2579043993024862972901171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1719362662016575315267447 2579043993024862972901171)
                  ·
                    refine ⟨3868565989537294459351757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2579043993024862972901171 3868565989537294459351757)
                    ·
                      refine ⟨1450712246076485422256909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3868565989537294459351757 1450712246076485422256909)
                      ·
                        rfl

theorem cell23_2825252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_2825252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825252 prefixEnd_2825252 := by exact prefixLift 2825252
  have htrace : WordTrace (prefixWord ++ tailWord_2825252) baseStart_2825252 baseEnd_2825252 := by
    simpa [prefixWord, tailWord_2825252, baseEnd_2825252] using wordTrace_append hprefix tailTrace_2825252
  have hstable : (prefixWord ++ tailWord_2825252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825252).length < 2 ^ (prefixWord ++ tailWord_2825252).sum := by decide
  have hdescent : baseEnd_2825252 < baseStart_2825252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825264 : List Nat := [2, 1, 1, 1, 2, 4, 2, 10]
def baseStart_2825264 : Nat := 118140960795 + 2825264 * 2 ^ 59
def prefixEnd_2825264 : Nat := 4983230072969 + 3 ^ 40 * 2825264 * 2
def baseEnd_2825264 : Nat := 53730311401642199085439

theorem tailTrace_2825264 : CollatzResearch.WordTrace tailWord_2825264 prefixEnd_2825264 53730311401642199085439 := by
  unfold tailWord_2825264
  simp only [CollatzResearch.WordTrace]
  refine ⟨51522921818279259760597423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68697229091039013014129897 51522921818279259760597423)
  ·
    refine ⟨77284382727418889640896135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51522921818279259760597423 77284382727418889640896135)
    ·
      refine ⟨115926574091128334461344203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77284382727418889640896135 115926574091128334461344203)
      ·
        refine ⟨173889861136692501692016305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115926574091128334461344203 173889861136692501692016305)
        ·
          refine ⟨130417395852519376269012229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173889861136692501692016305 130417395852519376269012229)
          ·
            refine ⟨24453261722347383050439793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130417395852519376269012229 24453261722347383050439793)
            ·
              refine ⟨18339946291760537287829845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24453261722347383050439793 18339946291760537287829845)
              ·
                refine ⟨53730311401642199085439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18339946291760537287829845 53730311401642199085439)
                ·
                  rfl

theorem cell23_2825264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 10].length) (baseStart_2825264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825264 prefixEnd_2825264 := by exact prefixLift 2825264
  have htrace : WordTrace (prefixWord ++ tailWord_2825264) baseStart_2825264 baseEnd_2825264 := by
    simpa [prefixWord, tailWord_2825264, baseEnd_2825264] using wordTrace_append hprefix tailTrace_2825264
  have hstable : (prefixWord ++ tailWord_2825264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825264).length < 2 ^ (prefixWord ++ tailWord_2825264).sum := by decide
  have hdescent : baseEnd_2825264 < baseStart_2825264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825286 : List Nat := [6, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3]
def baseStart_2825286 : Nat := 118140960795 + 2825286 * 2 ^ 59
def prefixEnd_2825286 : Nat := 4983230072969 + 3 ^ 40 * 2825286 * 2
def baseEnd_2825286 : Nat := 1450729704418738289231753

theorem tailTrace_2825286 : CollatzResearch.WordTrace tailWord_2825286 prefixEnd_2825286 1450729704418738289231753 := by
  unfold tailWord_2825286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3220207688827463039952991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 68697764028319211518997141 3220207688827463039952991)
  ·
    refine ⟨4830311533241194559929487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3220207688827463039952991 4830311533241194559929487)
    ·
      refine ⟨7245467299861791839894231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4830311533241194559929487 7245467299861791839894231)
      ·
        refine ⟨10868200949792687759841347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7245467299861791839894231 10868200949792687759841347)
        ·
          refine ⟨16302301424689031639762021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10868200949792687759841347 16302301424689031639762021)
          ·
            refine ⟨3056681517129193432455379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16302301424689031639762021 3056681517129193432455379)
            ·
              refine ⟨4585022275693790148683069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3056681517129193432455379 4585022275693790148683069)
              ·
                refine ⟨1719383353385171305756151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4585022275693790148683069 1719383353385171305756151)
                ·
                  refine ⟨2579075030077756958634227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1719383353385171305756151 2579075030077756958634227)
                  ·
                    refine ⟨3868612545116635437951341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2579075030077756958634227 3868612545116635437951341)
                    ·
                      refine ⟨1450729704418738289231753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3868612545116635437951341 1450729704418738289231753)
                      ·
                        rfl

theorem cell23_2825286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_2825286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825286 prefixEnd_2825286 := by exact prefixLift 2825286
  have htrace : WordTrace (prefixWord ++ tailWord_2825286) baseStart_2825286 baseEnd_2825286 := by
    simpa [prefixWord, tailWord_2825286, baseEnd_2825286] using wordTrace_append hprefix tailTrace_2825286
  have hstable : (prefixWord ++ tailWord_2825286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825286).length < 2 ^ (prefixWord ++ tailWord_2825286).sum := by decide
  have hdescent : baseEnd_2825286 < baseStart_2825286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825368 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 2, 4, 3]
def baseStart_2825368 : Nat := 118140960795 + 2825368 * 2 ^ 59
def prefixEnd_2825368 : Nat := 4983230072969 + 3 ^ 40 * 2825368 * 2
def baseEnd_2825368 : Nat := 1450771809832406968406375

theorem tailTrace_2825368 : CollatzResearch.WordTrace tailWord_2825368 prefixEnd_2825368 1450771809832406968406375 := by
  unfold tailWord_2825368
  simp only [CollatzResearch.WordTrace]
  refine ⟨51524818414090872641490379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68699757885454496855320505 51524818414090872641490379)
  ·
    refine ⟨77287227621136308962235569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51524818414090872641490379 77287227621136308962235569)
    ·
      refine ⟨57965420715852231721676677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77287227621136308962235569 57965420715852231721676677)
      ·
        refine ⟨10868516384222293447814377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57965420715852231721676677 10868516384222293447814377)
        ·
          refine ⟨8151387288166720085860783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10868516384222293447814377 8151387288166720085860783)
          ·
            refine ⟨12227080932250080128791175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8151387288166720085860783 12227080932250080128791175)
            ·
              refine ⟨18340621398375120193186763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12227080932250080128791175 18340621398375120193186763)
              ·
                refine ⟨27510932097562680289780145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18340621398375120193186763 27510932097562680289780145)
                ·
                  refine ⟨20633199073172010217335109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27510932097562680289780145 20633199073172010217335109)
                  ·
                    refine ⟨3868724826219751915750333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20633199073172010217335109 3868724826219751915750333)
                    ·
                      refine ⟨1450771809832406968406375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3868724826219751915750333 1450771809832406968406375)
                      ·
                        rfl

theorem cell23_2825368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_2825368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825368 prefixEnd_2825368 := by exact prefixLift 2825368
  have htrace : WordTrace (prefixWord ++ tailWord_2825368) baseStart_2825368 baseEnd_2825368 := by
    simpa [prefixWord, tailWord_2825368, baseEnd_2825368] using wordTrace_append hprefix tailTrace_2825368
  have hstable : (prefixWord ++ tailWord_2825368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825368).length < 2 ^ (prefixWord ++ tailWord_2825368).sum := by decide
  have hdescent : baseEnd_2825368 < baseStart_2825368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825411 : List Nat := [1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 5]
def baseStart_2825411 : Nat := 118140960795 + 2825411 * 2 ^ 59
def prefixEnd_2825411 : Nat := 4983230072969 + 3 ^ 40 * 2825411 * 2
def baseEnd_2825411 : Nat := 1450793889500550300168677

theorem tailTrace_2825411 : CollatzResearch.WordTrace tailWord_2825411 prefixEnd_2825411 1450793889500550300168677 := by
  unfold tailWord_2825411
  simp only [CollatzResearch.WordTrace]
  refine ⟨103051205167025963626796087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68700803444683975751197391 103051205167025963626796087)
  ·
    refine ⟨154576807750538945440194131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103051205167025963626796087 154576807750538945440194131)
    ·
      refine ⟨231865211625808418160291197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154576807750538945440194131 231865211625808418160291197)
      ·
        refine ⟨86949454359678156810109199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231865211625808418160291197 86949454359678156810109199)
        ·
          refine ⟨130424181539517235215163799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86949454359678156810109199 130424181539517235215163799)
          ·
            refine ⟨195636272309275852822745699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130424181539517235215163799 195636272309275852822745699)
            ·
              refine ⟨293454408463913779234118549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195636272309275852822745699 293454408463913779234118549)
              ·
                refine ⟨13755675396745958401599307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 293454408463913779234118549 13755675396745958401599307)
                ·
                  refine ⟨20633513095118937602398961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13755675396745958401599307 20633513095118937602398961)
                  ·
                    refine ⟨15475134821339203201799221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20633513095118937602398961 15475134821339203201799221)
                    ·
                      refine ⟨1450793889500550300168677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15475134821339203201799221 1450793889500550300168677)
                      ·
                        rfl

theorem cell23_2825411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_2825411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825411 prefixEnd_2825411 := by exact prefixLift 2825411
  have htrace : WordTrace (prefixWord ++ tailWord_2825411) baseStart_2825411 baseEnd_2825411 := by
    simpa [prefixWord, tailWord_2825411, baseEnd_2825411] using wordTrace_append hprefix tailTrace_2825411
  have hstable : (prefixWord ++ tailWord_2825411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825411).length < 2 ^ (prefixWord ++ tailWord_2825411).sum := by decide
  have hdescent : baseEnd_2825411 < baseStart_2825411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825475 : List Nat := [1, 1, 1, 3, 2, 5, 1, 2, 2, 2, 3]
def baseStart_2825475 : Nat := 118140960795 + 2825475 * 2 ^ 59
def prefixEnd_2825475 : Nat := 4983230072969 + 3 ^ 40 * 2825475 * 2
def baseEnd_2825475 : Nat := 1450826752262438049768383

theorem tailTrace_2825475 : CollatzResearch.WordTrace tailWord_2825475 prefixEnd_2825475 1450826752262438049768383 := by
  unfold tailWord_2825475
  simp only [CollatzResearch.WordTrace]
  refine ⟨103053539438794102557125879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68702359625862735038083919 103053539438794102557125879)
  ·
    refine ⟨154580309158191153835688819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103053539438794102557125879 154580309158191153835688819)
    ·
      refine ⟨231870463737286730753533229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154580309158191153835688819 231870463737286730753533229)
      ·
        refine ⟨86951423901482524032574961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231870463737286730753533229 86951423901482524032574961)
        ·
          refine ⟨65213567926111893024431221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86951423901482524032574961 65213567926111893024431221)
          ·
            refine ⟨6113771993072989971040427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65213567926111893024431221 6113771993072989971040427)
            ·
              refine ⟨9170657989609484956560641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6113771993072989971040427 9170657989609484956560641)
              ·
                refine ⟨6877993492207113717420481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9170657989609484956560641 6877993492207113717420481)
                ·
                  refine ⟨5158495119155335288065361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6877993492207113717420481 5158495119155335288065361)
                  ·
                    refine ⟨3868871339366501466049021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5158495119155335288065361 3868871339366501466049021)
                    ·
                      refine ⟨1450826752262438049768383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3868871339366501466049021 1450826752262438049768383)
                      ·
                        rfl

theorem cell23_2825475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 2, 3].length) (baseStart_2825475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825475 prefixEnd_2825475 := by exact prefixLift 2825475
  have htrace : WordTrace (prefixWord ++ tailWord_2825475) baseStart_2825475 baseEnd_2825475 := by
    simpa [prefixWord, tailWord_2825475, baseEnd_2825475] using wordTrace_append hprefix tailTrace_2825475
  have hstable : (prefixWord ++ tailWord_2825475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825475).length < 2 ^ (prefixWord ++ tailWord_2825475).sum := by decide
  have hdescent : baseEnd_2825475 < baseStart_2825475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825491 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 1, 11]
def baseStart_2825491 : Nat := 118140960795 + 2825491 * 2 ^ 59
def prefixEnd_2825491 : Nat := 4983230072969 + 3 ^ 40 * 2825491 * 2
def baseEnd_2825491 : Nat := 483611655984303329056103

theorem tailTrace_2825491 : CollatzResearch.WordTrace tailWord_2825491 prefixEnd_2825491 483611655984303329056103 := by
  unfold tailWord_2825491
  simp only [CollatzResearch.WordTrace]
  refine ⟨103054123006736137289708327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68702748671157424859805551 103054123006736137289708327)
  ·
    refine ⟨154581184510104205934562491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103054123006736137289708327 154581184510104205934562491)
    ·
      refine ⟨231871776765156308901843737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154581184510104205934562491 231871776765156308901843737)
      ·
        refine ⟨173903832573867231676382803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231871776765156308901843737 173903832573867231676382803)
        ·
          refine ⟨260855748860800847514574205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173903832573867231676382803 260855748860800847514574205)
          ·
            refine ⟨97820905822800317817965327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260855748860800847514574205 97820905822800317817965327)
            ·
              refine ⟨146731358734200476726947991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97820905822800317817965327 146731358734200476726947991)
              ·
                refine ⟨220097038101300715090421987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146731358734200476726947991 220097038101300715090421987)
                ·
                  refine ⟨330145557151951072635632981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220097038101300715090421987 330145557151951072635632981)
                  ·
                    refine ⟨483611655984303329056103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 330145557151951072635632981 483611655984303329056103)
                    ·
                      rfl

theorem cell23_2825491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 11].length) (baseStart_2825491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825491 prefixEnd_2825491 := by exact prefixLift 2825491
  have htrace : WordTrace (prefixWord ++ tailWord_2825491) baseStart_2825491 baseEnd_2825491 := by
    simpa [prefixWord, tailWord_2825491, baseEnd_2825491] using wordTrace_append hprefix tailTrace_2825491
  have hstable : (prefixWord ++ tailWord_2825491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825491).length < 2 ^ (prefixWord ++ tailWord_2825491).sum := by decide
  have hdescent : baseEnd_2825491 < baseStart_2825491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825505 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 5, 1, 3]
def baseStart_2825505 : Nat := 118140960795 + 2825505 * 2 ^ 59
def prefixEnd_2825505 : Nat := 4983230072969 + 3 ^ 40 * 2825505 * 2
def baseEnd_2825505 : Nat := 1450842156682072932393245

theorem tailTrace_2825505 : CollatzResearch.WordTrace tailWord_2825505 prefixEnd_2825505 1450842156682072932393245 := by
  unfold tailWord_2825505
  simp only [CollatzResearch.WordTrace]
  refine ⟨103054633628685417680717969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68703089085790278453811979 103054633628685417680717969)
  ·
    refine ⟨77290975221514063260538477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103054633628685417680717969 77290975221514063260538477)
    ·
      refine ⟨28984115708067773722701929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77290975221514063260538477 28984115708067773722701929)
      ·
        refine ⟨21738086781050830292026447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28984115708067773722701929 21738086781050830292026447)
        ·
          refine ⟨32607130171576245438039671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21738086781050830292026447 32607130171576245438039671)
          ·
            refine ⟨48910695257364368157059507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32607130171576245438039671 48910695257364368157059507)
            ·
              refine ⟨73366042886046552235589261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48910695257364368157059507 73366042886046552235589261)
              ·
                refine ⟨27512266082267457088345973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73366042886046552235589261 27512266082267457088345973)
                ·
                  refine ⟨2579274945212574102032435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27512266082267457088345973 2579274945212574102032435)
                  ·
                    refine ⟨3868912417818861153048653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2579274945212574102032435 3868912417818861153048653)
                    ·
                      refine ⟨1450842156682072932393245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3868912417818861153048653 1450842156682072932393245)
                      ·
                        rfl

theorem cell23_2825505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_2825505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825505 prefixEnd_2825505 := by exact prefixLift 2825505
  have htrace : WordTrace (prefixWord ++ tailWord_2825505) baseStart_2825505 baseEnd_2825505 := by
    simpa [prefixWord, tailWord_2825505, baseEnd_2825505] using wordTrace_append hprefix tailTrace_2825505
  have hstable : (prefixWord ++ tailWord_2825505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825505).length < 2 ^ (prefixWord ++ tailWord_2825505).sum := by decide
  have hdescent : baseEnd_2825505 < baseStart_2825505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825532 : List Nat := [2, 2, 2, 2, 1, 3, 2, 2, 2, 3, 2]
def baseStart_2825532 : Nat := 118140960795 + 2825532 * 2 ^ 59
def prefixEnd_2825532 : Nat := 4983230072969 + 3 ^ 40 * 2825532 * 2
def baseEnd_2825532 : Nat := 1450856020659744326755621

theorem tailTrace_2825532 : CollatzResearch.WordTrace tailWord_2825532 prefixEnd_2825532 1450856020659744326755621 := by
  unfold tailWord_2825532
  simp only [CollatzResearch.WordTrace]
  refine ⟨51527809199793800645975425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68703745599725067527967233 51527809199793800645975425)
  ·
    refine ⟨38645856899845350484481569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51527809199793800645975425 38645856899845350484481569)
    ·
      refine ⟨28984392674884012863361177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38645856899845350484481569 28984392674884012863361177)
      ·
        refine ⟨21738294506163009647520883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28984392674884012863361177 21738294506163009647520883)
        ·
          refine ⟨32607441759244514471281325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21738294506163009647520883 32607441759244514471281325)
          ·
            refine ⟨12227790659716692926730497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32607441759244514471281325 12227790659716692926730497)
            ·
              refine ⟨9170842994787519695047873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12227790659716692926730497 9170842994787519695047873)
              ·
                refine ⟨6878132246090639771285905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9170842994787519695047873 6878132246090639771285905)
                ·
                  refine ⟨5158599184567979828464429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6878132246090639771285905 5158599184567979828464429)
                  ·
                    refine ⟨1934474694212992435674161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5158599184567979828464429 1934474694212992435674161)
                    ·
                      refine ⟨1450856020659744326755621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1934474694212992435674161 1450856020659744326755621)
                      ·
                        rfl

theorem cell23_2825532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_2825532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825532 prefixEnd_2825532 := by exact prefixLift 2825532
  have htrace : WordTrace (prefixWord ++ tailWord_2825532) baseStart_2825532 baseEnd_2825532 := by
    simpa [prefixWord, tailWord_2825532, baseEnd_2825532] using wordTrace_append hprefix tailTrace_2825532
  have hstable : (prefixWord ++ tailWord_2825532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825532).length < 2 ^ (prefixWord ++ tailWord_2825532).sum := by decide
  have hdescent : baseEnd_2825532 < baseStart_2825532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825533 : List Nat := [1, 4, 1, 5, 1, 2, 2, 2, 1, 4]
def baseStart_2825533 : Nat := 118140960795 + 2825533 * 2 ^ 59
def prefixEnd_2825533 : Nat := 4983230072969 + 3 ^ 40 * 2825533 * 2
def baseEnd_2825533 : Nat := 483618844713466274281039

theorem tailTrace_2825533 : CollatzResearch.WordTrace tailWord_2825533 prefixEnd_2825533 483618844713466274281039 := by
  unfold tailWord_2825533
  simp only [CollatzResearch.WordTrace]
  refine ⟨103055654872583978462737253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68703769915055985641824835 103055654872583978462737253)
  ·
    refine ⟨19322935288609495961763235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103055654872583978462737253 19322935288609495961763235)
    ·
      refine ⟨28984402932914243942644853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19322935288609495961763235 28984402932914243942644853)
      ·
        refine ⟨2717287774960710369622955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28984402932914243942644853 2717287774960710369622955)
        ·
          refine ⟨4075931662441065554434433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2717287774960710369622955 4075931662441065554434433)
          ·
            refine ⟨3056948746830799165825825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4075931662441065554434433 3056948746830799165825825)
            ·
              refine ⟨2292711560123099374369369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3056948746830799165825825 2292711560123099374369369)
              ·
                refine ⟨1719533670092324530777027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2292711560123099374369369 1719533670092324530777027)
                ·
                  refine ⟨2579300505138486796165541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1719533670092324530777027 2579300505138486796165541)
                  ·
                    refine ⟨483618844713466274281039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2579300505138486796165541 483618844713466274281039)
                    ·
                      rfl

theorem cell23_2825533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_2825533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825533 prefixEnd_2825533 := by exact prefixLift 2825533
  have htrace : WordTrace (prefixWord ++ tailWord_2825533) baseStart_2825533 baseEnd_2825533 := by
    simpa [prefixWord, tailWord_2825533, baseEnd_2825533] using wordTrace_append hprefix tailTrace_2825533
  have hstable : (prefixWord ++ tailWord_2825533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825533).length < 2 ^ (prefixWord ++ tailWord_2825533).sum := by decide
  have hdescent : baseEnd_2825533 < baseStart_2825533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825555 : List Nat := [1, 1, 1, 2, 1, 1, 5, 5, 2, 4]
def baseStart_2825555 : Nat := 118140960795 + 2825555 * 2 ^ 59
def prefixEnd_2825555 : Nat := 4983230072969 + 3 ^ 40 * 2825555 * 2
def baseEnd_2825555 : Nat := 483622610238265912256005

theorem tailTrace_2825555 : CollatzResearch.WordTrace tailWord_2825555 prefixEnd_2825555 483622610238265912256005 := by
  unfold tailWord_2825555
  simp only [CollatzResearch.WordTrace]
  refine ⟨103056457278504276220038119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68704304852336184146692079 103056457278504276220038119)
  ·
    refine ⟨154584685917756414330057179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103056457278504276220038119 154584685917756414330057179)
    ·
      refine ⟨231877028876634621495085769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154584685917756414330057179 231877028876634621495085769)
      ·
        refine ⟨173907771657475966121314327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231877028876634621495085769 173907771657475966121314327)
        ·
          refine ⟨260861657486213949181971491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173907771657475966121314327 260861657486213949181971491)
          ·
            refine ⟨391292486229320923772957237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260861657486213949181971491 391292486229320923772957237)
            ·
              refine ⟨36683670583998836603714741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 391292486229320923772957237 36683670583998836603714741)
              ·
                refine ⟨3439094117249890931598257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36683670583998836603714741 3439094117249890931598257)
                ·
                  refine ⟨2579320587937418198698693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3439094117249890931598257 2579320587937418198698693)
                  ·
                    refine ⟨483622610238265912256005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2579320587937418198698693 483622610238265912256005)
                    ·
                      rfl

theorem cell23_2825555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 2, 4].length) (baseStart_2825555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825555 prefixEnd_2825555 := by exact prefixLift 2825555
  have htrace : WordTrace (prefixWord ++ tailWord_2825555) baseStart_2825555 baseEnd_2825555 := by
    simpa [prefixWord, tailWord_2825555, baseEnd_2825555] using wordTrace_append hprefix tailTrace_2825555
  have hstable : (prefixWord ++ tailWord_2825555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825555).length < 2 ^ (prefixWord ++ tailWord_2825555).sum := by decide
  have hdescent : baseEnd_2825555 < baseStart_2825555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825562 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 5, 2, 2]
def baseStart_2825562 : Nat := 118140960795 + 2825562 * 2 ^ 59
def prefixEnd_2825562 : Nat := 4983230072969 + 3 ^ 40 * 2825562 * 2
def baseEnd_2825562 : Nat := 1450871425079379209380483

theorem tailTrace_2825562 : CollatzResearch.WordTrace tailWord_2825562 prefixEnd_2825562 1450871425079379209380483 := by
  unfold tailWord_2825562
  simp only [CollatzResearch.WordTrace]
  refine ⟨25764178147369729103885735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68704475059652610943695293 25764178147369729103885735)
  ·
    refine ⟨38646267221054593655828603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25764178147369729103885735 38646267221054593655828603)
    ·
      refine ⟨57969400831581890483742905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38646267221054593655828603 57969400831581890483742905)
      ·
        refine ⟨43477050623686417862807179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57969400831581890483742905 43477050623686417862807179)
        ·
          refine ⟨65215575935529626794210769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43477050623686417862807179 65215575935529626794210769)
          ·
            refine ⟨48911681951647220095658077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65215575935529626794210769 48911681951647220095658077)
            ·
              refine ⟨18341880731867707535871779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48911681951647220095658077 18341880731867707535871779)
              ·
                refine ⟨27512821097801561303807669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18341880731867707535871779 27512821097801561303807669)
                ·
                  refine ⟨2579326977918896372231969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27512821097801561303807669 2579326977918896372231969)
                  ·
                    refine ⟨1934495233439172279173977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2579326977918896372231969 1934495233439172279173977)
                    ·
                      refine ⟨1450871425079379209380483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1934495233439172279173977 1450871425079379209380483)
                      ·
                        rfl

theorem cell23_2825562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 5, 2, 2].length) (baseStart_2825562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825562 prefixEnd_2825562 := by exact prefixLift 2825562
  have htrace : WordTrace (prefixWord ++ tailWord_2825562) baseStart_2825562 baseEnd_2825562 := by
    simpa [prefixWord, tailWord_2825562, baseEnd_2825562] using wordTrace_append hprefix tailTrace_2825562
  have hstable : (prefixWord ++ tailWord_2825562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825562).length < 2 ^ (prefixWord ++ tailWord_2825562).sum := by decide
  have hdescent : baseEnd_2825562 < baseStart_2825562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825576 : List Nat := [2, 1, 4, 2, 4, 1, 2, 1, 1, 5]
def baseStart_2825576 : Nat := 118140960795 + 2825576 * 2 ^ 59
def prefixEnd_2825576 : Nat := 4983230072969 + 3 ^ 40 * 2825576 * 2
def baseEnd_2825576 : Nat := 483626204602847384868473

theorem tailTrace_2825576 : CollatzResearch.WordTrace tailWord_2825576 prefixEnd_2825576 483626204602847384868473 := by
  unfold tailWord_2825576
  simp only [CollatzResearch.WordTrace]
  refine ⟨51528611605714098403276291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68704815474285464537701721 51528611605714098403276291)
  ·
    refine ⟨77292917408571147604914437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51528611605714098403276291 77292917408571147604914437)
    ·
      refine ⟨14492422014107090175921457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77292917408571147604914437 14492422014107090175921457)
      ·
        refine ⟨10869316510580317631941093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14492422014107090175921457 10869316510580317631941093)
        ·
          refine ⟨2037996845733809555988955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10869316510580317631941093 2037996845733809555988955)
          ·
            refine ⟨3056995268600714333983433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2037996845733809555988955 3056995268600714333983433)
            ·
              refine ⟨2292746451450535750487575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3056995268600714333983433 2292746451450535750487575)
              ·
                refine ⟨3439119677175803625731363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2292746451450535750487575 3439119677175803625731363)
                ·
                  refine ⟨5158679515763705438597045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3439119677175803625731363 5158679515763705438597045)
                  ·
                    refine ⟨483626204602847384868473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5158679515763705438597045 483626204602847384868473)
                    ·
                      rfl

theorem cell23_2825576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_2825576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825576 prefixEnd_2825576 := by exact prefixLift 2825576
  have htrace : WordTrace (prefixWord ++ tailWord_2825576) baseStart_2825576 baseEnd_2825576 := by
    simpa [prefixWord, tailWord_2825576, baseEnd_2825576] using wordTrace_append hprefix tailTrace_2825576
  have hstable : (prefixWord ++ tailWord_2825576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825576).length < 2 ^ (prefixWord ++ tailWord_2825576).sum := by decide
  have hdescent : baseEnd_2825576 < baseStart_2825576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825609 : List Nat := [1, 2, 1, 1, 8, 1, 1, 1, 1, 2, 4]
def baseStart_2825609 : Nat := 118140960795 + 2825609 * 2 ^ 59
def prefixEnd_2825609 : Nat := 4983230072969 + 3 ^ 40 * 2825609 * 2
def baseEnd_2825609 : Nat := 1450895558670140525492767

theorem tailTrace_2825609 : CollatzResearch.WordTrace tailWord_2825609 prefixEnd_2825609 1450895558670140525492767 := by
  unfold tailWord_2825609
  simp only [CollatzResearch.WordTrace]
  refine ⟨103058426820308643442503881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68705617880205762295002587 103058426820308643442503881)
  ·
    refine ⟨77293820115231482581877911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103058426820308643442503881 77293820115231482581877911)
    ·
      refine ⟨115940730172847223872816867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77293820115231482581877911 115940730172847223872816867)
      ·
        refine ⟨173911095259270835809225301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115940730172847223872816867 173911095259270835809225301)
        ·
          refine ⟨2038020647569580107139359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 173911095259270835809225301 2038020647569580107139359)
          ·
            refine ⟨3057030971354370160709039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2038020647569580107139359 3057030971354370160709039)
            ·
              refine ⟨4585546457031555241063559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3057030971354370160709039 4585546457031555241063559)
              ·
                refine ⟨6878319685547332861595339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4585546457031555241063559 6878319685547332861595339)
                ·
                  refine ⟨10317479528320999292393009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6878319685547332861595339 10317479528320999292393009)
                  ·
                    refine ⟨7738109646240749469294757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10317479528320999292393009 7738109646240749469294757)
                    ·
                      refine ⟨1450895558670140525492767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7738109646240749469294757 1450895558670140525492767)
                      ·
                        rfl

theorem cell23_2825609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 1, 2, 4].length) (baseStart_2825609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825609 prefixEnd_2825609 := by exact prefixLift 2825609
  have htrace : WordTrace (prefixWord ++ tailWord_2825609) baseStart_2825609 baseEnd_2825609 := by
    simpa [prefixWord, tailWord_2825609, baseEnd_2825609] using wordTrace_append hprefix tailTrace_2825609
  have hstable : (prefixWord ++ tailWord_2825609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825609).length < 2 ^ (prefixWord ++ tailWord_2825609).sum := by decide
  have hdescent : baseEnd_2825609 < baseStart_2825609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825639 : List Nat := [1, 1, 6, 1, 1, 1, 1, 5, 1, 3, 2]
def baseStart_2825639 : Nat := 118140960795 + 2825639 * 2 ^ 59
def prefixEnd_2825639 : Nat := 4983230072969 + 3 ^ 40 * 2825639 * 2
def baseEnd_2825639 : Nat := 1450910963089775408117629

theorem tailTrace_2825639 : CollatzResearch.WordTrace tailWord_2825639 prefixEnd_2825639 1450910963089775408117629 := by
  unfold tailWord_2825639
  simp only [CollatzResearch.WordTrace]
  refine ⟨103059521010199958566095971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68706347340133305710730647 103059521010199958566095971)
  ·
    refine ⟨154589281515299937849143957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103059521010199958566095971 154589281515299937849143957)
    ·
      refine ⟨7246372571029684586678623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 154589281515299937849143957 7246372571029684586678623)
      ·
        refine ⟨10869558856544526880017935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7246372571029684586678623 10869558856544526880017935)
        ·
          refine ⟨16304338284816790320026903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10869558856544526880017935 16304338284816790320026903)
          ·
            refine ⟨24456507427225185480040355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16304338284816790320026903 24456507427225185480040355)
            ·
              refine ⟨36684761140837778220060533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24456507427225185480040355 36684761140837778220060533)
              ·
                refine ⟨3439196356953541708130675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36684761140837778220060533 3439196356953541708130675)
                ·
                  refine ⟨5158794535430312562196013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3439196356953541708130675 5158794535430312562196013)
                  ·
                    refine ⟨1934547950786367210823505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5158794535430312562196013 1934547950786367210823505)
                    ·
                      refine ⟨1450910963089775408117629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1934547950786367210823505 1450910963089775408117629)
                      ·
                        rfl

theorem cell23_2825639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_2825639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825639 prefixEnd_2825639 := by exact prefixLift 2825639
  have htrace : WordTrace (prefixWord ++ tailWord_2825639) baseStart_2825639 baseEnd_2825639 := by
    simpa [prefixWord, tailWord_2825639, baseEnd_2825639] using wordTrace_append hprefix tailTrace_2825639
  have hstable : (prefixWord ++ tailWord_2825639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825639).length < 2 ^ (prefixWord ++ tailWord_2825639).sum := by decide
  have hdescent : baseEnd_2825639 < baseStart_2825639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825648 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 6]
def baseStart_2825648 : Nat := 118140960795 + 2825648 * 2 ^ 59
def prefixEnd_2825648 : Nat := 4983230072969 + 3 ^ 40 * 2825648 * 2
def baseEnd_2825648 : Nat := 1450915584415665872905087

theorem tailTrace_2825648 : CollatzResearch.WordTrace tailWord_2825648 prefixEnd_2825648 1450915584415665872905087 := by
  unfold tailWord_2825648
  simp only [CollatzResearch.WordTrace]
  refine ⟨51529924633583676551586799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68706566178111568735449065 51529924633583676551586799)
  ·
    refine ⟨77294886950375514827380199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51529924633583676551586799 77294886950375514827380199)
    ·
      refine ⟨115942330425563272241070299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77294886950375514827380199 115942330425563272241070299)
      ·
        refine ⟨173913495638344908361605449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115942330425563272241070299 173913495638344908361605449)
        ·
          refine ⟨130435121728758681271204087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173913495638344908361605449 130435121728758681271204087)
          ·
            refine ⟨195652682593138021906806131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130435121728758681271204087 195652682593138021906806131)
            ·
              refine ⟨293479023889707032860209197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195652682593138021906806131 293479023889707032860209197)
              ·
                refine ⟨110054633958640137322578449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 293479023889707032860209197 110054633958640137322578449)
                ·
                  refine ⟨82540975468980102991933837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110054633958640137322578449 82540975468980102991933837)
                  ·
                    refine ⟨30952865800867538621975189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82540975468980102991933837 30952865800867538621975189)
                    ·
                      refine ⟨1450915584415665872905087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30952865800867538621975189 1450915584415665872905087)
                      ·
                        rfl

theorem cell23_2825648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 6].length) (baseStart_2825648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825648 prefixEnd_2825648 := by exact prefixLift 2825648
  have htrace : WordTrace (prefixWord ++ tailWord_2825648) baseStart_2825648 baseEnd_2825648 := by
    simpa [prefixWord, tailWord_2825648, baseEnd_2825648] using wordTrace_append hprefix tailTrace_2825648
  have hstable : (prefixWord ++ tailWord_2825648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825648).length < 2 ^ (prefixWord ++ tailWord_2825648).sum := by decide
  have hdescent : baseEnd_2825648 < baseStart_2825648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825655 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 2, 4, 3]
def baseStart_2825655 : Nat := 118140960795 + 2825655 * 2 ^ 59
def prefixEnd_2825655 : Nat := 4983230072969 + 3 ^ 40 * 2825655 * 2
def baseEnd_2825655 : Nat := 1450919178780247345517555

theorem tailTrace_2825655 : CollatzResearch.WordTrace tailWord_2825655 prefixEnd_2825655 1450919178780247345517555 := by
  unfold tailWord_2825655
  simp only [CollatzResearch.WordTrace]
  refine ⟨103060104578141993298678419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68706736385427995532452279 103060104578141993298678419)
  ·
    refine ⟨154590156867212989948017629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103060104578141993298678419 154590156867212989948017629)
    ·
      refine ⟨57971308825204871230506611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154590156867212989948017629 57971308825204871230506611)
      ·
        refine ⟨86956963237807306845759917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57971308825204871230506611 86956963237807306845759917)
        ·
          refine ⟨32608861214177740067159969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86956963237807306845759917 32608861214177740067159969)
          ·
            refine ⟨24456645910633305050369977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32608861214177740067159969 24456645910633305050369977)
            ·
              refine ⟨18342484432974978787777483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24456645910633305050369977 18342484432974978787777483)
              ·
                refine ⟨27513726649462468181666225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18342484432974978787777483 27513726649462468181666225)
                ·
                  refine ⟨20635294987096851136249669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27513726649462468181666225 20635294987096851136249669)
                  ·
                    refine ⟨3869117810080659588046813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20635294987096851136249669 3869117810080659588046813)
                    ·
                      refine ⟨1450919178780247345517555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3869117810080659588046813 1450919178780247345517555)
                      ·
                        rfl

theorem cell23_2825655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 4, 3].length) (baseStart_2825655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825655 prefixEnd_2825655 := by exact prefixLift 2825655
  have htrace : WordTrace (prefixWord ++ tailWord_2825655) baseStart_2825655 baseEnd_2825655 := by
    simpa [prefixWord, tailWord_2825655, baseEnd_2825655] using wordTrace_append hprefix tailTrace_2825655
  have hstable : (prefixWord ++ tailWord_2825655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825655).length < 2 ^ (prefixWord ++ tailWord_2825655).sum := by decide
  have hdescent : baseEnd_2825655 < baseStart_2825655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825686 : List Nat := [5, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2]
def baseStart_2825686 : Nat := 118140960795 + 2825686 * 2 ^ 59
def prefixEnd_2825686 : Nat := 4983230072969 + 3 ^ 40 * 2825686 * 2
def baseEnd_2825686 : Nat := 1450935096680536724229913

theorem tailTrace_2825686 : CollatzResearch.WordTrace tailWord_2825686 prefixEnd_2825686 1450935096680536724229913 := by
  unfold tailWord_2825686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6441327202564355349566057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68707490160686457062037941 6441327202564355349566057)
  ·
    refine ⟨4830995401923266512174543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6441327202564355349566057 4830995401923266512174543)
    ·
      refine ⟨7246493102884899768261815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4830995401923266512174543 7246493102884899768261815)
      ·
        refine ⟨10869739654327349652392723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7246493102884899768261815 10869739654327349652392723)
        ·
          refine ⟨16304609481491024478589085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10869739654327349652392723 16304609481491024478589085)
          ·
            refine ⟨6114228555559134179470907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16304609481491024478589085 6114228555559134179470907)
            ·
              refine ⟨9171342833338701269206361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6114228555559134179470907 9171342833338701269206361)
              ·
                refine ⟨6878507125004025951904771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9171342833338701269206361 6878507125004025951904771)
                ·
                  refine ⟨10317760687506038927857157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6878507125004025951904771 10317760687506038927857157)
                  ·
                    refine ⟨1934580128907382298973217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10317760687506038927857157 1934580128907382298973217)
                    ·
                      refine ⟨1450935096680536724229913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1934580128907382298973217 1450935096680536724229913)
                      ·
                        rfl

theorem cell23_2825686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_2825686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825686 prefixEnd_2825686 := by exact prefixLift 2825686
  have htrace : WordTrace (prefixWord ++ tailWord_2825686) baseStart_2825686 baseEnd_2825686 := by
    simpa [prefixWord, tailWord_2825686, baseEnd_2825686] using wordTrace_append hprefix tailTrace_2825686
  have hstable : (prefixWord ++ tailWord_2825686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825686).length < 2 ^ (prefixWord ++ tailWord_2825686).sum := by decide
  have hdescent : baseEnd_2825686 < baseStart_2825686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825712 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 2, 5, 2]
def baseStart_2825712 : Nat := 118140960795 + 2825712 * 2 ^ 59
def prefixEnd_2825712 : Nat := 4983230072969 + 3 ^ 40 * 2825712 * 2
def baseEnd_2825712 : Nat := 1450948447177553622504793

theorem tailTrace_2825712 : CollatzResearch.WordTrace tailWord_2825712 prefixEnd_2825712 1450948447177553622504793 := by
  unfold tailWord_2825712
  simp only [CollatzResearch.WordTrace]
  refine ⟨51531091769467746016751695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68708122359290328022335593 51531091769467746016751695)
  ·
    refine ⟨77296637654201619025127543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51531091769467746016751695 77296637654201619025127543)
    ·
      refine ⟨115944956481302428537691315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77296637654201619025127543 115944956481302428537691315)
      ·
        refine ⟨173917434721953642806536973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115944956481302428537691315 173917434721953642806536973)
        ·
          refine ⟨65219038020732616052451365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173917434721953642806536973 65219038020732616052451365)
          ·
            refine ⟨12228569628887365509834631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65219038020732616052451365 12228569628887365509834631)
            ·
              refine ⟨18342854443331048264751947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12228569628887365509834631 18342854443331048264751947)
              ·
                refine ⟨27514281664996572397127921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18342854443331048264751947 27514281664996572397127921)
                ·
                  refine ⟨20635711248747429297845941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27514281664996572397127921 20635711248747429297845941)
                  ·
                    refine ⟨1934597929570071496673057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20635711248747429297845941 1934597929570071496673057)
                    ·
                      refine ⟨1450948447177553622504793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1934597929570071496673057 1450948447177553622504793)
                      ·
                        rfl

theorem cell23_2825712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 2, 5, 2].length) (baseStart_2825712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825712 prefixEnd_2825712 := by exact prefixLift 2825712
  have htrace : WordTrace (prefixWord ++ tailWord_2825712) baseStart_2825712 baseEnd_2825712 := by
    simpa [prefixWord, tailWord_2825712, baseEnd_2825712] using wordTrace_append hprefix tailTrace_2825712
  have hstable : (prefixWord ++ tailWord_2825712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825712).length < 2 ^ (prefixWord ++ tailWord_2825712).sum := by decide
  have hdescent : baseEnd_2825712 < baseStart_2825712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825739 : List Nat := [1, 1, 1, 1, 8, 2, 1, 1, 2, 5]
def baseStart_2825739 : Nat := 118140960795 + 2825739 * 2 ^ 59
def prefixEnd_2825739 : Nat := 4983230072969 + 3 ^ 40 * 2825739 * 2
def baseEnd_2825739 : Nat := 483654103718408338955723

theorem tailTrace_2825739 : CollatzResearch.WordTrace tailWord_2825739 prefixEnd_2825739 483654103718408338955723 := by
  unfold tailWord_2825739
  simp only [CollatzResearch.WordTrace]
  refine ⟨103063168309837675644736271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68708778873225117096490847 103063168309837675644736271)
  ·
    refine ⟨154594752464756513467104407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103063168309837675644736271 154594752464756513467104407)
    ·
      refine ⟨231892128697134770200656611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154594752464756513467104407 231892128697134770200656611)
      ·
        refine ⟨347838193045702155300984917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231892128697134770200656611 347838193045702155300984917)
        ·
          refine ⟨4076228824754322132433417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 347838193045702155300984917 4076228824754322132433417)
          ·
            refine ⟨3057171618565741599325063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4076228824754322132433417 3057171618565741599325063)
            ·
              refine ⟨4585757427848612398987595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3057171618565741599325063 4585757427848612398987595)
              ·
                refine ⟨6878636141772918598481393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4585757427848612398987595 6878636141772918598481393)
                ·
                  refine ⟨5158977106329688948861045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6878636141772918598481393 5158977106329688948861045)
                  ·
                    refine ⟨483654103718408338955723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5158977106329688948861045 483654103718408338955723)
                    ·
                      rfl

theorem cell23_2825739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 5].length) (baseStart_2825739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825739 prefixEnd_2825739 := by exact prefixLift 2825739
  have htrace : WordTrace (prefixWord ++ tailWord_2825739) baseStart_2825739 baseEnd_2825739 := by
    simpa [prefixWord, tailWord_2825739, baseEnd_2825739] using wordTrace_append hprefix tailTrace_2825739
  have hstable : (prefixWord ++ tailWord_2825739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825739).length < 2 ^ (prefixWord ++ tailWord_2825739).sum := by decide
  have hdescent : baseEnd_2825739 < baseStart_2825739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825835 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 5]
def baseStart_2825835 : Nat := 118140960795 + 2825835 * 2 ^ 59
def prefixEnd_2825835 : Nat := 4983230072969 + 3 ^ 40 * 2825835 * 2
def baseEnd_2825835 : Nat := 1451011605298056641266727

theorem tailTrace_2825835 : CollatzResearch.WordTrace tailWord_2825835 prefixEnd_2825835 1451011605298056641266727 := by
  unfold tailWord_2825835
  simp only [CollatzResearch.WordTrace]
  refine ⟨103066669717489884040230959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68711113144993256026820639 103066669717489884040230959)
  ·
    refine ⟨154600004576234826060346439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103066669717489884040230959 154600004576234826060346439)
    ·
      refine ⟨231900006864352239090519659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154600004576234826060346439 231900006864352239090519659)
      ·
        refine ⟨347850010296528358635779489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231900006864352239090519659 347850010296528358635779489)
        ·
          refine ⟨260887507722396268976834617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347850010296528358635779489 260887507722396268976834617)
          ·
            refine ⟨195665630791797201732625963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260887507722396268976834617 195665630791797201732625963)
            ·
              refine ⟨293498446187695802598938945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195665630791797201732625963 293498446187695802598938945)
              ·
                refine ⟨220123834640771851949204209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 293498446187695802598938945 220123834640771851949204209)
                ·
                  refine ⟨165092875980578888961903157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220123834640771851949204209 165092875980578888961903157)
                  ·
                    refine ⟨15477457123179270840178421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 165092875980578888961903157 15477457123179270840178421)
                    ·
                      refine ⟨1451011605298056641266727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15477457123179270840178421 1451011605298056641266727)
                      ·
                        rfl

theorem cell23_2825835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 5].length) (baseStart_2825835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825835 prefixEnd_2825835 := by exact prefixLift 2825835
  have htrace : WordTrace (prefixWord ++ tailWord_2825835) baseStart_2825835 baseEnd_2825835 := by
    simpa [prefixWord, tailWord_2825835, baseEnd_2825835] using wordTrace_append hprefix tailTrace_2825835
  have hstable : (prefixWord ++ tailWord_2825835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825835).length < 2 ^ (prefixWord ++ tailWord_2825835).sum := by decide
  have hdescent : baseEnd_2825835 < baseStart_2825835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825846 : List Nat := [5, 1, 1, 2, 2, 1, 3, 2, 1, 5]
def baseStart_2825846 : Nat := 118140960795 + 2825846 * 2 ^ 59
def prefixEnd_2825846 : Nat := 4983230072969 + 3 ^ 40 * 2825846 * 2
def baseEnd_2825846 : Nat := 483672417861752032743059

theorem tailTrace_2825846 : CollatzResearch.WordTrace tailWord_2825846 prefixEnd_2825846 483672417861752032743059 := by
  unfold tailWord_2825846
  simp only [CollatzResearch.WordTrace]
  refine ⟨6441691932528127057430087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 68711380613633355279254261 6441691932528127057430087)
  ·
    refine ⟨9662537898792190586145131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6441691932528127057430087 9662537898792190586145131)
    ·
      refine ⟨14493806848188285879217697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9662537898792190586145131 14493806848188285879217697)
      ·
        refine ⟨10870355136141214409413273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14493806848188285879217697 10870355136141214409413273)
        ·
          refine ⟨8152766352105910807059955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10870355136141214409413273 8152766352105910807059955)
          ·
            refine ⟨12229149528158866210589933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8152766352105910807059955 12229149528158866210589933)
            ·
              refine ⟨4585931073059574828971225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12229149528158866210589933 4585931073059574828971225)
              ·
                refine ⟨3439448304794681121728419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4585931073059574828971225 3439448304794681121728419)
                ·
                  refine ⟨5159172457192021682592629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3439448304794681121728419 5159172457192021682592629)
                  ·
                    refine ⟨483672417861752032743059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5159172457192021682592629 483672417861752032743059)
                    ·
                      rfl

theorem cell23_2825846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_2825846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825846 prefixEnd_2825846 := by exact prefixLift 2825846
  have htrace : WordTrace (prefixWord ++ tailWord_2825846) baseStart_2825846 baseEnd_2825846 := by
    simpa [prefixWord, tailWord_2825846, baseEnd_2825846] using wordTrace_append hprefix tailTrace_2825846
  have hstable : (prefixWord ++ tailWord_2825846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825846).length < 2 ^ (prefixWord ++ tailWord_2825846).sum := by decide
  have hdescent : baseEnd_2825846 < baseStart_2825846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825886 : List Nat := [4, 3, 1, 1, 1, 2, 1, 2, 3, 2, 3]
def baseStart_2825886 : Nat := 118140960795 + 2825886 * 2 ^ 59
def prefixEnd_2825886 : Nat := 4983230072969 + 3 ^ 40 * 2825886 * 2
def baseEnd_2825886 : Nat := 1451037792811435941728993

theorem tailTrace_2825886 : CollatzResearch.WordTrace tailWord_2825886 prefixEnd_2825886 1451037792811435941728993 := by
  unfold tailWord_2825886
  simp only [CollatzResearch.WordTrace]
  refine ⟨12883566230038139968792189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68712353226870079833558341 12883566230038139968792189)
  ·
    refine ⟨4831337336264302488297071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12883566230038139968792189 4831337336264302488297071)
    ·
      refine ⟨7247006004396453732445607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4831337336264302488297071 7247006004396453732445607)
      ·
        refine ⟨10870509006594680598668411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7247006004396453732445607 10870509006594680598668411)
        ·
          refine ⟨16305763509892020898002617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10870509006594680598668411 16305763509892020898002617)
          ·
            refine ⟨12229322632419015673501963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16305763509892020898002617 12229322632419015673501963)
            ·
              refine ⟨18343983948628523510252945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12229322632419015673501963 18343983948628523510252945)
              ·
                refine ⟨13757987961471392632689709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18343983948628523510252945 13757987961471392632689709)
                ·
                  refine ⟨5159245485551772237258641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13757987961471392632689709 5159245485551772237258641)
                  ·
                    refine ⟨3869434114163829177943981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5159245485551772237258641 3869434114163829177943981)
                    ·
                      refine ⟨1451037792811435941728993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3869434114163829177943981 1451037792811435941728993)
                      ·
                        rfl

theorem cell23_2825886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_2825886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825886 prefixEnd_2825886 := by exact prefixLift 2825886
  have htrace : WordTrace (prefixWord ++ tailWord_2825886) baseStart_2825886 baseEnd_2825886 := by
    simpa [prefixWord, tailWord_2825886, baseEnd_2825886] using wordTrace_append hprefix tailTrace_2825886
  have hstable : (prefixWord ++ tailWord_2825886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825886).length < 2 ^ (prefixWord ++ tailWord_2825886).sum := by decide
  have hdescent : baseEnd_2825886 < baseStart_2825886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825889 : List Nat := [1, 2, 3, 3, 2, 3, 1, 8]
def baseStart_2825889 : Nat := 118140960795 + 2825889 * 2 ^ 59
def prefixEnd_2825889 : Nat := 4983230072969 + 3 ^ 40 * 2825889 * 2
def baseEnd_2825889 : Nat := 53742197527903682592277

theorem tailTrace_2825889 : CollatzResearch.WordTrace tailWord_2825889 prefixEnd_2825889 53742197527903682592277 := by
  unfold tailWord_2825889
  simp only [CollatzResearch.WordTrace]
  refine ⟨103068639259294251262696721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68712426172862834175131147 103068639259294251262696721)
  ·
    refine ⟨77301479444470688447022541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103068639259294251262696721 77301479444470688447022541)
    ·
      refine ⟨28988054791676508167633453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77301479444470688447022541 28988054791676508167633453)
      ·
        refine ⟨10870520546878690562862545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28988054791676508167633453 10870520546878690562862545)
        ·
          refine ⟨8152890410159017922146909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10870520546878690562862545 8152890410159017922146909)
          ·
            refine ⟨3057333903809631720805091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8152890410159017922146909 3057333903809631720805091)
            ·
              refine ⟨4586000855714447581207637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3057333903809631720805091 4586000855714447581207637)
              ·
                refine ⟨53742197527903682592277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4586000855714447581207637 53742197527903682592277)
                ·
                  rfl

theorem cell23_2825889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 8].length) (baseStart_2825889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825889 prefixEnd_2825889 := by exact prefixLift 2825889
  have htrace : WordTrace (prefixWord ++ tailWord_2825889) baseStart_2825889 baseEnd_2825889 := by
    simpa [prefixWord, tailWord_2825889, baseEnd_2825889] using wordTrace_append hprefix tailTrace_2825889
  have hstable : (prefixWord ++ tailWord_2825889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825889).length < 2 ^ (prefixWord ++ tailWord_2825889).sum := by decide
  have hdescent : baseEnd_2825889 < baseStart_2825889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2825979 : List Nat := [1, 1, 1, 1, 1, 3, 1, 9, 5]
def baseStart_2825979 : Nat := 118140960795 + 2825979 * 2 ^ 59
def prefixEnd_2825979 : Nat := 4983230072969 + 3 ^ 40 * 2825979 * 2
def baseEnd_2825979 : Nat := 161231727390256008651785

theorem tailTrace_2825979 : CollatzResearch.WordTrace tailWord_2825979 prefixEnd_2825979 161231727390256008651785 := by
  unfold tailWord_2825979
  simp only [CollatzResearch.WordTrace]
  refine ⟨103071921828968196633472991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68714614552645464422315327 103071921828968196633472991)
  ·
    refine ⟨154607882743452294950209487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103071921828968196633472991 154607882743452294950209487)
    ·
      refine ⟨231911824115178442425314231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154607882743452294950209487 231911824115178442425314231)
      ·
        refine ⟨347867736172767663637971347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231911824115178442425314231 347867736172767663637971347)
        ·
          refine ⟨521801604259151495456957021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347867736172767663637971347 521801604259151495456957021)
          ·
            refine ⟨195675601597181810796358883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 521801604259151495456957021 195675601597181810796358883)
            ·
              refine ⟨293513402395772716194538325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195675601597181810796358883 293513402395772716194538325)
              ·
                refine ⟨1719805092162730758952373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 293513402395772716194538325 1719805092162730758952373)
                ·
                  refine ⟨161231727390256008651785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1719805092162730758952373 161231727390256008651785)
                  ·
                    rfl

theorem cell23_2825979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 9, 5].length) (baseStart_2825979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2825979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2825979 prefixEnd_2825979 := by exact prefixLift 2825979
  have htrace : WordTrace (prefixWord ++ tailWord_2825979) baseStart_2825979 baseEnd_2825979 := by
    simpa [prefixWord, tailWord_2825979, baseEnd_2825979] using wordTrace_append hprefix tailTrace_2825979
  have hstable : (prefixWord ++ tailWord_2825979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2825979).length < 2 ^ (prefixWord ++ tailWord_2825979).sum := by decide
  have hdescent : baseEnd_2825979 < baseStart_2825979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2825979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826007 : List Nat := [1, 1, 3, 4, 2, 3, 2, 1, 2, 2, 2]
def baseStart_2826007 : Nat := 118140960795 + 2826007 * 2 ^ 59
def prefixEnd_2826007 : Nat := 4983230072969 + 3 ^ 40 * 2826007 * 2
def baseEnd_2826007 : Nat := 1451099923970629968315937

theorem tailTrace_2826007 : CollatzResearch.WordTrace tailWord_2826007 prefixEnd_2826007 1451099923970629968315937 := by
  unfold tailWord_2826007
  simp only [CollatzResearch.WordTrace]
  refine ⟨103072943072866757415492275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68715295381911171610328183 103072943072866757415492275)
  ·
    refine ⟨154609414609300136123238413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103072943072866757415492275 154609414609300136123238413)
    ·
      refine ⟨57978530478487551046214405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154609414609300136123238413 57978530478487551046214405)
      ·
        refine ⟨10870974464716415821165201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57978530478487551046214405 10870974464716415821165201)
        ·
          refine ⟨8153230848537311865873901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10870974464716415821165201 8153230848537311865873901)
          ·
            refine ⟨3057461568201491949702713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8153230848537311865873901 3057461568201491949702713)
            ·
              refine ⟨2293096176151118962277035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3057461568201491949702713 2293096176151118962277035)
              ·
                refine ⟨3439644264226678443415553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2293096176151118962277035 3439644264226678443415553)
                ·
                  refine ⟨2579733198170008832561665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3439644264226678443415553 2579733198170008832561665)
                  ·
                    refine ⟨1934799898627506624421249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2579733198170008832561665 1934799898627506624421249)
                    ·
                      refine ⟨1451099923970629968315937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1934799898627506624421249 1451099923970629968315937)
                      ·
                        rfl

theorem cell23_2826007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_2826007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826007 prefixEnd_2826007 := by exact prefixLift 2826007
  have htrace : WordTrace (prefixWord ++ tailWord_2826007) baseStart_2826007 baseEnd_2826007 := by
    simpa [prefixWord, tailWord_2826007, baseEnd_2826007] using wordTrace_append hprefix tailTrace_2826007
  have hstable : (prefixWord ++ tailWord_2826007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826007).length < 2 ^ (prefixWord ++ tailWord_2826007).sum := by decide
  have hdescent : baseEnd_2826007 < baseStart_2826007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826032 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 9]
def baseStart_2826032 : Nat := 118140960795 + 2826032 * 2 ^ 59
def prefixEnd_2826032 : Nat := 4983230072969 + 3 ^ 40 * 2826032 * 2
def baseEnd_2826032 : Nat := 1451112760986992370503321

theorem tailTrace_2826032 : CollatzResearch.WordTrace tailWord_2826032 prefixEnd_2826032 1451112760986992370503321 := by
  unfold tailWord_2826032
  simp only [CollatzResearch.WordTrace]
  refine ⟨51536927448888093342576175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68715903265184124456768233 51536927448888093342576175)
  ·
    refine ⟨77305391173332140013864263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51536927448888093342576175 77305391173332140013864263)
    ·
      refine ⟨115958086759998210020796395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77305391173332140013864263 115958086759998210020796395)
      ·
        refine ⟨173937130139997315031194593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115958086759998210020796395 173937130139997315031194593)
        ·
          refine ⟨130452847604997986273395945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173937130139997315031194593 130452847604997986273395945)
          ·
            refine ⟨97839635703748489705046959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130452847604997986273395945 97839635703748489705046959)
            ·
              refine ⟨146759453555622734557570439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97839635703748489705046959 146759453555622734557570439)
              ·
                refine ⟨220139180333434101836355659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146759453555622734557570439 220139180333434101836355659)
                ·
                  refine ⟨330208770500151152754533489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220139180333434101836355659 330208770500151152754533489)
                  ·
                    refine ⟨247656577875113364565900117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 330208770500151152754533489 247656577875113364565900117)
                    ·
                      refine ⟨1451112760986992370503321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 247656577875113364565900117 1451112760986992370503321)
                      ·
                        rfl

theorem cell23_2826032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 9].length) (baseStart_2826032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826032 prefixEnd_2826032 := by exact prefixLift 2826032
  have htrace : WordTrace (prefixWord ++ tailWord_2826032) baseStart_2826032 baseEnd_2826032 := by
    simpa [prefixWord, tailWord_2826032, baseEnd_2826032] using wordTrace_append hprefix tailTrace_2826032
  have hstable : (prefixWord ++ tailWord_2826032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826032).length < 2 ^ (prefixWord ++ tailWord_2826032).sum := by decide
  have hdescent : baseEnd_2826032 < baseStart_2826032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826036 : List Nat := [2, 5, 1, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_2826036 : Nat := 118140960795 + 2826036 * 2 ^ 59
def prefixEnd_2826036 : Nat := 4983230072969 + 3 ^ 40 * 2826036 * 2
def baseEnd_2826036 : Nat := 1451114814909610354853303

theorem tailTrace_2826036 : CollatzResearch.WordTrace tailWord_2826036 prefixEnd_2826036 1451114814909610354853303 := by
  unfold tailWord_2826036
  simp only [CollatzResearch.WordTrace]
  refine ⟨51537000394880847684148981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68716000526507796912198641 51537000394880847684148981)
  ·
    refine ⟨4831593787020079470388967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51537000394880847684148981 4831593787020079470388967)
    ·
      refine ⟨7247390680530119205583451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4831593787020079470388967 7247390680530119205583451)
      ·
        refine ⟨10871086020795178808375177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7247390680530119205583451 10871086020795178808375177)
        ·
          refine ⟨8153314515596384106281383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10871086020795178808375177 8153314515596384106281383)
          ·
            refine ⟨12229971773394576159422075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8153314515596384106281383 12229971773394576159422075)
            ·
              refine ⟨18344957660091864239133113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12229971773394576159422075 18344957660091864239133113)
              ·
                refine ⟨13758718245068898179349835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18344957660091864239133113 13758718245068898179349835)
                ·
                  refine ⟨20638077367603347269024753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13758718245068898179349835 20638077367603347269024753)
                  ·
                    refine ⟨15478558025702510451768565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20638077367603347269024753 15478558025702510451768565)
                    ·
                      refine ⟨1451114814909610354853303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15478558025702510451768565 1451114814909610354853303)
                      ·
                        rfl

theorem cell23_2826036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_2826036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826036 prefixEnd_2826036 := by exact prefixLift 2826036
  have htrace : WordTrace (prefixWord ++ tailWord_2826036) baseStart_2826036 baseEnd_2826036 := by
    simpa [prefixWord, tailWord_2826036, baseEnd_2826036] using wordTrace_append hprefix tailTrace_2826036
  have hstable : (prefixWord ++ tailWord_2826036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826036).length < 2 ^ (prefixWord ++ tailWord_2826036).sum := by decide
  have hdescent : baseEnd_2826036 < baseStart_2826036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826039 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 7, 4]
def baseStart_2826039 : Nat := 118140960795 + 2826039 * 2 ^ 59
def prefixEnd_2826039 : Nat := 4983230072969 + 3 ^ 40 * 2826039 * 2
def baseEnd_2826039 : Nat := 483705451783857947705263

theorem tailTrace_2826039 : CollatzResearch.WordTrace tailWord_2826039 prefixEnd_2826039 483705451783857947705263 := by
  unfold tailWord_2826039
  simp only [CollatzResearch.WordTrace]
  refine ⟨103074110208750826880657171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68716073472500551253771447 103074110208750826880657171)
  ·
    refine ⟨154611165313126240320985757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103074110208750826880657171 154611165313126240320985757)
    ·
      refine ⟨57979186992422340120369659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154611165313126240320985757 57979186992422340120369659)
      ·
        refine ⟨86968780488633510180554489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57979186992422340120369659 86968780488633510180554489)
        ·
          refine ⟨65226585366475132635415867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86968780488633510180554489 65226585366475132635415867)
          ·
            refine ⟨97839878049712698953123801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65226585366475132635415867 97839878049712698953123801)
            ·
              refine ⟨73379908537284524214842851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97839878049712698953123801 73379908537284524214842851)
              ·
                refine ⟨110069862805926786322264277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73379908537284524214842851 110069862805926786322264277)
                ·
                  refine ⟨2579762409513909054428069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 110069862805926786322264277 2579762409513909054428069)
                  ·
                    refine ⟨483705451783857947705263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2579762409513909054428069 483705451783857947705263)
                    ·
                      rfl

theorem cell23_2826039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 7, 4].length) (baseStart_2826039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826039 prefixEnd_2826039 := by exact prefixLift 2826039
  have htrace : WordTrace (prefixWord ++ tailWord_2826039) baseStart_2826039 baseEnd_2826039 := by
    simpa [prefixWord, tailWord_2826039, baseEnd_2826039] using wordTrace_append hprefix tailTrace_2826039
  have hstable : (prefixWord ++ tailWord_2826039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826039).length < 2 ^ (prefixWord ++ tailWord_2826039).sum := by decide
  have hdescent : baseEnd_2826039 < baseStart_2826039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826096 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 7, 1, 3]
def baseStart_2826096 : Nat := 118140960795 + 2826096 * 2 ^ 59
def prefixEnd_2826096 : Nat := 4983230072969 + 3 ^ 40 * 2826096 * 2
def baseEnd_2826096 : Nat := 1451145623748880120103027

theorem tailTrace_2826096 : CollatzResearch.WordTrace tailWord_2826096 prefixEnd_2826096 1451145623748880120103027 := by
  unfold tailWord_2826096
  simp only [CollatzResearch.WordTrace]
  refine ⟨51538094584772162807741071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68717459446362883743654761 51538094584772162807741071)
  ·
    refine ⟨77307141877158244211611607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51538094584772162807741071 77307141877158244211611607)
    ·
      refine ⟨115960712815737366317417411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77307141877158244211611607 115960712815737366317417411)
      ·
        refine ⟨173941069223606049476126117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115960712815737366317417411 173941069223606049476126117)
        ·
          refine ⟨32613950479426134276773647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173941069223606049476126117 32613950479426134276773647)
          ·
            refine ⟨48920925719139201415160471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32613950479426134276773647 48920925719139201415160471)
            ·
              refine ⟨73381388578708802122740707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48920925719139201415160471 73381388578708802122740707)
              ·
                refine ⟨110072082868063203184111061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73381388578708802122740707 110072082868063203184111061)
                ·
                  refine ⟨2579814442220231324627603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 110072082868063203184111061 2579814442220231324627603)
                  ·
                    refine ⟨3869721663330346986941405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2579814442220231324627603 3869721663330346986941405)
                    ·
                      refine ⟨1451145623748880120103027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3869721663330346986941405 1451145623748880120103027)
                      ·
                        rfl

theorem cell23_2826096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 7, 1, 3].length) (baseStart_2826096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826096 prefixEnd_2826096 := by exact prefixLift 2826096
  have htrace : WordTrace (prefixWord ++ tailWord_2826096) baseStart_2826096 baseEnd_2826096 := by
    simpa [prefixWord, tailWord_2826096, baseEnd_2826096] using wordTrace_append hprefix tailTrace_2826096
  have hstable : (prefixWord ++ tailWord_2826096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826096).length < 2 ^ (prefixWord ++ tailWord_2826096).sum := by decide
  have hdescent : baseEnd_2826096 < baseStart_2826096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826130 : List Nat := [3, 2, 3, 2, 1, 1, 2, 2, 3, 1, 3]
def baseStart_2826130 : Nat := 118140960795 + 2826130 * 2 ^ 59
def prefixEnd_2826130 : Nat := 4983230072969 + 3 ^ 40 * 2826130 * 2
def baseEnd_2826130 : Nat := 1451163082091132987077871

theorem tailTrace_2826130 : CollatzResearch.WordTrace tailWord_2826130 prefixEnd_2826130 1451163082091132987077871 := by
  unfold tailWord_2826130
  simp only [CollatzResearch.WordTrace]
  refine ⟨25769357312855287355554961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68718286167614099614813229 25769357312855287355554961)
  ·
    refine ⟨19327017984641465516666221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25769357312855287355554961 19327017984641465516666221)
    ·
      refine ⟨7247631744240549568749833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19327017984641465516666221 7247631744240549568749833)
      ·
        refine ⟨5435723808180412176562375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7247631744240549568749833 5435723808180412176562375)
        ·
          refine ⟨8153585712270618264843563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5435723808180412176562375 8153585712270618264843563)
          ·
            refine ⟨12230378568405927397265345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8153585712270618264843563 12230378568405927397265345)
            ·
              refine ⟨9172783926304445547949009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12230378568405927397265345 9172783926304445547949009)
              ·
                refine ⟨6879587944728334160961757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9172783926304445547949009 6879587944728334160961757)
                ·
                  refine ⟨2579845479273125310360659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6879587944728334160961757 2579845479273125310360659)
                  ·
                    refine ⟨3869768218909687965540989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2579845479273125310360659 3869768218909687965540989)
                    ·
                      refine ⟨1451163082091132987077871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3869768218909687965540989 1451163082091132987077871)
                      ·
                        rfl

theorem cell23_2826130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_2826130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826130 prefixEnd_2826130 := by exact prefixLift 2826130
  have htrace : WordTrace (prefixWord ++ tailWord_2826130) baseStart_2826130 baseEnd_2826130 := by
    simpa [prefixWord, tailWord_2826130, baseEnd_2826130] using wordTrace_append hprefix tailTrace_2826130
  have hstable : (prefixWord ++ tailWord_2826130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826130).length < 2 ^ (prefixWord ++ tailWord_2826130).sum := by decide
  have hdescent : baseEnd_2826130 < baseStart_2826130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826164 : List Nat := [2, 5, 2, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_2826164 : Nat := 118140960795 + 2826164 * 2 ^ 59
def prefixEnd_2826164 : Nat := 4983230072969 + 3 ^ 40 * 2826164 * 2
def baseEnd_2826164 : Nat := 1451180540433385854052715

theorem tailTrace_2826164 : CollatzResearch.WordTrace tailWord_2826164 prefixEnd_2826164 1451180540433385854052715 := by
  unfold tailWord_2826164
  simp only [CollatzResearch.WordTrace]
  refine ⟨51539334666648986614478773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68719112888865315485971697 51539334666648986614478773)
  ·
    refine ⟨4831812624998342495107385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51539334666648986614478773 4831812624998342495107385)
    ·
      refine ⟨3623859468748756871330539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4831812624998342495107385 3623859468748756871330539)
      ·
        refine ⟨5435789203123135306995809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3623859468748756871330539 5435789203123135306995809)
        ·
          refine ⟨4076841902342351480246857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5435789203123135306995809 4076841902342351480246857)
          ·
            refine ⟨3057631426756763610185143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4076841902342351480246857 3057631426756763610185143)
            ·
              refine ⟨4586447140135145415277715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3057631426756763610185143 4586447140135145415277715)
              ·
                refine ⟨6879670710202718122916573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4586447140135145415277715 6879670710202718122916573)
                ·
                  refine ⟨2579876516326019296093715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6879670710202718122916573 2579876516326019296093715)
                  ·
                    refine ⟨3869814774489028944140573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2579876516326019296093715 3869814774489028944140573)
                    ·
                      refine ⟨1451180540433385854052715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3869814774489028944140573 1451180540433385854052715)
                      ·
                        rfl

theorem cell23_2826164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_2826164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826164 prefixEnd_2826164 := by exact prefixLift 2826164
  have htrace : WordTrace (prefixWord ++ tailWord_2826164) baseStart_2826164 baseEnd_2826164 := by
    simpa [prefixWord, tailWord_2826164, baseEnd_2826164] using wordTrace_append hprefix tailTrace_2826164
  have hstable : (prefixWord ++ tailWord_2826164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826164).length < 2 ^ (prefixWord ++ tailWord_2826164).sum := by decide
  have hdescent : baseEnd_2826164 < baseStart_2826164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826219 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 3, 8]
def baseStart_2826219 : Nat := 118140960795 + 2826219 * 2 ^ 59
def prefixEnd_2826219 : Nat := 4983230072969 + 3 ^ 40 * 2826219 * 2
def baseEnd_2826219 : Nat := 483736260623127712954987

theorem tailTrace_2826219 : CollatzResearch.WordTrace tailWord_2826219 prefixEnd_2826219 483736260623127712954987 := by
  unfold tailWord_2826219
  simp only [CollatzResearch.WordTrace]
  refine ⟨103080675348098717622209711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68720450232065811748139807 103080675348098717622209711)
  ·
    refine ⟨154621013022148076433314567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103080675348098717622209711 154621013022148076433314567)
    ·
      refine ⟨231931519533222114649971851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154621013022148076433314567 231931519533222114649971851)
      ·
        refine ⟨347897279299833171974957777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231931519533222114649971851 347897279299833171974957777)
        ·
          refine ⟨260922959474874878981218333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347897279299833171974957777 260922959474874878981218333)
          ·
            refine ⟨97846109803078079617956875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 260922959474874878981218333 97846109803078079617956875)
            ·
              refine ⟨146769164704617119426935313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97846109803078079617956875 146769164704617119426935313)
              ·
                refine ⟨110076873528462839570201485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146769164704617119426935313 110076873528462839570201485)
                ·
                  refine ⟨41278827573173564838825557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110076873528462839570201485 41278827573173564838825557)
                  ·
                    refine ⟨483736260623127712954987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41278827573173564838825557 483736260623127712954987)
                    ·
                      rfl

theorem cell23_2826219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 8].length) (baseStart_2826219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826219 prefixEnd_2826219 := by exact prefixLift 2826219
  have htrace : WordTrace (prefixWord ++ tailWord_2826219) baseStart_2826219 baseEnd_2826219 := by
    simpa [prefixWord, tailWord_2826219, baseEnd_2826219] using wordTrace_append hprefix tailTrace_2826219
  have hstable : (prefixWord ++ tailWord_2826219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826219).length < 2 ^ (prefixWord ++ tailWord_2826219).sum := by decide
  have hdescent : baseEnd_2826219 < baseStart_2826219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826221 : List Nat := [1, 5, 1, 4, 1, 1, 1, 4, 1, 2, 2]
def baseStart_2826221 : Nat := 118140960795 + 2826221 * 2 ^ 59
def prefixEnd_2826221 : Nat := 4983230072969 + 3 ^ 40 * 2826221 * 2
def baseEnd_2826221 : Nat := 1451209808830692131039953

theorem tailTrace_2826221 : CollatzResearch.WordTrace tailWord_2826221 prefixEnd_2826221 1451209808830692131039953 := by
  unfold tailWord_2826221
  simp only [CollatzResearch.WordTrace]
  refine ⟨103080748294091471963782517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68720498862727647975855011 103080748294091471963782517)
  ·
    refine ⟨9663820152571075496604611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103080748294091471963782517 9663820152571075496604611)
    ·
      refine ⟨14495730228856613244906917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9663820152571075496604611 14495730228856613244906917)
      ·
        refine ⟨2717949417910614983420047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14495730228856613244906917 2717949417910614983420047)
        ·
          refine ⟨4076924126865922475130071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2717949417910614983420047 4076924126865922475130071)
          ·
            refine ⟨6115386190298883712695107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4076924126865922475130071 6115386190298883712695107)
            ·
              refine ⟨9173079285448325569042661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6115386190298883712695107 9173079285448325569042661)
              ·
                refine ⟨1719952366021561044195499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9173079285448325569042661 1719952366021561044195499)
                ·
                  refine ⟨2579928549032341566293249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1719952366021561044195499 2579928549032341566293249)
                  ·
                    refine ⟨1934946411774256174719937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2579928549032341566293249 1934946411774256174719937)
                    ·
                      refine ⟨1451209808830692131039953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1934946411774256174719937 1451209808830692131039953)
                      ·
                        rfl

theorem cell23_2826221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_2826221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826221 prefixEnd_2826221 := by exact prefixLift 2826221
  have htrace : WordTrace (prefixWord ++ tailWord_2826221) baseStart_2826221 baseEnd_2826221 := by
    simpa [prefixWord, tailWord_2826221, baseEnd_2826221] using wordTrace_append hprefix tailTrace_2826221
  have hstable : (prefixWord ++ tailWord_2826221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826221).length < 2 ^ (prefixWord ++ tailWord_2826221).sum := by decide
  have hdescent : baseEnd_2826221 < baseStart_2826221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826236 : List Nat := [2, 2, 2, 1, 2, 2, 3, 1, 2, 6]
def baseStart_2826236 : Nat := 118140960795 + 2826236 * 2 ^ 59
def prefixEnd_2826236 : Nat := 4983230072969 + 3 ^ 40 * 2826236 * 2
def baseEnd_2826236 : Nat := 483739170346836524117461

theorem tailTrace_2826236 : CollatzResearch.WordTrace tailWord_2826236 prefixEnd_2826236 483739170346836524117461 := by
  unfold tailWord_2826236
  simp only [CollatzResearch.WordTrace]
  refine ⟨51540647694518564762789281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68720863592691419683719041 51540647694518564762789281)
  ·
    refine ⟨38655485770888923572091961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51540647694518564762789281 38655485770888923572091961)
    ·
      refine ⟨28991614328166692679068971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38655485770888923572091961 28991614328166692679068971)
      ·
        refine ⟨43487421492250039018603457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28991614328166692679068971 43487421492250039018603457)
        ·
          refine ⟨32615566119187529263952593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43487421492250039018603457 32615566119187529263952593)
          ·
            refine ⟨24461674589390646947964445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32615566119187529263952593 24461674589390646947964445)
            ·
              refine ⟨9173127971021492605486667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24461674589390646947964445 9173127971021492605486667)
              ·
                refine ⟨13759691956532238908230001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9173127971021492605486667 13759691956532238908230001)
                ·
                  refine ⟨10319768967399179181172501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13759691956532238908230001 10319768967399179181172501)
                  ·
                    refine ⟨483739170346836524117461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10319768967399179181172501 483739170346836524117461)
                    ·
                      rfl

theorem cell23_2826236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_2826236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826236 prefixEnd_2826236 := by exact prefixLift 2826236
  have htrace : WordTrace (prefixWord ++ tailWord_2826236) baseStart_2826236 baseEnd_2826236 := by
    simpa [prefixWord, tailWord_2826236, baseEnd_2826236] using wordTrace_append hprefix tailTrace_2826236
  have hstable : (prefixWord ++ tailWord_2826236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826236).length < 2 ^ (prefixWord ++ tailWord_2826236).sum := by decide
  have hdescent : baseEnd_2826236 < baseStart_2826236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826277 : List Nat := [1, 3, 1, 2, 2, 3, 3, 2, 2, 2, 2]
def baseStart_2826277 : Nat := 118140960795 + 2826277 * 2 ^ 59
def prefixEnd_2826277 : Nat := 4983230072969 + 3 ^ 40 * 2826277 * 2
def baseEnd_2826277 : Nat := 1451238563747343911939695

theorem tailTrace_2826277 : CollatzResearch.WordTrace tailWord_2826277 prefixEnd_2826277 1451238563747343911939695 := by
  unfold tailWord_2826277
  simp only [CollatzResearch.WordTrace]
  refine ⟨103082790781888593527821085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68721860521259062351880723 103082790781888593527821085)
  ·
    refine ⟨38656046543208222572932907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103082790781888593527821085 38656046543208222572932907)
    ·
      refine ⟨57984069814812333859399361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38656046543208222572932907 57984069814812333859399361)
      ·
        refine ⟨43488052361109250394549521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57984069814812333859399361 43488052361109250394549521)
        ·
          refine ⟨32616039270831937795912141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43488052361109250394549521 32616039270831937795912141)
          ·
            refine ⟨12231014726561976673467053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32616039270831937795912141 12231014726561976673467053)
            ·
              refine ⟨4586630522460741252550145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12231014726561976673467053 4586630522460741252550145)
              ·
                refine ⟨3439972891845555939412609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4586630522460741252550145 3439972891845555939412609)
                ·
                  refine ⟨2579979668884166954559457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3439972891845555939412609 2579979668884166954559457)
                  ·
                    refine ⟨1934984751663125215919593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2579979668884166954559457 1934984751663125215919593)
                    ·
                      refine ⟨1451238563747343911939695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1934984751663125215919593 1451238563747343911939695)
                      ·
                        rfl

theorem cell23_2826277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 2, 2, 2].length) (baseStart_2826277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826277 prefixEnd_2826277 := by exact prefixLift 2826277
  have htrace : WordTrace (prefixWord ++ tailWord_2826277) baseStart_2826277 baseEnd_2826277 := by
    simpa [prefixWord, tailWord_2826277, baseEnd_2826277] using wordTrace_append hprefix tailTrace_2826277
  have hstable : (prefixWord ++ tailWord_2826277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826277).length < 2 ^ (prefixWord ++ tailWord_2826277).sum := by decide
  have hdescent : baseEnd_2826277 < baseStart_2826277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826293 : List Nat := [1, 3, 3, 1, 1, 1, 4, 1, 2, 3, 3]
def baseStart_2826293 : Nat := 118140960795 + 2826293 * 2 ^ 59
def prefixEnd_2826293 : Nat := 4983230072969 + 3 ^ 40 * 2826293 * 2
def baseEnd_2826293 : Nat := 1451246779437815849339621

theorem tailTrace_2826293 : CollatzResearch.WordTrace tailWord_2826293 prefixEnd_2826293 1451246779437815849339621 := by
  unfold tailWord_2826293
  simp only [CollatzResearch.WordTrace]
  refine ⟨103083374349830628260403533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68722249566553752173602355 103083374349830628260403533)
  ·
    refine ⟨38656265381186485597651325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103083374349830628260403533 38656265381186485597651325)
    ·
      refine ⟨14496099517944932099119247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38656265381186485597651325 14496099517944932099119247)
      ·
        refine ⟨21744149276917398148678871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14496099517944932099119247 21744149276917398148678871)
        ·
          refine ⟨32616223915376097223018307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21744149276917398148678871 32616223915376097223018307)
          ·
            refine ⟨48924335873064145834527461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32616223915376097223018307 48924335873064145834527461)
            ·
              refine ⟨9173312976199527343973899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48924335873064145834527461 9173312976199527343973899)
              ·
                refine ⟨13759969464299291015960849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9173312976199527343973899 13759969464299291015960849)
                ·
                  refine ⟨10319977098224468261970637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13759969464299291015960849 10319977098224468261970637)
                  ·
                    refine ⟨3869991411834175598238989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10319977098224468261970637 3869991411834175598238989)
                    ·
                      refine ⟨1451246779437815849339621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3869991411834175598238989 1451246779437815849339621)
                      ·
                        rfl

theorem cell23_2826293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_2826293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826293 prefixEnd_2826293 := by exact prefixLift 2826293
  have htrace : WordTrace (prefixWord ++ tailWord_2826293) baseStart_2826293 baseEnd_2826293 := by
    simpa [prefixWord, tailWord_2826293, baseEnd_2826293] using wordTrace_append hprefix tailTrace_2826293
  have hstable : (prefixWord ++ tailWord_2826293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826293).length < 2 ^ (prefixWord ++ tailWord_2826293).sum := by decide
  have hdescent : baseEnd_2826293 < baseStart_2826293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826303 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 2, 5, 2]
def baseStart_2826303 : Nat := 118140960795 + 2826303 * 2 ^ 59
def prefixEnd_2826303 : Nat := 4983230072969 + 3 ^ 40 * 2826303 * 2
def baseEnd_2826303 : Nat := 1451251914244360810214575

theorem tailTrace_2826303 : CollatzResearch.WordTrace tailWord_2826303 prefixEnd_2826303 1451251914244360810214575 := by
  unfold tailWord_2826303
  simp only [CollatzResearch.WordTrace]
  refine ⟨103083739079794399968267563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68722492719862933312178375 103083739079794399968267563)
  ·
    refine ⟨154625608619691599952401345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103083739079794399968267563 154625608619691599952401345)
    ·
      refine ⟨115969206464768699964301009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154625608619691599952401345 115969206464768699964301009)
      ·
        refine ⟨86976904848576524973225757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115969206464768699964301009 86976904848576524973225757)
        ·
          refine ⟨32616339318216196864959659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86976904848576524973225757 32616339318216196864959659)
          ·
            refine ⟨48924508977324295297439489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32616339318216196864959659 48924508977324295297439489)
            ·
              refine ⟨36693381732993221473079617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48924508977324295297439489 36693381732993221473079617)
              ·
                refine ⟨27520036299744916104809713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36693381732993221473079617 27520036299744916104809713)
                ·
                  refine ⟨20640027224808687078607285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27520036299744916104809713 20640027224808687078607285)
                  ·
                    refine ⟨1935002552325814413619433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20640027224808687078607285 1935002552325814413619433)
                    ·
                      refine ⟨1451251914244360810214575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1935002552325814413619433 1451251914244360810214575)
                      ·
                        rfl

theorem cell23_2826303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 5, 2].length) (baseStart_2826303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826303 prefixEnd_2826303 := by exact prefixLift 2826303
  have htrace : WordTrace (prefixWord ++ tailWord_2826303) baseStart_2826303 baseEnd_2826303 := by
    simpa [prefixWord, tailWord_2826303, baseEnd_2826303] using wordTrace_append hprefix tailTrace_2826303
  have hstable : (prefixWord ++ tailWord_2826303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826303).length < 2 ^ (prefixWord ++ tailWord_2826303).sum := by decide
  have hdescent : baseEnd_2826303 < baseStart_2826303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826334 : List Nat := [4, 4, 1, 1, 2, 2, 1, 1, 7]
def baseStart_2826334 : Nat := 118140960795 + 2826334 * 2 ^ 59
def prefixEnd_2826334 : Nat := 4983230072969 + 3 ^ 40 * 2826334 * 2
def baseEnd_2826334 : Nat := 161251981349405576547437

theorem tailTrace_2826334 : CollatzResearch.WordTrace tailWord_2826334 prefixEnd_2826334 161251981349405576547437 := by
  unfold tailWord_2826334
  simp only [CollatzResearch.WordTrace]
  refine ⟨12885608717835261532830757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68723246495121394841764037 12885608717835261532830757)
  ·
    refine ⟨2416051634594111537405767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12885608717835261532830757 2416051634594111537405767)
    ·
      refine ⟨3624077451891167306108651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2416051634594111537405767 3624077451891167306108651)
      ·
        refine ⟨5436116177836750959162977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3624077451891167306108651 5436116177836750959162977)
        ·
          refine ⟨4077087133377563219372233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5436116177836750959162977 4077087133377563219372233)
          ·
            refine ⟨3057815350033172414529175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4077087133377563219372233 3057815350033172414529175)
            ·
              refine ⟨4586723025049758621793763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3057815350033172414529175 4586723025049758621793763)
              ·
                refine ⟨6880084537574637932690645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4586723025049758621793763 6880084537574637932690645)
                ·
                  refine ⟨161251981349405576547437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6880084537574637932690645 161251981349405576547437)
                  ·
                    rfl

theorem cell23_2826334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_2826334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826334 prefixEnd_2826334 := by exact prefixLift 2826334
  have htrace : WordTrace (prefixWord ++ tailWord_2826334) baseStart_2826334 baseEnd_2826334 := by
    simpa [prefixWord, tailWord_2826334, baseEnd_2826334] using wordTrace_append hprefix tailTrace_2826334
  have hstable : (prefixWord ++ tailWord_2826334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826334).length < 2 ^ (prefixWord ++ tailWord_2826334).sum := by decide
  have hdescent : baseEnd_2826334 < baseStart_2826334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826350 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2]
def baseStart_2826350 : Nat := 118140960795 + 2826350 * 2 ^ 59
def prefixEnd_2826350 : Nat := 4983230072969 + 3 ^ 40 * 2826350 * 2
def baseEnd_2826350 : Nat := 1451276047835122126326859

theorem tailTrace_2826350 : CollatzResearch.WordTrace tailWord_2826350 prefixEnd_2826350 1451276047835122126326859 := by
  unfold tailWord_2826350
  simp only [CollatzResearch.WordTrace]
  refine ⟨12885681663828015874403563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68723635540416084663485669 12885681663828015874403563)
  ·
    refine ⟨19328522495742023811605345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12885681663828015874403563 19328522495742023811605345)
    ·
      refine ⟨14496391871806517858704009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19328522495742023811605345 14496391871806517858704009)
      ·
        refine ⟨10872293903854888394028007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14496391871806517858704009 10872293903854888394028007)
        ·
          refine ⟨16308440855782332591042011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10872293903854888394028007 16308440855782332591042011)
          ·
            refine ⟨24462661283673498886563017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16308440855782332591042011 24462661283673498886563017)
            ·
              refine ⟨18346995962755124164922263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24462661283673498886563017 18346995962755124164922263)
              ·
                refine ⟨27520493944132686247383395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18346995962755124164922263 27520493944132686247383395)
                ·
                  refine ⟨41280740916199029371075093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27520493944132686247383395 41280740916199029371075093)
                  ·
                    refine ⟨1935034730446829501769145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41280740916199029371075093 1935034730446829501769145)
                    ·
                      refine ⟨1451276047835122126326859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1935034730446829501769145 1451276047835122126326859)
                      ·
                        rfl

theorem cell23_2826350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_2826350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826350 prefixEnd_2826350 := by exact prefixLift 2826350
  have htrace : WordTrace (prefixWord ++ tailWord_2826350) baseStart_2826350 baseEnd_2826350 := by
    simpa [prefixWord, tailWord_2826350, baseEnd_2826350] using wordTrace_append hprefix tailTrace_2826350
  have hstable : (prefixWord ++ tailWord_2826350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826350).length < 2 ^ (prefixWord ++ tailWord_2826350).sum := by decide
  have hdescent : baseEnd_2826350 < baseStart_2826350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826353 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 4, 2, 3]
def baseStart_2826353 : Nat := 118140960795 + 2826353 * 2 ^ 59
def prefixEnd_2826353 : Nat := 4983230072969 + 3 ^ 40 * 2826353 * 2
def baseEnd_2826353 : Nat := 1451277588277085614589345

theorem tailTrace_2826353 : CollatzResearch.WordTrace tailWord_2826353 prefixEnd_2826353 1451277588277085614589345 := by
  unfold tailWord_2826353
  simp only [CollatzResearch.WordTrace]
  refine ⟨103085562729613258507587713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68723708486408839005058475 103085562729613258507587713)
  ·
    refine ⟨77314172047209943880690785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103085562729613258507587713 77314172047209943880690785)
    ·
      refine ⟨57985629035407457910518089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77314172047209943880690785 57985629035407457910518089)
      ·
        refine ⟨43489221776555593432888567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57985629035407457910518089 43489221776555593432888567)
        ·
          refine ⟨65233832664833390149332851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43489221776555593432888567 65233832664833390149332851)
          ·
            refine ⟨97850748997250085223999277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65233832664833390149332851 97850748997250085223999277)
            ·
              refine ⟨36694030873968781958999729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97850748997250085223999277 36694030873968781958999729)
              ·
                refine ⟨27520523155476586469249797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36694030873968781958999729 27520523155476586469249797)
                ·
                  refine ⟨5160098091651859962984337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27520523155476586469249797 5160098091651859962984337)
                  ·
                    refine ⟨3870073568738894972238253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5160098091651859962984337 3870073568738894972238253)
                    ·
                      refine ⟨1451277588277085614589345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3870073568738894972238253 1451277588277085614589345)
                      ·
                        rfl

theorem cell23_2826353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_2826353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826353 prefixEnd_2826353 := by exact prefixLift 2826353
  have htrace : WordTrace (prefixWord ++ tailWord_2826353) baseStart_2826353 baseEnd_2826353 := by
    simpa [prefixWord, tailWord_2826353, baseEnd_2826353] using wordTrace_append hprefix tailTrace_2826353
  have hstable : (prefixWord ++ tailWord_2826353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826353).length < 2 ^ (prefixWord ++ tailWord_2826353).sum := by decide
  have hdescent : baseEnd_2826353 < baseStart_2826353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826394 : List Nat := [3, 1, 1, 5, 2, 1, 1, 4, 1, 4]
def baseStart_2826394 : Nat := 118140960795 + 2826394 * 2 ^ 59
def prefixEnd_2826394 : Nat := 4983230072969 + 3 ^ 40 * 2826394 * 2
def baseEnd_2826394 : Nat := 483766213661306651392219

theorem tailTrace_2826394 : CollatzResearch.WordTrace tailWord_2826394 prefixEnd_2826394 483766213661306651392219 := by
  unfold tailWord_2826394
  simp only [CollatzResearch.WordTrace]
  refine ⟨25771764530616180627457559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68724705414976481673220157 25771764530616180627457559)
  ·
    refine ⟨38657646795924270941186339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25771764530616180627457559 38657646795924270941186339)
    ·
      refine ⟨57986470193886406411779509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38657646795924270941186339 57986470193886406411779509)
      ·
        refine ⟨5436231580676850601104329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57986470193886406411779509 5436231580676850601104329)
        ·
          refine ⟨4077173685507637950828247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5436231580676850601104329 4077173685507637950828247)
          ·
            refine ⟨6115760528261456926242371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4077173685507637950828247 6115760528261456926242371)
            ·
              refine ⟨9173640792392185389363557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6115760528261456926242371 9173640792392185389363557)
              ·
                refine ⟨1720057648573534760505667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9173640792392185389363557 1720057648573534760505667)
                ·
                  refine ⟨2580086472860302140758501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1720057648573534760505667 2580086472860302140758501)
                  ·
                    refine ⟨483766213661306651392219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2580086472860302140758501 483766213661306651392219)
                    ·
                      rfl

theorem cell23_2826394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 4, 1, 4].length) (baseStart_2826394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826394 prefixEnd_2826394 := by exact prefixLift 2826394
  have htrace : WordTrace (prefixWord ++ tailWord_2826394) baseStart_2826394 baseEnd_2826394 := by
    simpa [prefixWord, tailWord_2826394, baseEnd_2826394] using wordTrace_append hprefix tailTrace_2826394
  have hstable : (prefixWord ++ tailWord_2826394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826394).length < 2 ^ (prefixWord ++ tailWord_2826394).sum := by decide
  have hdescent : baseEnd_2826394 < baseStart_2826394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826421 : List Nat := [1, 3, 3, 4, 2, 1, 1, 1, 2, 2, 3]
def baseStart_2826421 : Nat := 118140960795 + 2826421 * 2 ^ 59
def prefixEnd_2826421 : Nat := 4983230072969 + 3 ^ 40 * 2826421 * 2
def baseEnd_2826421 : Nat := 1451312504961591348539033

theorem tailTrace_2826421 : CollatzResearch.WordTrace tailWord_2826421 prefixEnd_2826421 1451312504961591348539033 := by
  unfold tailWord_2826421
  simp only [CollatzResearch.WordTrace]
  refine ⟨103088042893366906121063117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68725361928911270747375411 103088042893366906121063117)
  ·
    refine ⟨38658016085012589795398669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103088042893366906121063117 38658016085012589795398669)
    ·
      refine ⟨14496756031879721173274501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38658016085012589795398669 14496756031879721173274501)
      ·
        refine ⟨2718141755977447719988969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14496756031879721173274501 2718141755977447719988969)
        ·
          refine ⟨2038606316983085789991727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2718141755977447719988969 2038606316983085789991727)
          ·
            refine ⟨3057909475474628684987591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2038606316983085789991727 3057909475474628684987591)
            ·
              refine ⟨4586864213211943027481387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3057909475474628684987591 4586864213211943027481387)
              ·
                refine ⟨6880296319817914541222081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4586864213211943027481387 6880296319817914541222081)
                ·
                  refine ⟨5160222239863435905916561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6880296319817914541222081 5160222239863435905916561)
                  ·
                    refine ⟨3870166679897576929437421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5160222239863435905916561 3870166679897576929437421)
                    ·
                      refine ⟨1451312504961591348539033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3870166679897576929437421 1451312504961591348539033)
                      ·
                        rfl

theorem cell23_2826421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_2826421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826421 prefixEnd_2826421 := by exact prefixLift 2826421
  have htrace : WordTrace (prefixWord ++ tailWord_2826421) baseStart_2826421 baseEnd_2826421 := by
    simpa [prefixWord, tailWord_2826421, baseEnd_2826421] using wordTrace_append hprefix tailTrace_2826421
  have hstable : (prefixWord ++ tailWord_2826421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826421).length < 2 ^ (prefixWord ++ tailWord_2826421).sum := by decide
  have hdescent : baseEnd_2826421 < baseStart_2826421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826443 : List Nat := [1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 5]
def baseStart_2826443 : Nat := 118140960795 + 2826443 * 2 ^ 59
def prefixEnd_2826443 : Nat := 4983230072969 + 3 ^ 40 * 2826443 * 2
def baseEnd_2826443 : Nat := 1451323801535990262463931

theorem tailTrace_2826443 : CollatzResearch.WordTrace tailWord_2826443 prefixEnd_2826443 1451323801535990262463931 := by
  unfold tailWord_2826443
  simp only [CollatzResearch.WordTrace]
  refine ⟨103088845299287203878363983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68725896866191469252242655 103088845299287203878363983)
  ·
    refine ⟨154633267948930805817545975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103088845299287203878363983 154633267948930805817545975)
    ·
      refine ⟨231949901923396208726318963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154633267948930805817545975 231949901923396208726318963)
      ·
        refine ⟨347924852885094313089478445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231949901923396208726318963 347924852885094313089478445)
        ·
          refine ⟨130471819831910367408554417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 347924852885094313089478445 130471819831910367408554417)
          ·
            refine ⟨97853864873932775556415813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130471819831910367408554417 97853864873932775556415813)
            ·
              refine ⟨18347599663862395416827965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97853864873932775556415813 18347599663862395416827965)
              ·
                refine ⟨6880349873948398281310487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18347599663862395416827965 6880349873948398281310487)
                ·
                  refine ⟨10320524810922597421965731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6880349873948398281310487 10320524810922597421965731)
                  ·
                    refine ⟨15480787216383896132948597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10320524810922597421965731 15480787216383896132948597)
                    ·
                      refine ⟨1451323801535990262463931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15480787216383896132948597 1451323801535990262463931)
                      ·
                        rfl

theorem cell23_2826443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 5].length) (baseStart_2826443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826443 prefixEnd_2826443 := by exact prefixLift 2826443
  have htrace : WordTrace (prefixWord ++ tailWord_2826443) baseStart_2826443 baseEnd_2826443 := by
    simpa [prefixWord, tailWord_2826443, baseEnd_2826443] using wordTrace_append hprefix tailTrace_2826443
  have hstable : (prefixWord ++ tailWord_2826443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826443).length < 2 ^ (prefixWord ++ tailWord_2826443).sum := by decide
  have hdescent : baseEnd_2826443 < baseStart_2826443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826457 : List Nat := [1, 2, 1, 2, 3, 1, 3, 3, 3, 2, 2]
def baseStart_2826457 : Nat := 118140960795 + 2826457 * 2 ^ 59
def prefixEnd_2826457 : Nat := 4983230072969 + 3 ^ 40 * 2826457 * 2
def baseEnd_2826457 : Nat := 1451330990265153207688867

theorem tailTrace_2826457 : CollatzResearch.WordTrace tailWord_2826457 prefixEnd_2826457 1451330990265153207688867 := by
  unfold tailWord_2826457
  simp only [CollatzResearch.WordTrace]
  refine ⟨103089355921236484269373625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68726237280824322846249083 103089355921236484269373625)
  ·
    refine ⟨77317016940927363202030219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103089355921236484269373625 77317016940927363202030219)
    ·
      refine ⟨115975525411391044803045329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77317016940927363202030219 115975525411391044803045329)
      ·
        refine ⟨86981644058543283602283997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115975525411391044803045329 86981644058543283602283997)
        ·
          refine ⟨32618116521953731350856499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86981644058543283602283997 32618116521953731350856499)
          ·
            refine ⟨48927174782930597026284749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32618116521953731350856499 48927174782930597026284749)
            ·
              refine ⟨18347690543598973884856781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48927174782930597026284749 18347690543598973884856781)
              ·
                refine ⟨6880383953849615206821293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18347690543598973884856781 6880383953849615206821293)
                ·
                  refine ⟨2580143982693605702557985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6880383953849615206821293 2580143982693605702557985)
                  ·
                    refine ⟨1935107987020204276918489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2580143982693605702557985 1935107987020204276918489)
                    ·
                      refine ⟨1451330990265153207688867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1935107987020204276918489 1451330990265153207688867)
                      ·
                        rfl

theorem cell23_2826457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 3, 2, 2].length) (baseStart_2826457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826457 prefixEnd_2826457 := by exact prefixLift 2826457
  have htrace : WordTrace (prefixWord ++ tailWord_2826457) baseStart_2826457 baseEnd_2826457 := by
    simpa [prefixWord, tailWord_2826457, baseEnd_2826457] using wordTrace_append hprefix tailTrace_2826457
  have hstable : (prefixWord ++ tailWord_2826457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826457).length < 2 ^ (prefixWord ++ tailWord_2826457).sum := by decide
  have hdescent : baseEnd_2826457 < baseStart_2826457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826507 : List Nat := [1, 1, 1, 1, 5, 2, 2, 4, 2, 1, 3]
def baseStart_2826507 : Nat := 118140960795 + 2826507 * 2 ^ 59
def prefixEnd_2826507 : Nat := 4983230072969 + 3 ^ 40 * 2826507 * 2
def baseEnd_2826507 : Nat := 1451356664297878012063637

theorem tailTrace_2826507 : CollatzResearch.WordTrace tailWord_2826507 prefixEnd_2826507 1451356664297878012063637 := by
  unfold tailWord_2826507
  simp only [CollatzResearch.WordTrace]
  refine ⟨103091179571055342808693775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68727453047370228539129183 103091179571055342808693775)
  ·
    refine ⟨154636769356583014213040663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103091179571055342808693775 154636769356583014213040663)
    ·
      refine ⟨231955154034874521319560995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154636769356583014213040663 231955154034874521319560995)
      ·
        refine ⟨347932731052311781979341493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231955154034874521319560995 347932731052311781979341493)
        ·
          refine ⟨32618693536154229560563265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 347932731052311781979341493 32618693536154229560563265)
          ·
            refine ⟨24464020152115672170422449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32618693536154229560563265 24464020152115672170422449)
            ·
              refine ⟨18348015114086754127816837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24464020152115672170422449 18348015114086754127816837)
              ·
                refine ⟨3440252833891266398965657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18348015114086754127816837 3440252833891266398965657)
                ·
                  refine ⟨2580189625418449799224243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3440252833891266398965657 2580189625418449799224243)
                  ·
                    refine ⟨3870284438127674698836365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2580189625418449799224243 3870284438127674698836365)
                    ·
                      refine ⟨1451356664297878012063637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3870284438127674698836365 1451356664297878012063637)
                      ·
                        rfl

theorem cell23_2826507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 2, 1, 3].length) (baseStart_2826507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826507 prefixEnd_2826507 := by exact prefixLift 2826507
  have htrace : WordTrace (prefixWord ++ tailWord_2826507) baseStart_2826507 baseEnd_2826507 := by
    simpa [prefixWord, tailWord_2826507, baseEnd_2826507] using wordTrace_append hprefix tailTrace_2826507
  have hstable : (prefixWord ++ tailWord_2826507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826507).length < 2 ^ (prefixWord ++ tailWord_2826507).sum := by decide
  have hdescent : baseEnd_2826507 < baseStart_2826507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826523 : List Nat := [1, 1, 1, 1, 1, 1, 6, 3, 2, 6]
def baseStart_2826523 : Nat := 118140960795 + 2826523 * 2 ^ 59
def prefixEnd_2826523 : Nat := 4983230072969 + 3 ^ 40 * 2826523 * 2
def baseEnd_2826523 : Nat := 483788293329449983154521

theorem tailTrace_2826523 : CollatzResearch.WordTrace tailWord_2826523 prefixEnd_2826523 483788293329449983154521 := by
  unfold tailWord_2826523
  simp only [CollatzResearch.WordTrace]
  refine ⟨103091763138997377541276223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68727842092664918360850815 103091763138997377541276223)
  ·
    refine ⟨154637644708496066311914335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103091763138997377541276223 154637644708496066311914335)
    ·
      refine ⟨231956467062744099467871503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154637644708496066311914335 231956467062744099467871503)
      ·
        refine ⟨347934700594116149201807255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231956467062744099467871503 347934700594116149201807255)
        ·
          refine ⟨521902050891174223802710883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347934700594116149201807255 521902050891174223802710883)
          ·
            refine ⟨782853076336761335704066325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 521902050891174223802710883 782853076336761335704066325)
            ·
              refine ⟨36696237953285687611128109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 782853076336761335704066325 36696237953285687611128109)
              ·
                refine ⟨13761089232482132854173041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36696237953285687611128109 13761089232482132854173041)
                ·
                  refine ⟨10320816924361599640629781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13761089232482132854173041 10320816924361599640629781)
                  ·
                    refine ⟨483788293329449983154521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10320816924361599640629781 483788293329449983154521)
                    ·
                      rfl

theorem cell23_2826523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 6].length) (baseStart_2826523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826523 prefixEnd_2826523 := by exact prefixLift 2826523
  have htrace : WordTrace (prefixWord ++ tailWord_2826523) baseStart_2826523 baseEnd_2826523 := by
    simpa [prefixWord, tailWord_2826523, baseEnd_2826523] using wordTrace_append hprefix tailTrace_2826523
  have hstable : (prefixWord ++ tailWord_2826523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826523).length < 2 ^ (prefixWord ++ tailWord_2826523).sum := by decide
  have hdescent : baseEnd_2826523 < baseStart_2826523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826547 : List Nat := [1, 1, 1, 2, 5, 1, 3, 2, 1, 4, 2]
def baseStart_2826547 : Nat := 118140960795 + 2826547 * 2 ^ 59
def prefixEnd_2826547 : Nat := 4983230072969 + 3 ^ 40 * 2826547 * 2
def baseEnd_2826547 : Nat := 1451377203524057855563453

theorem tailTrace_2826547 : CollatzResearch.WordTrace tailWord_2826547 prefixEnd_2826547 1451377203524057855563453 := by
  unfold tailWord_2826547
  simp only [CollatzResearch.WordTrace]
  refine ⟨103092638490910429640149895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68728425660606953093433263 103092638490910429640149895)
  ·
    refine ⟨154638957736365644460224843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103092638490910429640149895 154638957736365644460224843)
    ·
      refine ⟨231958436604548466690337265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154638957736365644460224843 231958436604548466690337265)
      ·
        refine ⟨173968827453411350017752949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231958436604548466690337265 173968827453411350017752949)
        ·
          refine ⟨16309577573757314064164339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 173968827453411350017752949 16309577573757314064164339)
          ·
            refine ⟨24464366360635971096246509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16309577573757314064164339 24464366360635971096246509)
            ·
              refine ⟨9174137385238489161092441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24464366360635971096246509 9174137385238489161092441)
              ·
                refine ⟨6880603038928866870819331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9174137385238489161092441 6880603038928866870819331)
                ·
                  refine ⟨10320904558393300306228997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6880603038928866870819331 10320904558393300306228997)
                  ·
                    refine ⟨1935169604698743807417937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10320904558393300306228997 1935169604698743807417937)
                    ·
                      refine ⟨1451377203524057855563453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1935169604698743807417937 1451377203524057855563453)
                      ·
                        rfl

theorem cell23_2826547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 4, 2].length) (baseStart_2826547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826547 prefixEnd_2826547 := by exact prefixLift 2826547
  have htrace : WordTrace (prefixWord ++ tailWord_2826547) baseStart_2826547 baseEnd_2826547 := by
    simpa [prefixWord, tailWord_2826547, baseEnd_2826547] using wordTrace_append hprefix tailTrace_2826547
  have hstable : (prefixWord ++ tailWord_2826547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826547).length < 2 ^ (prefixWord ++ tailWord_2826547).sum := by decide
  have hdescent : baseEnd_2826547 < baseStart_2826547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826563 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 7]
def baseStart_2826563 : Nat := 118140960795 + 2826563 * 2 ^ 59
def prefixEnd_2826563 : Nat := 4983230072969 + 3 ^ 40 * 2826563 * 2
def baseEnd_2826563 : Nat := 1451385419214529792963379

theorem tailTrace_2826563 : CollatzResearch.WordTrace tailWord_2826563 prefixEnd_2826563 1451385419214529792963379 := by
  unfold tailWord_2826563
  simp only [CollatzResearch.WordTrace]
  refine ⟨103093222058852464372732343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68728814705901642915154895 103093222058852464372732343)
  ·
    refine ⟨154639833088278696559098515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103093222058852464372732343 154639833088278696559098515)
    ·
      refine ⟨231959749632418044838647773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154639833088278696559098515 231959749632418044838647773)
      ·
        refine ⟨86984906112156766814492915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 231959749632418044838647773 86984906112156766814492915)
        ·
          refine ⟨130477359168235150221739373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86984906112156766814492915 130477359168235150221739373)
          ·
            refine ⟨48929009688088181333152265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130477359168235150221739373 48929009688088181333152265)
            ·
              refine ⟨36696757266066135999864199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48929009688088181333152265 36696757266066135999864199)
              ·
                refine ⟨55045135899099203999796299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36696757266066135999864199 55045135899099203999796299)
                ·
                  refine ⟨82567703848648805999694449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55045135899099203999796299 82567703848648805999694449)
                  ·
                    refine ⟨61925777886486604499770837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82567703848648805999694449 61925777886486604499770837)
                    ·
                      refine ⟨1451385419214529792963379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 61925777886486604499770837 1451385419214529792963379)
                      ·
                        rfl

theorem cell23_2826563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_2826563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826563 prefixEnd_2826563 := by exact prefixLift 2826563
  have htrace : WordTrace (prefixWord ++ tailWord_2826563) baseStart_2826563 baseEnd_2826563 := by
    simpa [prefixWord, tailWord_2826563, baseEnd_2826563] using wordTrace_append hprefix tailTrace_2826563
  have hstable : (prefixWord ++ tailWord_2826563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826563).length < 2 ^ (prefixWord ++ tailWord_2826563).sum := by decide
  have hdescent : baseEnd_2826563 < baseStart_2826563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826604 : List Nat := [2, 2, 1, 1, 6, 1, 2, 3, 5]
def baseStart_2826604 : Nat := 118140960795 + 2826604 * 2 ^ 59
def prefixEnd_2826604 : Nat := 4983230072969 + 3 ^ 40 * 2826604 * 2
def baseEnd_2826604 : Nat := 161267385769040459172299

theorem tailTrace_2826604 : CollatzResearch.WordTrace tailWord_2826604 prefixEnd_2826604 161267385769040459172299 := by
  unfold tailWord_2826604
  simp only [CollatzResearch.WordTrace]
  refine ⟨51547358725851964187487433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68729811634469285583316577 51547358725851964187487433)
  ·
    refine ⟨38660519044388973140615575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51547358725851964187487433 38660519044388973140615575)
    ·
      refine ⟨57990778566583459710923363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38660519044388973140615575 57990778566583459710923363)
      ·
        refine ⟨86986167849875189566385045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57990778566583459710923363 86986167849875189566385045)
        ·
          refine ⟨4077476617962899510924299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 86986167849875189566385045 4077476617962899510924299)
          ·
            refine ⟨6116214926944349266386449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4077476617962899510924299 6116214926944349266386449)
            ·
              refine ⟨4587161195208261949789837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6116214926944349266386449 4587161195208261949789837)
              ·
                refine ⟨1720185448203098231171189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4587161195208261949789837 1720185448203098231171189)
                ·
                  refine ⟨161267385769040459172299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1720185448203098231171189 161267385769040459172299)
                  ·
                    rfl

theorem cell23_2826604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3, 5].length) (baseStart_2826604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826604 prefixEnd_2826604 := by exact prefixLift 2826604
  have htrace : WordTrace (prefixWord ++ tailWord_2826604) baseStart_2826604 baseEnd_2826604 := by
    simpa [prefixWord, tailWord_2826604, baseEnd_2826604] using wordTrace_append hprefix tailTrace_2826604
  have hstable : (prefixWord ++ tailWord_2826604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826604).length < 2 ^ (prefixWord ++ tailWord_2826604).sum := by decide
  have hdescent : baseEnd_2826604 < baseStart_2826604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826647 : List Nat := [1, 1, 3, 3, 1, 1, 4, 2, 3, 4]
def baseStart_2826647 : Nat := 118140960795 + 2826647 * 2 ^ 59
def prefixEnd_2826647 : Nat := 4983230072969 + 3 ^ 40 * 2826647 * 2
def baseEnd_2826647 : Nat := 483809517196502488104331

theorem tailTrace_2826647 : CollatzResearch.WordTrace tailWord_2826647 prefixEnd_2826647 483809517196502488104331 := by
  unfold tailWord_2826647
  simp only [CollatzResearch.WordTrace]
  refine ⟨103096285790548146718790195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68730857193698764479193463 103096285790548146718790195)
  ·
    refine ⟨154644428685822220078185293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103096285790548146718790195 154644428685822220078185293)
    ·
      refine ⟨57991660757183332529319485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154644428685822220078185293 57991660757183332529319485)
      ·
        refine ⟨21746872783943749698494807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57991660757183332529319485 21746872783943749698494807)
        ·
          refine ⟨32620309175915624547742211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21746872783943749698494807 32620309175915624547742211)
          ·
            refine ⟨48930463763873436821613317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32620309175915624547742211 48930463763873436821613317)
            ·
              refine ⟨9174461955726269404052497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48930463763873436821613317 9174461955726269404052497)
              ·
                refine ⟨6880846466794702053039373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9174461955726269404052497 6880846466794702053039373)
                ·
                  refine ⟨2580317425048013269889765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6880846466794702053039373 2580317425048013269889765)
                  ·
                    refine ⟨483809517196502488104331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2580317425048013269889765 483809517196502488104331)
                    ·
                      rfl

theorem cell23_2826647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 3, 4].length) (baseStart_2826647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826647 prefixEnd_2826647 := by exact prefixLift 2826647
  have htrace : WordTrace (prefixWord ++ tailWord_2826647) baseStart_2826647 baseEnd_2826647 := by
    simpa [prefixWord, tailWord_2826647, baseEnd_2826647] using wordTrace_append hprefix tailTrace_2826647
  have hstable : (prefixWord ++ tailWord_2826647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826647).length < 2 ^ (prefixWord ++ tailWord_2826647).sum := by decide
  have hdescent : baseEnd_2826647 < baseStart_2826647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826654 : List Nat := [4, 3, 1, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_2826654 : Nat := 118140960795 + 2826654 * 2 ^ 59
def prefixEnd_2826654 : Nat := 4983230072969 + 3 ^ 40 * 2826654 * 2
def baseEnd_2826654 : Nat := 1451432145954088936925461

theorem tailTrace_2826654 : CollatzResearch.WordTrace tailWord_2826654 prefixEnd_2826654 1451432145954088936925461 := by
  unfold tailWord_2826654
  simp only [CollatzResearch.WordTrace]
  refine ⟨12887067637690348364286877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68731027401015191276196677 12887067637690348364286877)
  ·
    refine ⟨4832650364133880636607579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12887067637690348364286877 4832650364133880636607579)
    ·
      refine ⟨7248975546200820954911369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4832650364133880636607579 7248975546200820954911369)
      ·
        refine ⟨5436731659650615716183527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7248975546200820954911369 5436731659650615716183527)
        ·
          refine ⟨8155097489475923574275291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5436731659650615716183527 8155097489475923574275291)
          ·
            refine ⟨12232646234213885361412937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8155097489475923574275291 12232646234213885361412937)
            ·
              refine ⟨9174484675660414021059703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12232646234213885361412937 9174484675660414021059703)
              ·
                refine ⟨13761727013490621031589555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9174484675660414021059703 13761727013490621031589555)
                ·
                  refine ⟨20642590520235931547384333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13761727013490621031589555 20642590520235931547384333)
                  ·
                    refine ⟨7740971445088474330269125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20642590520235931547384333 7740971445088474330269125)
                    ·
                      refine ⟨1451432145954088936925461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7740971445088474330269125 1451432145954088936925461)
                      ·
                        rfl

theorem cell23_2826654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_2826654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826654 prefixEnd_2826654 := by exact prefixLift 2826654
  have htrace : WordTrace (prefixWord ++ tailWord_2826654) baseStart_2826654 baseEnd_2826654 := by
    simpa [prefixWord, tailWord_2826654, baseEnd_2826654] using wordTrace_append hprefix tailTrace_2826654
  have hstable : (prefixWord ++ tailWord_2826654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826654).length < 2 ^ (prefixWord ++ tailWord_2826654).sum := by decide
  have hdescent : baseEnd_2826654 < baseStart_2826654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826660 : List Nat := [2, 3, 1, 2, 1, 1, 3, 2, 8]
def baseStart_2826660 : Nat := 118140960795 + 2826660 * 2 ^ 59
def prefixEnd_2826660 : Nat := 4983230072969 + 3 ^ 40 * 2826660 * 2
def baseEnd_2826660 : Nat := 161270580759779545938937

theorem tailTrace_2826660 : CollatzResearch.WordTrace tailWord_2826660 prefixEnd_2826660 161270580759779545938937 := by
  unfold tailWord_2826660
  simp only [CollatzResearch.WordTrace]
  refine ⟨51548379969750524969506717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68731173293000699959342289 51548379969750524969506717)
  ·
    refine ⟨19330642488656446863565019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51548379969750524969506717 19330642488656446863565019)
    ·
      refine ⟨28995963732984670295347529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19330642488656446863565019 28995963732984670295347529)
      ·
        refine ⟨21746972799738502721510647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28995963732984670295347529 21746972799738502721510647)
        ·
          refine ⟨32620459199607754082265971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21746972799738502721510647 32620459199607754082265971)
          ·
            refine ⟨48930688799411631123398957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32620459199607754082265971 48930688799411631123398957)
            ·
              refine ⟨18349008299779361671274609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48930688799411631123398957 18349008299779361671274609)
              ·
                refine ⟨13761756224834521253455957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18349008299779361671274609 13761756224834521253455957)
                ·
                  refine ⟨161270580759779545938937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13761756224834521253455957 161270580759779545938937)
                  ·
                    rfl

theorem cell23_2826660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 8].length) (baseStart_2826660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826660 prefixEnd_2826660 := by exact prefixLift 2826660
  have htrace : WordTrace (prefixWord ++ tailWord_2826660) baseStart_2826660 baseEnd_2826660 := by
    simpa [prefixWord, tailWord_2826660, baseEnd_2826660] using wordTrace_append hprefix tailTrace_2826660
  have hstable : (prefixWord ++ tailWord_2826660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826660).length < 2 ^ (prefixWord ++ tailWord_2826660).sum := by decide
  have hdescent : baseEnd_2826660 < baseStart_2826660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826697 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 3, 5, 2]
def baseStart_2826697 : Nat := 118140960795 + 2826697 * 2 ^ 59
def prefixEnd_2826697 : Nat := 4983230072969 + 3 ^ 40 * 2826697 * 2
def baseEnd_2826697 : Nat := 1451454225622232268687763

theorem tailTrace_2826697 : CollatzResearch.WordTrace tailWord_2826697 prefixEnd_2826697 1451454225622232268687763 := by
  unfold tailWord_2826697
  simp only [CollatzResearch.WordTrace]
  refine ⟨103098109440367005258110345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68732072960244670172073563 103098109440367005258110345)
  ·
    refine ⟨77323582080275253943582759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103098109440367005258110345 77323582080275253943582759)
    ·
      refine ⟨115985373120412880915374139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77323582080275253943582759 115985373120412880915374139)
      ·
        refine ⟨173978059680619321373061209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115985373120412880915374139 173978059680619321373061209)
        ·
          refine ⟨130483544760464491029795907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173978059680619321373061209 130483544760464491029795907)
          ·
            refine ⟨195725317140696736544693861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130483544760464491029795907 195725317140696736544693861)
            ·
              refine ⟨36698496963880638102130099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 195725317140696736544693861 36698496963880638102130099)
              ·
                refine ⟨55047745445820957153195149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36698496963880638102130099 55047745445820957153195149)
                ·
                  refine ⟨20642904542182858932448181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55047745445820957153195149 20642904542182858932448181)
                  ·
                    refine ⟨1935272300829643024917017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20642904542182858932448181 1935272300829643024917017)
                    ·
                      refine ⟨1451454225622232268687763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1935272300829643024917017 1451454225622232268687763)
                      ·
                        rfl

theorem cell23_2826697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 5, 2].length) (baseStart_2826697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826697 prefixEnd_2826697 := by exact prefixLift 2826697
  have htrace : WordTrace (prefixWord ++ tailWord_2826697) baseStart_2826697 baseEnd_2826697 := by
    simpa [prefixWord, tailWord_2826697, baseEnd_2826697] using wordTrace_append hprefix tailTrace_2826697
  have hstable : (prefixWord ++ tailWord_2826697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826697).length < 2 ^ (prefixWord ++ tailWord_2826697).sum := by decide
  have hdescent : baseEnd_2826697 < baseStart_2826697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826721 : List Nat := [1, 2, 3, 1, 2, 2, 2, 5, 1, 1, 3]
def baseStart_2826721 : Nat := 118140960795 + 2826721 * 2 ^ 59
def prefixEnd_2826721 : Nat := 4983230072969 + 3 ^ 40 * 2826721 * 2
def baseEnd_2826721 : Nat := 1451466549157940174787653

theorem tailTrace_2826721 : CollatzResearch.WordTrace tailWord_2826721 prefixEnd_2826721 1451466549157940174787653 := by
  unfold tailWord_2826721
  simp only [CollatzResearch.WordTrace]
  refine ⟨103098984792280057356984017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68732656528186704904656011 103098984792280057356984017)
  ·
    refine ⟨77324238594210043017738013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103098984792280057356984017 77324238594210043017738013)
    ·
      refine ⟨28996589472828766131651755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77324238594210043017738013 28996589472828766131651755)
      ·
        refine ⟨43494884209243149197477633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28996589472828766131651755 43494884209243149197477633)
        ·
          refine ⟨32621163156932361898108225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43494884209243149197477633 32621163156932361898108225)
          ·
            refine ⟨24465872367699271423581169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32621163156932361898108225 24465872367699271423581169)
            ·
              refine ⟨18349404275774453567685877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24465872367699271423581169 18349404275774453567685877)
              ·
                refine ⟨1720256650853855021970551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18349404275774453567685877 1720256650853855021970551)
                ·
                  refine ⟨2580384976280782532955827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1720256650853855021970551 2580384976280782532955827)
                  ·
                    refine ⟨3870577464421173799433741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2580384976280782532955827 3870577464421173799433741)
                    ·
                      refine ⟨1451466549157940174787653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3870577464421173799433741 1451466549157940174787653)
                      ·
                        rfl

theorem cell23_2826721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 5, 1, 1, 3].length) (baseStart_2826721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826721 prefixEnd_2826721 := by exact prefixLift 2826721
  have htrace : WordTrace (prefixWord ++ tailWord_2826721) baseStart_2826721 baseEnd_2826721 := by
    simpa [prefixWord, tailWord_2826721, baseEnd_2826721] using wordTrace_append hprefix tailTrace_2826721
  have hstable : (prefixWord ++ tailWord_2826721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826721).length < 2 ^ (prefixWord ++ tailWord_2826721).sum := by decide
  have hdescent : baseEnd_2826721 < baseStart_2826721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826757 : List Nat := [1, 3, 1, 1, 2, 2, 3, 3, 1, 2, 4]
def baseStart_2826757 : Nat := 118140960795 + 2826757 * 2 ^ 59
def prefixEnd_2826757 : Nat := 4983230072969 + 3 ^ 40 * 2826757 * 2
def baseEnd_2826757 : Nat := 1451485034461502033937487

theorem tailTrace_2826757 : CollatzResearch.WordTrace tailWord_2826757 prefixEnd_2826757 1451485034461502033937487 := by
  unfold tailWord_2826757
  simp only [CollatzResearch.WordTrace]
  refine ⟨103100297820149635505294525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68733531880099757003529683 103100297820149635505294525)
  ·
    refine ⟨38662611682556113314485447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103100297820149635505294525 38662611682556113314485447)
    ·
      refine ⟨57993917523834169971728171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38662611682556113314485447 57993917523834169971728171)
      ·
        refine ⟨86990876285751254957592257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57993917523834169971728171 86990876285751254957592257)
        ·
          refine ⟨65243157214313441218194193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86990876285751254957592257 65243157214313441218194193)
          ·
            refine ⟨48932367910735080913645645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65243157214313441218194193 48932367910735080913645645)
            ·
              refine ⟨18349637966525655342617117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48932367910735080913645645 18349637966525655342617117)
              ·
                refine ⟨6881114237447120753481419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18349637966525655342617117 6881114237447120753481419)
                ·
                  refine ⟨10321671356170681130222129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6881114237447120753481419 10321671356170681130222129)
                  ·
                    refine ⟨7741253517128010847666597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10321671356170681130222129 7741253517128010847666597)
                    ·
                      refine ⟨1451485034461502033937487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7741253517128010847666597 1451485034461502033937487)
                      ·
                        rfl

theorem cell23_2826757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_2826757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826757 prefixEnd_2826757 := by exact prefixLift 2826757
  have htrace : WordTrace (prefixWord ++ tailWord_2826757) baseStart_2826757 baseEnd_2826757 := by
    simpa [prefixWord, tailWord_2826757, baseEnd_2826757] using wordTrace_append hprefix tailTrace_2826757
  have hstable : (prefixWord ++ tailWord_2826757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826757).length < 2 ^ (prefixWord ++ tailWord_2826757).sum := by decide
  have hdescent : baseEnd_2826757 < baseStart_2826757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826758 : List Nat := [6, 2, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_2826758 : Nat := 118140960795 + 2826758 * 2 ^ 59
def prefixEnd_2826758 : Nat := 4983230072969 + 3 ^ 40 * 2826758 * 2
def baseEnd_2826758 : Nat := 483828515980718843341661

theorem tailTrace_2826758 : CollatzResearch.WordTrace tailWord_2826758 prefixEnd_2826758 483828515980718843341661 := by
  unfold tailWord_2826758
  simp only [CollatzResearch.WordTrace]
  refine ⟨3221885446660812896127529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 68733556195430675117387285 3221885446660812896127529)
  ·
    refine ⟨2416414084995609672095647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3221885446660812896127529 2416414084995609672095647)
    ·
      refine ⟨3624621127493414508143471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2416414084995609672095647 3624621127493414508143471)
      ·
        refine ⟨5436931691240121762215207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3624621127493414508143471 5436931691240121762215207)
        ·
          refine ⟨8155397536860182643322811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5436931691240121762215207 8155397536860182643322811)
          ·
            refine ⟨12233096305290273964984217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8155397536860182643322811 12233096305290273964984217)
            ·
              refine ⟨9174822228967705473738163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12233096305290273964984217 9174822228967705473738163)
              ·
                refine ⟨13762233343451558210607245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9174822228967705473738163 13762233343451558210607245)
                ·
                  refine ⟨5160837503794334328977717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13762233343451558210607245 5160837503794334328977717)
                  ·
                    refine ⟨483828515980718843341661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5160837503794334328977717 483828515980718843341661)
                    ·
                      rfl

theorem cell23_2826758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_2826758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826758 prefixEnd_2826758 := by exact prefixLift 2826758
  have htrace : WordTrace (prefixWord ++ tailWord_2826758) baseStart_2826758 baseEnd_2826758 := by
    simpa [prefixWord, tailWord_2826758, baseEnd_2826758] using wordTrace_append hprefix tailTrace_2826758
  have hstable : (prefixWord ++ tailWord_2826758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826758).length < 2 ^ (prefixWord ++ tailWord_2826758).sum := by decide
  have hdescent : baseEnd_2826758 < baseStart_2826758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826764 : List Nat := [2, 2, 1, 2, 4, 1, 2, 1, 3, 2, 3]
def baseStart_2826764 : Nat := 118140960795 + 2826764 * 2 ^ 59
def prefixEnd_2826764 : Nat := 4983230072969 + 3 ^ 40 * 2826764 * 2
def baseEnd_2826764 : Nat := 1451488628826083506549955

theorem tailTrace_2826764 : CollatzResearch.WordTrace tailWord_2826764 prefixEnd_2826764 1451488628826083506549955 := by
  unfold tailWord_2826764
  simp only [CollatzResearch.WordTrace]
  refine ⟨51550276565562137850399673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68733702087416183800532897 51550276565562137850399673)
  ·
    refine ⟨38662707424171603387799755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51550276565562137850399673 38662707424171603387799755)
    ·
      refine ⟨57994061136257405081699633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38662707424171603387799755 57994061136257405081699633)
      ·
        refine ⟨43495545852193053811274725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57994061136257405081699633 43495545852193053811274725)
        ·
          refine ⟨8155414847286197589614011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43495545852193053811274725 8155414847286197589614011)
          ·
            refine ⟨12233122270929296384421017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8155414847286197589614011 12233122270929296384421017)
            ·
              refine ⟨9174841703196972288315763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12233122270929296384421017 9174841703196972288315763)
              ·
                refine ⟨13762262554795458432473645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9174841703196972288315763 13762262554795458432473645)
                ·
                  refine ⟨5160848458048296912177617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13762262554795458432473645 5160848458048296912177617)
                  ·
                    refine ⟨3870636343536222684133213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5160848458048296912177617 3870636343536222684133213)
                    ·
                      refine ⟨1451488628826083506549955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3870636343536222684133213 1451488628826083506549955)
                      ·
                        rfl

theorem cell23_2826764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_2826764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826764 prefixEnd_2826764 := by exact prefixLift 2826764
  have htrace : WordTrace (prefixWord ++ tailWord_2826764) baseStart_2826764 baseEnd_2826764 := by
    simpa [prefixWord, tailWord_2826764, baseEnd_2826764] using wordTrace_append hprefix tailTrace_2826764
  have hstable : (prefixWord ++ tailWord_2826764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826764).length < 2 ^ (prefixWord ++ tailWord_2826764).sum := by decide
  have hdescent : baseEnd_2826764 < baseStart_2826764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826765 : List Nat := [1, 7, 1, 1, 1, 1, 3, 1, 2, 3, 2]
def baseStart_2826765 : Nat := 118140960795 + 2826765 * 2 ^ 59
def prefixEnd_2826765 : Nat := 4983230072969 + 3 ^ 40 * 2826765 * 2
def baseEnd_2826765 : Nat := 1451489142306738002637451

theorem tailTrace_2826765 : CollatzResearch.WordTrace tailWord_2826765 prefixEnd_2826765 1451489142306738002637451 := by
  unfold tailWord_2826765
  simp only [CollatzResearch.WordTrace]
  refine ⟨103100589604120652871585749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68733726402747101914390499 103100589604120652871585749)
  ·
    refine ⟨2416420068846577801677791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 103100589604120652871585749 2416420068846577801677791)
    ·
      refine ⟨3624630103269866702516687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2416420068846577801677791 3624630103269866702516687)
      ·
        refine ⟨5436945154904800053775031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3624630103269866702516687 5436945154904800053775031)
        ·
          refine ⟨8155417732357200080662547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5436945154904800053775031 8155417732357200080662547)
          ·
            refine ⟨12233126598535800120993821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8155417732357200080662547 12233126598535800120993821)
            ·
              refine ⟨4587422474450925045372683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12233126598535800120993821 4587422474450925045372683)
              ·
                refine ⟨6881133711676387568059025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4587422474450925045372683 6881133711676387568059025)
                ·
                  refine ⟨5160850283757290676044269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6881133711676387568059025 5160850283757290676044269)
                  ·
                    refine ⟨1935318856408984003516601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5160850283757290676044269 1935318856408984003516601)
                    ·
                      refine ⟨1451489142306738002637451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1935318856408984003516601 1451489142306738002637451)
                      ·
                        rfl

theorem cell23_2826765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_2826765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826765 prefixEnd_2826765 := by exact prefixLift 2826765
  have htrace : WordTrace (prefixWord ++ tailWord_2826765) baseStart_2826765 baseEnd_2826765 := by
    simpa [prefixWord, tailWord_2826765, baseEnd_2826765] using wordTrace_append hprefix tailTrace_2826765
  have hstable : (prefixWord ++ tailWord_2826765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826765).length < 2 ^ (prefixWord ++ tailWord_2826765).sum := by decide
  have hdescent : baseEnd_2826765 < baseStart_2826765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826775 : List Nat := [1, 1, 3, 6, 2, 1, 2, 1, 1, 5]
def baseStart_2826775 : Nat := 118140960795 + 2826775 * 2 ^ 59
def prefixEnd_2826775 : Nat := 4983230072969 + 3 ^ 40 * 2826775 * 2
def baseEnd_2826775 : Nat := 483831425704427654504135

theorem tailTrace_2826775 : CollatzResearch.WordTrace tailWord_2826775 prefixEnd_2826775 483831425704427654504135 := by
  unfold tailWord_2826775
  simp only [CollatzResearch.WordTrace]
  refine ⟨103100954334084424579449779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68733969556056283052966519 103100954334084424579449779)
  ·
    refine ⟨154651431501126636869174669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103100954334084424579449779 154651431501126636869174669)
    ·
      refine ⟨57994286812922488825940501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154651431501126636869174669 57994286812922488825940501)
      ·
        refine ⟨2718482194355741663715961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 57994286812922488825940501 2718482194355741663715961)
        ·
          refine ⟨2038861645766806247786971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2718482194355741663715961 2038861645766806247786971)
          ·
            refine ⟨3058292468650209371680457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2038861645766806247786971 3058292468650209371680457)
            ·
              refine ⟨2293719351487657028760343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3058292468650209371680457 2293719351487657028760343)
              ·
                refine ⟨3440579027231485543140515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2293719351487657028760343 3440579027231485543140515)
                ·
                  refine ⟨5160868540847228314710773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3440579027231485543140515 5160868540847228314710773)
                  ·
                    refine ⟨483831425704427654504135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5160868540847228314710773 483831425704427654504135)
                    ·
                      rfl

theorem cell23_2826775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 1, 5].length) (baseStart_2826775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826775 prefixEnd_2826775 := by exact prefixLift 2826775
  have htrace : WordTrace (prefixWord ++ tailWord_2826775) baseStart_2826775 baseEnd_2826775 := by
    simpa [prefixWord, tailWord_2826775, baseEnd_2826775] using wordTrace_append hprefix tailTrace_2826775
  have hstable : (prefixWord ++ tailWord_2826775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826775).length < 2 ^ (prefixWord ++ tailWord_2826775).sum := by decide
  have hdescent : baseEnd_2826775 < baseStart_2826775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826778 : List Nat := [3, 1, 1, 3, 1, 1, 3, 5, 1, 2, 2]
def baseStart_2826778 : Nat := 118140960795 + 2826778 * 2 ^ 59
def prefixEnd_2826778 : Nat := 4983230072969 + 3 ^ 40 * 2826778 * 2
def baseEnd_2826778 : Nat := 1451495817555246451774891

theorem tailTrace_2826778 : CollatzResearch.WordTrace tailWord_2826778 prefixEnd_2826778 1451495817555246451774891 := by
  unfold tailWord_2826778
  simp only [CollatzResearch.WordTrace]
  refine ⟨25775265938268389022952247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 68734042502049037394539325 25775265938268389022952247)
  ·
    refine ⟨38662898907402583534428371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25775265938268389022952247 38662898907402583534428371)
    ·
      refine ⟨57994348361103875301642557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38662898907402583534428371 57994348361103875301642557)
      ·
        refine ⟨21747880635413953238115959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57994348361103875301642557 21747880635413953238115959)
        ·
          refine ⟨32621820953120929857173939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21747880635413953238115959 32621820953120929857173939)
          ·
            refine ⟨48932731429681394785760909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32621820953120929857173939 48932731429681394785760909)
            ·
              refine ⟨18349774286130523044660341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48932731429681394785760909 18349774286130523044660341)
              ·
                refine ⟨1720291339324736535436907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18349774286130523044660341 1720291339324736535436907)
                ·
                  refine ⟨2580437008987104803155361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1720291339324736535436907 2580437008987104803155361)
                  ·
                    refine ⟨1935327756740328602366521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2580437008987104803155361 1935327756740328602366521)
                    ·
                      refine ⟨1451495817555246451774891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1935327756740328602366521 1451495817555246451774891)
                      ·
                        rfl

theorem cell23_2826778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_2826778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826778 prefixEnd_2826778 := by exact prefixLift 2826778
  have htrace : WordTrace (prefixWord ++ tailWord_2826778) baseStart_2826778 baseEnd_2826778 := by
    simpa [prefixWord, tailWord_2826778, baseEnd_2826778] using wordTrace_append hprefix tailTrace_2826778
  have hstable : (prefixWord ++ tailWord_2826778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826778).length < 2 ^ (prefixWord ++ tailWord_2826778).sum := by decide
  have hdescent : baseEnd_2826778 < baseStart_2826778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826781 : List Nat := [1, 4, 2, 2, 1, 3, 1, 3, 1, 2, 3]
def baseStart_2826781 : Nat := 118140960795 + 2826781 * 2 ^ 59
def prefixEnd_2826781 : Nat := 4983230072969 + 3 ^ 40 * 2826781 * 2
def baseEnd_2826781 : Nat := 1451497357997209940037377

theorem tailTrace_2826781 : CollatzResearch.WordTrace tailWord_2826781 prefixEnd_2826781 1451497357997209940037377 := by
  unfold tailWord_2826781
  simp only [CollatzResearch.WordTrace]
  refine ⟨103101173172062687604168197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68734115448041791736112131 103101173172062687604168197)
  ·
    refine ⟨19331469969761753925781537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103101173172062687604168197 19331469969761753925781537)
    ·
      refine ⟨14498602477321315444336153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19331469969761753925781537 14498602477321315444336153)
      ·
        refine ⟨10873951857990986583252115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14498602477321315444336153 10873951857990986583252115)
        ·
          refine ⟨16310927786986479874878173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10873951857990986583252115 16310927786986479874878173)
          ·
            refine ⟨6116597920119929953079315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16310927786986479874878173 6116597920119929953079315)
            ·
              refine ⟨9174896880179894929618973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6116597920119929953079315 9174896880179894929618973)
              ·
                refine ⟨3440586330067460598607115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9174896880179894929618973 3440586330067460598607115)
                ·
                  refine ⟨5160879495101190897910673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3440586330067460598607115 5160879495101190897910673)
                  ·
                    refine ⟨3870659621325893173433005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5160879495101190897910673 3870659621325893173433005)
                    ·
                      refine ⟨1451497357997209940037377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3870659621325893173433005 1451497357997209940037377)
                      ·
                        rfl

theorem cell23_2826781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_2826781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826781 prefixEnd_2826781 := by exact prefixLift 2826781
  have htrace : WordTrace (prefixWord ++ tailWord_2826781) baseStart_2826781 baseEnd_2826781 := by
    simpa [prefixWord, tailWord_2826781, baseEnd_2826781] using wordTrace_append hprefix tailTrace_2826781
  have hstable : (prefixWord ++ tailWord_2826781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826781).length < 2 ^ (prefixWord ++ tailWord_2826781).sum := by decide
  have hdescent : baseEnd_2826781 < baseStart_2826781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826821 : List Nat := [1, 3, 1, 1, 1, 5, 1, 4, 1, 3, 2]
def baseStart_2826821 : Nat := 118140960795 + 2826821 * 2 ^ 59
def prefixEnd_2826821 : Nat := 4983230072969 + 3 ^ 40 * 2826821 * 2
def baseEnd_2826821 : Nat := 1451517897223389783537193

theorem tailTrace_2826821 : CollatzResearch.WordTrace tailWord_2826821 prefixEnd_2826821 1451517897223389783537193 := by
  unfold tailWord_2826821
  simp only [CollatzResearch.WordTrace]
  refine ⟨103102632091917774435624317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68735088061278516290416211 103102632091917774435624317)
  ·
    refine ⟨38663487034469165413359119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103102632091917774435624317 38663487034469165413359119)
    ·
      refine ⟨57995230551703748120038679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38663487034469165413359119 57995230551703748120038679)
      ·
        refine ⟨86992845827555622180058019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57995230551703748120038679 86992845827555622180058019)
        ·
          refine ⟨130489268741333433270087029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86992845827555622180058019 130489268741333433270087029)
          ·
            refine ⟨12233368944500009369070659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 130489268741333433270087029 12233368944500009369070659)
            ·
              refine ⟨18350053416750014053605989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12233368944500009369070659 18350053416750014053605989)
              ·
                refine ⟨3440635015640627635051123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18350053416750014053605989 3440635015640627635051123)
                ·
                  refine ⟨5160952523460941452576685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3440635015640627635051123 5160952523460941452576685)
                  ·
                    refine ⟨1935357196297853044716257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5160952523460941452576685 1935357196297853044716257)
                    ·
                      refine ⟨1451517897223389783537193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1935357196297853044716257 1451517897223389783537193)
                      ·
                        rfl

theorem cell23_2826821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 3, 2].length) (baseStart_2826821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826821 prefixEnd_2826821 := by exact prefixLift 2826821
  have htrace : WordTrace (prefixWord ++ tailWord_2826821) baseStart_2826821 baseEnd_2826821 := by
    simpa [prefixWord, tailWord_2826821, baseEnd_2826821] using wordTrace_append hprefix tailTrace_2826821
  have hstable : (prefixWord ++ tailWord_2826821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826821).length < 2 ^ (prefixWord ++ tailWord_2826821).sum := by decide
  have hdescent : baseEnd_2826821 < baseStart_2826821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826837 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 1, 3, 5]
def baseStart_2826837 : Nat := 118140960795 + 2826837 * 2 ^ 59
def prefixEnd_2826837 : Nat := 4983230072969 + 3 ^ 40 * 2826837 * 2
def baseEnd_2826837 : Nat := 1451526112913861720937119

theorem tailTrace_2826837 : CollatzResearch.WordTrace tailWord_2826837 prefixEnd_2826837 1451526112913861720937119 := by
  unfold tailWord_2826837
  simp only [CollatzResearch.WordTrace]
  refine ⟨103103215659859809168206765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68735477106573206112137843 103103215659859809168206765)
  ·
    refine ⟨38663705872447428438077537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103103215659859809168206765 38663705872447428438077537)
    ·
      refine ⟨28997779404335571328558153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38663705872447428438077537 28997779404335571328558153)
      ·
        refine ⟨21748334553251678496418615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28997779404335571328558153 21748334553251678496418615)
        ·
          refine ⟨32622501829877517744627923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21748334553251678496418615 32622501829877517744627923)
          ·
            refine ⟨48933752744816276616941885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32622501829877517744627923 48933752744816276616941885)
            ·
              refine ⟨18350157279306103731353207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48933752744816276616941885 18350157279306103731353207)
              ·
                refine ⟨27525235918959155597029811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18350157279306103731353207 27525235918959155597029811)
                ·
                  refine ⟨41287853878438733395544717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27525235918959155597029811 41287853878438733395544717)
                  ·
                    refine ⟨15482945204414525023329269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41287853878438733395544717 15482945204414525023329269)
                    ·
                      refine ⟨1451526112913861720937119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15482945204414525023329269 1451526112913861720937119)
                      ·
                        rfl

theorem cell23_2826837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_2826837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826837 prefixEnd_2826837 := by exact prefixLift 2826837
  have htrace : WordTrace (prefixWord ++ tailWord_2826837) baseStart_2826837 baseEnd_2826837 := by
    simpa [prefixWord, tailWord_2826837, baseEnd_2826837] using wordTrace_append hprefix tailTrace_2826837
  have hstable : (prefixWord ++ tailWord_2826837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826837).length < 2 ^ (prefixWord ++ tailWord_2826837).sum := by decide
  have hdescent : baseEnd_2826837 < baseStart_2826837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826846 : List Nat := [4, 4, 1, 2, 2, 1, 1, 1, 3, 2, 2]
def baseStart_2826846 : Nat := 118140960795 + 2826846 * 2 ^ 59
def prefixEnd_2826846 : Nat := 4983230072969 + 3 ^ 40 * 2826846 * 2
def baseEnd_2826846 : Nat := 1451530734239752185724579

theorem tailTrace_2826846 : CollatzResearch.WordTrace tailWord_2826846 prefixEnd_2826846 1451530734239752185724579 := by
  unfold tailWord_2826846
  simp only [CollatzResearch.WordTrace]
  refine ⟨12887942989603400463160549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 68735695944551469136856261 12887942989603400463160549)
  ·
    refine ⟨2416489310550637586842603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12887942989603400463160549 2416489310550637586842603)
    ·
      refine ⟨3624733965825956380263905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2416489310550637586842603 3624733965825956380263905)
      ·
        refine ⟨2718550474369467285197929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3624733965825956380263905 2718550474369467285197929)
        ·
          refine ⟨2038912855777100463898447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2718550474369467285197929 2038912855777100463898447)
          ·
            refine ⟨3058369283665650695847671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2038912855777100463898447 3058369283665650695847671)
            ·
              refine ⟨4587553925498476043771507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3058369283665650695847671 4587553925498476043771507)
              ·
                refine ⟨6881330888247714065657261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4587553925498476043771507 6881330888247714065657261)
                ·
                  refine ⟨2580499083092892774621473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6881330888247714065657261 2580499083092892774621473)
                  ·
                    refine ⟨1935374312319669580966105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2580499083092892774621473 1935374312319669580966105)
                    ·
                      refine ⟨1451530734239752185724579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1935374312319669580966105 1451530734239752185724579)
                      ·
                        rfl

theorem cell23_2826846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_2826846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826846 prefixEnd_2826846 := by exact prefixLift 2826846
  have htrace : WordTrace (prefixWord ++ tailWord_2826846) baseStart_2826846 baseEnd_2826846 := by
    simpa [prefixWord, tailWord_2826846, baseEnd_2826846] using wordTrace_append hprefix tailTrace_2826846
  have hstable : (prefixWord ++ tailWord_2826846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826846).length < 2 ^ (prefixWord ++ tailWord_2826846).sum := by decide
  have hdescent : baseEnd_2826846 < baseStart_2826846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826847 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 4]
def baseStart_2826847 : Nat := 118140960795 + 2826847 * 2 ^ 59
def prefixEnd_2826847 : Nat := 4983230072969 + 3 ^ 40 * 2826847 * 2
def baseEnd_2826847 : Nat := 1451531247720406681812073

theorem tailTrace_2826847 : CollatzResearch.WordTrace tailWord_2826847 prefixEnd_2826847 1451531247720406681812073 := by
  unfold tailWord_2826847
  simp only [CollatzResearch.WordTrace]
  refine ⟨103103580389823580876070795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68735720259882387250713863 103103580389823580876070795)
  ·
    refine ⟨154655370584735371314106193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103103580389823580876070795 154655370584735371314106193)
    ·
      refine ⟨115991527938551528485579645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154655370584735371314106193 115991527938551528485579645)
      ·
        refine ⟨43496822976956823182092367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115991527938551528485579645 43496822976956823182092367)
        ·
          refine ⟨65245234465435234773138551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43496822976956823182092367 65245234465435234773138551)
          ·
            refine ⟨97867851698152852159707827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65245234465435234773138551 97867851698152852159707827)
            ·
              refine ⟨146801777547229278239561741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97867851698152852159707827 146801777547229278239561741)
              ·
                refine ⟨55050666580210979339835653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146801777547229278239561741 55050666580210979339835653)
                ·
                  refine ⟨10321999983789558626219185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55050666580210979339835653 10321999983789558626219185)
                  ·
                    refine ⟨7741499987842168969664389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10321999983789558626219185 7741499987842168969664389)
                    ·
                      refine ⟨1451531247720406681812073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7741499987842168969664389 1451531247720406681812073)
                      ·
                        rfl

theorem cell23_2826847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_2826847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826847 prefixEnd_2826847 := by exact prefixLift 2826847
  have htrace : WordTrace (prefixWord ++ tailWord_2826847) baseStart_2826847 baseEnd_2826847 := by
    simpa [prefixWord, tailWord_2826847, baseEnd_2826847] using wordTrace_append hprefix tailTrace_2826847
  have hstable : (prefixWord ++ tailWord_2826847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826847).length < 2 ^ (prefixWord ++ tailWord_2826847).sum := by decide
  have hdescent : baseEnd_2826847 < baseStart_2826847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826851 : List Nat := [1, 1, 1, 5, 1, 2, 1, 3, 4, 2, 2]
def baseStart_2826851 : Nat := 118140960795 + 2826851 * 2 ^ 59
def prefixEnd_2826851 : Nat := 4983230072969 + 3 ^ 40 * 2826851 * 2
def baseEnd_2826851 : Nat := 1451533301643024666162055

theorem tailTrace_2826851 : CollatzResearch.WordTrace tailWord_2826851 prefixEnd_2826851 1451533301643024666162055 := by
  unfold tailWord_2826851
  simp only [CollatzResearch.WordTrace]
  refine ⟨103103726281809089559216407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 68735817521206059706144271 103103726281809089559216407)
  ·
    refine ⟨154655589422713634338824611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103103726281809089559216407 154655589422713634338824611)
    ·
      refine ⟨231983384134070451508236917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154655589422713634338824611 231983384134070451508236917)
      ·
        refine ⟨21748442262569104828897211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 231983384134070451508236917 21748442262569104828897211)
        ·
          refine ⟨32622663393853657243345817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21748442262569104828897211 32622663393853657243345817)
          ·
            refine ⟨24466997545390242932509363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32622663393853657243345817 24466997545390242932509363)
            ·
              refine ⟨36700496318085364398764045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24466997545390242932509363 36700496318085364398764045)
              ·
                refine ⟨13762686119282011649536517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36700496318085364398764045 13762686119282011649536517)
                ·
                  refine ⟨2580503647365377184288097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13762686119282011649536517 2580503647365377184288097)
                  ·
                    refine ⟨1935377735524032888216073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2580503647365377184288097 1935377735524032888216073)
                    ·
                      refine ⟨1451533301643024666162055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1935377735524032888216073 1451533301643024666162055)
                      ·
                        rfl

theorem cell23_2826851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_2826851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826851 prefixEnd_2826851 := by exact prefixLift 2826851
  have htrace : WordTrace (prefixWord ++ tailWord_2826851) baseStart_2826851 baseEnd_2826851 := by
    simpa [prefixWord, tailWord_2826851, baseEnd_2826851] using wordTrace_append hprefix tailTrace_2826851
  have hstable : (prefixWord ++ tailWord_2826851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826851).length < 2 ^ (prefixWord ++ tailWord_2826851).sum := by decide
  have hdescent : baseEnd_2826851 < baseStart_2826851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2826904 : List Nat := [2, 1, 2, 4, 1, 1, 1, 4, 2, 5]
def baseStart_2826904 : Nat := 118140960795 + 2826904 * 2 ^ 59
def prefixEnd_2826904 : Nat := 4983230072969 + 3 ^ 40 * 2826904 * 2
def baseEnd_2826904 : Nat := 483853505372570986266437

theorem tailTrace_2826904 : CollatzResearch.WordTrace tailWord_2826904 prefixEnd_2826904 483853505372570986266437 := by
  unfold tailWord_2826904
  simp only [CollatzResearch.WordTrace]
  refine ⟨51552829675308539805447883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 68737106233744719740597177 51552829675308539805447883)
  ·
    refine ⟨77329244512962809708171825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51552829675308539805447883 77329244512962809708171825)
    ·
      refine ⟨57996933384722107281128869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77329244512962809708171825 57996933384722107281128869)
      ·
        refine ⟨10874425009635395115211663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57996933384722107281128869 10874425009635395115211663)
        ·
          refine ⟨16311637514453092672817495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10874425009635395115211663 16311637514453092672817495)
          ·
            refine ⟨24467456271679639009226243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16311637514453092672817495 24467456271679639009226243)
            ·
              refine ⟨36701184407519458513839365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24467456271679639009226243 36701184407519458513839365)
              ·
                refine ⟨6881472076409898471344881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36701184407519458513839365 6881472076409898471344881)
                ·
                  refine ⟨5161104057307423853508661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6881472076409898471344881 5161104057307423853508661)
                  ·
                    refine ⟨483853505372570986266437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5161104057307423853508661 483853505372570986266437)
                    ·
                      rfl

theorem cell23_2826904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 2, 5].length) (baseStart_2826904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2826904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2826904 prefixEnd_2826904 := by exact prefixLift 2826904
  have htrace : WordTrace (prefixWord ++ tailWord_2826904) baseStart_2826904 baseEnd_2826904 := by
    simpa [prefixWord, tailWord_2826904, baseEnd_2826904] using wordTrace_append hprefix tailTrace_2826904
  have hstable : (prefixWord ++ tailWord_2826904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2826904).length < 2 ^ (prefixWord ++ tailWord_2826904).sum := by decide
  have hdescent : baseEnd_2826904 < baseStart_2826904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2826904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
