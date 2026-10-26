import V185TrunkScan23Chunk0368

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2181859 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 4, 5]
def baseStart_2181859 : Nat := 118140960795 + 2181859 * 2 ^ 59
def prefixEnd_2181859 : Nat := 4983230072969 + 3 ^ 40 * 2181859 * 2
def baseEnd_2181859 : Nat := 373447462446094733442773

theorem tailTrace_2181859 : CollatzResearch.WordTrace tailWord_2181859 prefixEnd_2181859 373447462446094733442773 := by
  unfold tailWord_2181859
  simp only [CollatzResearch.WordTrace]
  refine ⟨79578935402504949695572631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53052623601669966463715087 79578935402504949695572631)
  ·
    refine ⟨119368403103757424543358947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79578935402504949695572631 119368403103757424543358947)
    ·
      refine ⟨179052604655636136815038421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119368403103757424543358947 179052604655636136815038421)
      ·
        refine ⟨4196545421616471956602463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 179052604655636136815038421 4196545421616471956602463)
        ·
          refine ⟨6294818132424707934903695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4196545421616471956602463 6294818132424707934903695)
          ·
            refine ⟨9442227198637061902355543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6294818132424707934903695 9442227198637061902355543)
            ·
              refine ⟨14163340797955592853533315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9442227198637061902355543 14163340797955592853533315)
              ·
                refine ⟨21245011196933389280299973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14163340797955592853533315 21245011196933389280299973)
                ·
                  refine ⟨3983439599425010490056245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21245011196933389280299973 3983439599425010490056245)
                  ·
                    refine ⟨373447462446094733442773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3983439599425010490056245 373447462446094733442773)
                    ·
                      rfl

theorem cell23_2181859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 5].length) (baseStart_2181859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181859 prefixEnd_2181859 := by exact prefixLift 2181859
  have htrace : WordTrace (prefixWord ++ tailWord_2181859) baseStart_2181859 baseEnd_2181859 := by
    simpa [prefixWord, tailWord_2181859, baseEnd_2181859] using wordTrace_append hprefix tailTrace_2181859
  have hstable : (prefixWord ++ tailWord_2181859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181859).length < 2 ^ (prefixWord ++ tailWord_2181859).sum := by decide
  have hdescent : baseEnd_2181859 < baseStart_2181859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181869 : List Nat := [1, 5, 1, 2, 1, 1, 3, 1, 1, 2, 5]
def baseStart_2181869 : Nat := 118140960795 + 2181869 * 2 ^ 59
def prefixEnd_2181869 : Nat := 4983230072969 + 3 ^ 40 * 2181869 * 2
def baseEnd_2181869 : Nat := 1120347522144829161203273

theorem tailTrace_2181869 : CollatzResearch.WordTrace tailWord_2181869 prefixEnd_2181869 1120347522144829161203273 := by
  unfold tailWord_2181869
  simp only [CollatzResearch.WordTrace]
  refine ⟨79579300132468721403436661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53052866754979147602291107 79579300132468721403436661)
  ·
    refine ⟨7460559387418942631572187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79579300132468721403436661 7460559387418942631572187)
    ·
      refine ⟨11190839081128413947358281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7460559387418942631572187 11190839081128413947358281)
      ·
        refine ⟨8393129310846310460518711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11190839081128413947358281 8393129310846310460518711)
        ·
          refine ⟨12589693966269465690778067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8393129310846310460518711 12589693966269465690778067)
          ·
            refine ⟨18884540949404198536167101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12589693966269465690778067 18884540949404198536167101)
            ·
              refine ⟨7081702856026574451062663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18884540949404198536167101 7081702856026574451062663)
              ·
                refine ⟨10622554284039861676593995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7081702856026574451062663 10622554284039861676593995)
                ·
                  refine ⟨15933831426059792514890993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10622554284039861676593995 15933831426059792514890993)
                  ·
                    refine ⟨11950373569544844386168245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15933831426059792514890993 11950373569544844386168245)
                    ·
                      refine ⟨1120347522144829161203273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11950373569544844386168245 1120347522144829161203273)
                      ·
                        rfl

theorem cell23_2181869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_2181869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181869 prefixEnd_2181869 := by exact prefixLift 2181869
  have htrace : WordTrace (prefixWord ++ tailWord_2181869) baseStart_2181869 baseEnd_2181869 := by
    simpa [prefixWord, tailWord_2181869, baseEnd_2181869] using wordTrace_append hprefix tailTrace_2181869
  have hstable : (prefixWord ++ tailWord_2181869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181869).length < 2 ^ (prefixWord ++ tailWord_2181869).sum := by decide
  have hdescent : baseEnd_2181869 < baseStart_2181869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181879 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 1, 6, 2]
def baseStart_2181879 : Nat := 118140960795 + 2181879 * 2 ^ 59
def prefixEnd_2181879 : Nat := 4983230072969 + 3 ^ 40 * 2181879 * 2
def baseEnd_2181879 : Nat := 1120352656951374122078227

theorem tailTrace_2181879 : CollatzResearch.WordTrace tailWord_2181879 prefixEnd_2181879 1120352656951374122078227 := by
  unfold tailWord_2181879
  simp only [CollatzResearch.WordTrace]
  refine ⟨79579664862432493111300691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53053109908288328740867127 79579664862432493111300691)
  ·
    refine ⟨119369497293648739666951037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79579664862432493111300691 119369497293648739666951037)
    ·
      refine ⟨44763561485118277375106639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119369497293648739666951037 44763561485118277375106639)
      ·
        refine ⟨67145342227677416062659959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44763561485118277375106639 67145342227677416062659959)
        ·
          refine ⟨100718013341516124093989939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67145342227677416062659959 100718013341516124093989939)
          ·
            refine ⟨151077020012274186140984909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100718013341516124093989939 151077020012274186140984909)
            ·
              refine ⟨56653882504602819802869341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151077020012274186140984909 56653882504602819802869341)
              ·
                refine ⟨21245205939226057426076003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56653882504602819802869341 21245205939226057426076003)
                ·
                  refine ⟨31867808908839086139114005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21245205939226057426076003 31867808908839086139114005)
                  ·
                    refine ⟨1493803542601832162770969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31867808908839086139114005 1493803542601832162770969)
                    ·
                      refine ⟨1120352656951374122078227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1493803542601832162770969 1120352656951374122078227)
                      ·
                        rfl

theorem cell23_2181879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 6, 2].length) (baseStart_2181879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181879 prefixEnd_2181879 := by exact prefixLift 2181879
  have htrace : WordTrace (prefixWord ++ tailWord_2181879) baseStart_2181879 baseEnd_2181879 := by
    simpa [prefixWord, tailWord_2181879, baseEnd_2181879] using wordTrace_append hprefix tailTrace_2181879
  have hstable : (prefixWord ++ tailWord_2181879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181879).length < 2 ^ (prefixWord ++ tailWord_2181879).sum := by decide
  have hdescent : baseEnd_2181879 < baseStart_2181879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181889 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 5, 4]
def baseStart_2181889 : Nat := 118140960795 + 2181889 * 2 ^ 59
def prefixEnd_2181889 : Nat := 4983230072969 + 3 ^ 40 * 2181889 * 2
def baseEnd_2181889 : Nat := 373452597252639694317727

theorem tailTrace_2181889 : CollatzResearch.WordTrace tailWord_2181889 prefixEnd_2181889 373452597252639694317727 := by
  unfold tailWord_2181889
  simp only [CollatzResearch.WordTrace]
  refine ⟨79580029592396264819164721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53053353061597509879443147 79580029592396264819164721)
  ·
    refine ⟨59685022194297198614373541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79580029592396264819164721 59685022194297198614373541)
    ·
      refine ⟨11190941661430724740195039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59685022194297198614373541 11190941661430724740195039)
      ·
        refine ⟨16786412492146087110292559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11190941661430724740195039 16786412492146087110292559)
        ·
          refine ⟨25179618738219130665438839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16786412492146087110292559 25179618738219130665438839)
          ·
            refine ⟨37769428107328695998158259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25179618738219130665438839 37769428107328695998158259)
            ·
              refine ⟨56654142160993043997237389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37769428107328695998158259 56654142160993043997237389)
              ·
                refine ⟨21245303310372391498964021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56654142160993043997237389 21245303310372391498964021)
                ·
                  refine ⟨1991747185347411703027877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21245303310372391498964021 1991747185347411703027877)
                  ·
                    refine ⟨373452597252639694317727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1991747185347411703027877 373452597252639694317727)
                    ·
                      rfl

theorem cell23_2181889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_2181889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181889 prefixEnd_2181889 := by exact prefixLift 2181889
  have htrace : WordTrace (prefixWord ++ tailWord_2181889) baseStart_2181889 baseEnd_2181889 := by
    simpa [prefixWord, tailWord_2181889, baseEnd_2181889] using wordTrace_append hprefix tailTrace_2181889
  have hstable : (prefixWord ++ tailWord_2181889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181889).length < 2 ^ (prefixWord ++ tailWord_2181889).sum := by decide
  have hdescent : baseEnd_2181889 < baseStart_2181889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181896 : List Nat := [2, 1, 3, 2, 2, 3, 2, 1, 2, 1, 4]
def baseStart_2181896 : Nat := 118140960795 + 2181896 * 2 ^ 59
def prefixEnd_2181896 : Nat := 4983230072969 + 3 ^ 40 * 2181896 * 2
def baseEnd_2181896 : Nat := 1120361386122500555565649

theorem tailTrace_2181896 : CollatzResearch.WordTrace tailWord_2181896 prefixEnd_2181896 1120361386122500555565649 := by
  unfold tailWord_2181896
  simp only [CollatzResearch.WordTrace]
  refine ⟨39790142451685452507334771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53053523268913936676446361 39790142451685452507334771)
  ·
    refine ⟨59685213677528178761002157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39790142451685452507334771 59685213677528178761002157)
    ·
      refine ⟨22381955129073067035375809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59685213677528178761002157 22381955129073067035375809)
      ·
        refine ⟨16786466346804800276531857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22381955129073067035375809 16786466346804800276531857)
        ·
          refine ⟨12589849760103600207398893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16786466346804800276531857 12589849760103600207398893)
          ·
            refine ⟨4721193660038850077774585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12589849760103600207398893 4721193660038850077774585)
            ·
              refine ⟨3540895245029137558330939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4721193660038850077774585 3540895245029137558330939)
              ·
                refine ⟨5311342867543706337496409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3540895245029137558330939 5311342867543706337496409)
                ·
                  refine ⟨3983507150657779753122307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5311342867543706337496409 3983507150657779753122307)
                  ·
                    refine ⟨5975260725986669629683461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3983507150657779753122307 5975260725986669629683461)
                    ·
                      refine ⟨1120361386122500555565649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5975260725986669629683461 1120361386122500555565649)
                      ·
                        rfl

theorem cell23_2181896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_2181896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181896 prefixEnd_2181896 := by exact prefixLift 2181896
  have htrace : WordTrace (prefixWord ++ tailWord_2181896) baseStart_2181896 baseEnd_2181896 := by
    simpa [prefixWord, tailWord_2181896, baseEnd_2181896] using wordTrace_append hprefix tailTrace_2181896
  have hstable : (prefixWord ++ tailWord_2181896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181896).length < 2 ^ (prefixWord ++ tailWord_2181896).sum := by decide
  have hdescent : baseEnd_2181896 < baseStart_2181896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181916 : List Nat := [2, 2, 3, 1, 1, 3, 2, 2, 2, 2, 3]
def baseStart_2181916 : Nat := 118140960795 + 2181916 * 2 ^ 59
def prefixEnd_2181916 : Nat := 4983230072969 + 3 ^ 40 * 2181916 * 2
def baseEnd_2181916 : Nat := 1120371655735590477315557

theorem tailTrace_2181916 : CollatzResearch.WordTrace tailWord_2181916 prefixEnd_2181916 1120371655735590477315557 := by
  unfold tailWord_2181916
  simp only [CollatzResearch.WordTrace]
  refine ⟨39790507181649224215198801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53054009575532298953598401 39790507181649224215198801)
  ·
    refine ⟨29842880386236918161399101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39790507181649224215198801 29842880386236918161399101)
    ·
      refine ⟨11191080144838844310524663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29842880386236918161399101 11191080144838844310524663)
      ·
        refine ⟨16786620217258266465786995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11191080144838844310524663 16786620217258266465786995)
        ·
          refine ⟨25179930325887399698680493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16786620217258266465786995 25179930325887399698680493)
          ·
            refine ⟨9442473872207774887005185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25179930325887399698680493 9442473872207774887005185)
            ·
              refine ⟨7081855404155831165253889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9442473872207774887005185 7081855404155831165253889)
              ·
                refine ⟨5311391553116873373940417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7081855404155831165253889 5311391553116873373940417)
                ·
                  refine ⟨3983543664837655030455313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5311391553116873373940417 3983543664837655030455313)
                  ·
                    refine ⟨2987657748628241272841485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3983543664837655030455313 2987657748628241272841485)
                    ·
                      refine ⟨1120371655735590477315557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2987657748628241272841485 1120371655735590477315557)
                      ·
                        rfl

theorem cell23_2181916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_2181916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181916 prefixEnd_2181916 := by exact prefixLift 2181916
  have htrace : WordTrace (prefixWord ++ tailWord_2181916) baseStart_2181916 baseEnd_2181916 := by
    simpa [prefixWord, tailWord_2181916, baseEnd_2181916] using wordTrace_append hprefix tailTrace_2181916
  have hstable : (prefixWord ++ tailWord_2181916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181916).length < 2 ^ (prefixWord ++ tailWord_2181916).sum := by decide
  have hdescent : baseEnd_2181916 < baseStart_2181916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181919 : List Nat := [1, 1, 2, 4, 2, 2, 1, 4, 6]
def baseStart_2181919 : Nat := 118140960795 + 2181919 * 2 ^ 59
def prefixEnd_2181919 : Nat := 4983230072969 + 3 ^ 40 * 2181919 * 2
def baseEnd_2181919 : Nat := 124485910686394885064227

theorem tailTrace_2181919 : CollatzResearch.WordTrace tailWord_2181919 prefixEnd_2181919 124485910686394885064227 := by
  unfold tailWord_2181919
  simp only [CollatzResearch.WordTrace]
  refine ⟨79581123782287579942756811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53054082521525053295171207 79581123782287579942756811)
  ·
    refine ⟨119371685673431369914135217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79581123782287579942756811 119371685673431369914135217)
    ·
      refine ⟨89528764255073527435601413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119371685673431369914135217 89528764255073527435601413)
      ·
        refine ⟨16786643297826286394175265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89528764255073527435601413 16786643297826286394175265)
        ·
          refine ⟨12589982473369714795631449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16786643297826286394175265 12589982473369714795631449)
          ·
            refine ⟨9442486855027286096723587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12589982473369714795631449 9442486855027286096723587)
            ·
              refine ⟨14163730282540929145085381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9442486855027286096723587 14163730282540929145085381)
              ·
                refine ⟨2655699427976424214703509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14163730282540929145085381 2655699427976424214703509)
                ·
                  refine ⟨124485910686394885064227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2655699427976424214703509 124485910686394885064227)
                  ·
                    rfl

theorem cell23_2181919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 6].length) (baseStart_2181919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181919 prefixEnd_2181919 := by exact prefixLift 2181919
  have htrace : WordTrace (prefixWord ++ tailWord_2181919) baseStart_2181919 baseEnd_2181919 := by
    simpa [prefixWord, tailWord_2181919, baseEnd_2181919] using wordTrace_append hprefix tailTrace_2181919
  have hstable : (prefixWord ++ tailWord_2181919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181919).length < 2 ^ (prefixWord ++ tailWord_2181919).sum := by decide
  have hdescent : baseEnd_2181919 < baseStart_2181919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181930 : List Nat := [3, 1, 4, 3, 1, 1, 1, 1, 2, 4, 2]
def baseStart_2181930 : Nat := 118140960795 + 2181930 * 2 ^ 59
def prefixEnd_2181930 : Nat := 4983230072969 + 3 ^ 40 * 2181930 * 2
def baseEnd_2181930 : Nat := 1120378844464753422540493

theorem tailTrace_2181930 : CollatzResearch.WordTrace tailWord_2181930 prefixEnd_2181930 1120378844464753422540493 := by
  unfold tailWord_2181930
  simp only [CollatzResearch.WordTrace]
  refine ⟨19895381246311932205351811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53054349990165152547604829 19895381246311932205351811)
  ·
    refine ⟨29843071869467898308027717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19895381246311932205351811 29843071869467898308027717)
    ·
      refine ⟨5595575975525230932755197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29843071869467898308027717 5595575975525230932755197)
      ·
        refine ⟨2098340990821961599783199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5595575975525230932755197 2098340990821961599783199)
        ·
          refine ⟨3147511486232942399674799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2098340990821961599783199 3147511486232942399674799)
          ·
            refine ⟨4721267229349413599512199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3147511486232942399674799 4721267229349413599512199)
            ·
              refine ⟨7081900844024120399268299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4721267229349413599512199 7081900844024120399268299)
              ·
                refine ⟨10622851266036180598902449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7081900844024120399268299 10622851266036180598902449)
                ·
                  refine ⟨7967138449527135449176837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10622851266036180598902449 7967138449527135449176837)
                  ·
                    refine ⟨1493838459286337896720657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7967138449527135449176837 1493838459286337896720657)
                    ·
                      refine ⟨1120378844464753422540493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1493838459286337896720657 1120378844464753422540493)
                      ·
                        rfl

theorem cell23_2181930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_2181930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181930 prefixEnd_2181930 := by exact prefixLift 2181930
  have htrace : WordTrace (prefixWord ++ tailWord_2181930) baseStart_2181930 baseEnd_2181930 := by
    simpa [prefixWord, tailWord_2181930, baseEnd_2181930] using wordTrace_append hprefix tailTrace_2181930
  have hstable : (prefixWord ++ tailWord_2181930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181930).length < 2 ^ (prefixWord ++ tailWord_2181930).sum := by decide
  have hdescent : baseEnd_2181930 < baseStart_2181930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181950 : List Nat := [4, 2, 1, 2, 3, 2, 1, 1, 2, 2, 3]
def baseStart_2181950 : Nat := 118140960795 + 2181950 * 2 ^ 59
def prefixEnd_2181950 : Nat := 4983230072969 + 3 ^ 40 * 2181950 * 2
def baseEnd_2181950 : Nat := 1120389114077843344290401

theorem tailTrace_2181950 : CollatzResearch.WordTrace tailWord_2181950 prefixEnd_2181950 1120389114077843344290401 := by
  unfold tailWord_2181950
  simp only [CollatzResearch.WordTrace]
  refine ⟨9947781805646909029641913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53054836296783514824756869 9947781805646909029641913)
  ·
    refine ⟨7460836354235181772231435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9947781805646909029641913 7460836354235181772231435)
    ·
      refine ⟨11191254531352772658347153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7460836354235181772231435 11191254531352772658347153)
      ·
        refine ⟨8393440898514579493760365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11191254531352772658347153 8393440898514579493760365)
        ·
          refine ⟨3147540336942967310160137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8393440898514579493760365 3147540336942967310160137)
          ·
            refine ⟨2360655252707225482620103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3147540336942967310160137 2360655252707225482620103)
            ·
              refine ⟨3540982879060838223930155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2360655252707225482620103 3540982879060838223930155)
              ·
                refine ⟨5311474318591257335895233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3540982879060838223930155 5311474318591257335895233)
                ·
                  refine ⟨3983605738943443001921425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5311474318591257335895233 3983605738943443001921425)
                  ·
                    refine ⟨2987704304207582251441069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3983605738943443001921425 2987704304207582251441069)
                    ·
                      refine ⟨1120389114077843344290401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2987704304207582251441069 1120389114077843344290401)
                      ·
                        rfl

theorem cell23_2181950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_2181950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181950 prefixEnd_2181950 := by exact prefixLift 2181950
  have htrace : WordTrace (prefixWord ++ tailWord_2181950) baseStart_2181950 baseEnd_2181950 := by
    simpa [prefixWord, tailWord_2181950, baseEnd_2181950] using wordTrace_append hprefix tailTrace_2181950
  have hstable : (prefixWord ++ tailWord_2181950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181950).length < 2 ^ (prefixWord ++ tailWord_2181950).sum := by decide
  have hdescent : baseEnd_2181950 < baseStart_2181950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181980 : List Nat := [2, 2, 4, 2, 1, 2, 2, 1, 3, 1, 3]
def baseStart_2181980 : Nat := 118140960795 + 2181980 * 2 ^ 59
def prefixEnd_2181980 : Nat := 4983230072969 + 3 ^ 40 * 2181980 * 2
def baseEnd_2181980 : Nat := 1120404518497478226915263

theorem tailTrace_2181980 : CollatzResearch.WordTrace tailWord_2181980 prefixEnd_2181980 1120404518497478226915263 := by
  unfold tailWord_2181980
  simp only [CollatzResearch.WordTrace]
  refine ⟨39791674317533293680363697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53055565756711058240484929 39791674317533293680363697)
  ·
    refine ⟨29843755738149970260272773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39791674317533293680363697 29843755738149970260272773)
    ·
      refine ⟨5595704200903119423801145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29843755738149970260272773 5595704200903119423801145)
      ·
        refine ⟨4196778150677339567850859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5595704200903119423801145 4196778150677339567850859)
        ·
          refine ⟨6295167226016009351776289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4196778150677339567850859 6295167226016009351776289)
          ·
            refine ⟨4721375419512007013832217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6295167226016009351776289 4721375419512007013832217)
            ·
              refine ⟨3541031564634005260374163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4721375419512007013832217 3541031564634005260374163)
              ·
                refine ⟨5311547346951007890561245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3541031564634005260374163 5311547346951007890561245)
                ·
                  refine ⟨1991830255106627958960467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5311547346951007890561245 1991830255106627958960467)
                  ·
                    refine ⟨2987745382659941938440701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1991830255106627958960467 2987745382659941938440701)
                    ·
                      refine ⟨1120404518497478226915263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2987745382659941938440701 1120404518497478226915263)
                      ·
                        rfl

theorem cell23_2181980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_2181980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181980 prefixEnd_2181980 := by exact prefixLift 2181980
  have htrace : WordTrace (prefixWord ++ tailWord_2181980) baseStart_2181980 baseEnd_2181980 := by
    simpa [prefixWord, tailWord_2181980, baseEnd_2181980] using wordTrace_append hprefix tailTrace_2181980
  have hstable : (prefixWord ++ tailWord_2181980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181980).length < 2 ^ (prefixWord ++ tailWord_2181980).sum := by decide
  have hdescent : baseEnd_2181980 < baseStart_2181980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2181989 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 3, 1, 5]
def baseStart_2181989 : Nat := 118140960795 + 2181989 * 2 ^ 59
def prefixEnd_2181989 : Nat := 4983230072969 + 3 ^ 40 * 2181989 * 2
def baseEnd_2181989 : Nat := 1120409139823368691702721

theorem tailTrace_2181989 : CollatzResearch.WordTrace tailWord_2181989 prefixEnd_2181989 1120409139823368691702721 := by
  unfold tailWord_2181989
  simp only [CollatzResearch.WordTrace]
  refine ⟨79583676892033981897805021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53055784594689321265203347 79583676892033981897805021)
  ·
    refine ⟨29843878834512743211676883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79583676892033981897805021 29843878834512743211676883)
    ·
      refine ⟨44765818251769114817515325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29843878834512743211676883 44765818251769114817515325)
      ·
        refine ⟨16787181844413418056568247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44765818251769114817515325 16787181844413418056568247)
        ·
          refine ⟨25180772766620127084852371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16787181844413418056568247 25180772766620127084852371)
          ·
            refine ⟨37771159149930190627278557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25180772766620127084852371 37771159149930190627278557)
            ·
              refine ⟨14164184681223821485229459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37771159149930190627278557 14164184681223821485229459)
              ·
                refine ⟨21246277021835732227844189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14164184681223821485229459 21246277021835732227844189)
                ·
                  refine ⟨7967353883188399585441571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21246277021835732227844189 7967353883188399585441571)
                  ·
                    refine ⟨11951030824782599378162357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7967353883188399585441571 11951030824782599378162357)
                    ·
                      refine ⟨1120409139823368691702721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11951030824782599378162357 1120409139823368691702721)
                      ·
                        rfl

theorem cell23_2181989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_2181989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2181989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2181989 prefixEnd_2181989 := by exact prefixLift 2181989
  have htrace : WordTrace (prefixWord ++ tailWord_2181989) baseStart_2181989 baseEnd_2181989 := by
    simpa [prefixWord, tailWord_2181989, baseEnd_2181989] using wordTrace_append hprefix tailTrace_2181989
  have hstable : (prefixWord ++ tailWord_2181989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2181989).length < 2 ^ (prefixWord ++ tailWord_2181989).sum := by decide
  have hdescent : baseEnd_2181989 < baseStart_2181989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2181989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182003 : List Nat := [1, 1, 1, 2, 2, 1, 6, 2, 3, 2, 2]
def baseStart_2182003 : Nat := 118140960795 + 2182003 * 2 ^ 59
def prefixEnd_2182003 : Nat := 4983230072969 + 3 ^ 40 * 2182003 * 2
def baseEnd_2182003 : Nat := 1120416328552531636927657

theorem tailTrace_2182003 : CollatzResearch.WordTrace tailWord_2182003 prefixEnd_2182003 1120416328552531636927657 := by
  unfold tailWord_2182003
  simp only [CollatzResearch.WordTrace]
  refine ⟨79584187513983262288814663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53056125009322174859209775 79584187513983262288814663)
  ·
    refine ⟨119376281270974893433221995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79584187513983262288814663 119376281270974893433221995)
    ·
      refine ⟨179064421906462340149832993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119376281270974893433221995 179064421906462340149832993)
      ·
        refine ⟨134298316429846755112374745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179064421906462340149832993 134298316429846755112374745)
        ·
          refine ⟨100723737322385066334281059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134298316429846755112374745 100723737322385066334281059)
          ·
            refine ⟨151085605983577599501421589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100723737322385066334281059 151085605983577599501421589)
            ·
              refine ⟨7082137780480199976629137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 151085605983577599501421589 7082137780480199976629137)
              ·
                refine ⟨5311603335360149982471853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7082137780480199976629137 5311603335360149982471853)
                ·
                  refine ⟨1991851250760056243426945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5311603335360149982471853 1991851250760056243426945)
                  ·
                    refine ⟨1493888438070042182570209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1991851250760056243426945 1493888438070042182570209)
                    ·
                      refine ⟨1120416328552531636927657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1493888438070042182570209 1120416328552531636927657)
                      ·
                        rfl

theorem cell23_2182003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 3, 2, 2].length) (baseStart_2182003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182003 prefixEnd_2182003 := by exact prefixLift 2182003
  have htrace : WordTrace (prefixWord ++ tailWord_2182003) baseStart_2182003 baseEnd_2182003 := by
    simpa [prefixWord, tailWord_2182003, baseEnd_2182003] using wordTrace_append hprefix tailTrace_2182003
  have hstable : (prefixWord ++ tailWord_2182003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182003).length < 2 ^ (prefixWord ++ tailWord_2182003).sum := by decide
  have hdescent : baseEnd_2182003 < baseStart_2182003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182009 : List Nat := [1, 2, 1, 3, 2, 4, 1, 9]
def baseStart_2182009 : Nat := 118140960795 + 2182009 * 2 ^ 59
def prefixEnd_2182009 : Nat := 4983230072969 + 3 ^ 40 * 2182009 * 2
def baseEnd_2182009 : Nat := 41497015164313281979727

theorem tailTrace_2182009 : CollatzResearch.WordTrace tailWord_2182009 prefixEnd_2182009 41497015164313281979727 := by
  unfold tailWord_2182009
  simp only [CollatzResearch.WordTrace]
  refine ⟨79584406351961525313533081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53056270901307683542355387 79584406351961525313533081)
  ·
    refine ⟨59688304763971143985149811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79584406351961525313533081 59688304763971143985149811)
    ·
      refine ⟨89532457145956715977724717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59688304763971143985149811 89532457145956715977724717)
      ·
        refine ⟨33574671429733768491646769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89532457145956715977724717 33574671429733768491646769)
        ·
          refine ⟨25181003572300326368735077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33574671429733768491646769 25181003572300326368735077)
          ·
            refine ⟨4721438169806311194137827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25181003572300326368735077 4721438169806311194137827)
            ·
              refine ⟨7082157254709466791206741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4721438169806311194137827 7082157254709466791206741)
              ·
                refine ⟨41497015164313281979727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7082157254709466791206741 41497015164313281979727)
                ·
                  rfl

theorem cell23_2182009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 9].length) (baseStart_2182009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182009 prefixEnd_2182009 := by exact prefixLift 2182009
  have htrace : WordTrace (prefixWord ++ tailWord_2182009) baseStart_2182009 baseEnd_2182009 := by
    simpa [prefixWord, tailWord_2182009, baseEnd_2182009] using wordTrace_append hprefix tailTrace_2182009
  have hstable : (prefixWord ++ tailWord_2182009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182009).length < 2 ^ (prefixWord ++ tailWord_2182009).sum := by decide
  have hdescent : baseEnd_2182009 < baseStart_2182009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182023 : List Nat := [1, 1, 4, 2, 3, 1, 2, 3, 1, 2, 3]
def baseStart_2182023 : Nat := 118140960795 + 2182023 * 2 ^ 59
def prefixEnd_2182023 : Nat := 4983230072969 + 3 ^ 40 * 2182023 * 2
def baseEnd_2182023 : Nat := 1120426598165621558677565

theorem tailTrace_2182023 : CollatzResearch.WordTrace tailWord_2182023 prefixEnd_2182023 1120426598165621558677565 := by
  unfold tailWord_2182023
  simp only [CollatzResearch.WordTrace]
  refine ⟨79584916973910805704542723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53056611315940537136361815 79584916973910805704542723)
  ·
    refine ⟨119377375460866208556814085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79584916973910805704542723 119377375460866208556814085)
    ·
      refine ⟨22383257898912414104402641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119377375460866208556814085 22383257898912414104402641)
      ·
        refine ⟨16787443424184310578301981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22383257898912414104402641 16787443424184310578301981)
        ·
          refine ⟨6295291284069116466863243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16787443424184310578301981 6295291284069116466863243)
          ·
            refine ⟨9442936926103674700294865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6295291284069116466863243 9442936926103674700294865)
            ·
              refine ⟨7082202694577756025221149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9442936926103674700294865 7082202694577756025221149)
              ·
                refine ⟨2655826010466658509457931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7082202694577756025221149 2655826010466658509457931)
                ·
                  refine ⟨3983739015699987764186897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2655826010466658509457931 3983739015699987764186897)
                  ·
                    refine ⟨2987804261774990823140173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3983739015699987764186897 2987804261774990823140173)
                    ·
                      refine ⟨1120426598165621558677565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2987804261774990823140173 1120426598165621558677565)
                      ·
                        rfl

theorem cell23_2182023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_2182023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182023 prefixEnd_2182023 := by exact prefixLift 2182023
  have htrace : WordTrace (prefixWord ++ tailWord_2182023) baseStart_2182023 baseEnd_2182023 := by
    simpa [prefixWord, tailWord_2182023, baseEnd_2182023] using wordTrace_append hprefix tailTrace_2182023
  have hstable : (prefixWord ++ tailWord_2182023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182023).length < 2 ^ (prefixWord ++ tailWord_2182023).sum := by decide
  have hdescent : baseEnd_2182023 < baseStart_2182023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182026 : List Nat := [3, 1, 2, 4, 1, 3, 9]
def baseStart_2182026 : Nat := 118140960795 + 2182026 * 2 ^ 59
def prefixEnd_2182026 : Nat := 4983230072969 + 3 ^ 40 * 2182026 * 2
def baseEnd_2182026 : Nat := 13832446155649198110371

theorem tailTrace_2182026 : CollatzResearch.WordTrace tailWord_2182026 prefixEnd_2182026 13832446155649198110371 := by
  unfold tailWord_2182026
  simp only [CollatzResearch.WordTrace]
  refine ⟨19896256598224984304225483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53056684261933291477934621 19896256598224984304225483)
  ·
    refine ⟨29844384897337476456338225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19896256598224984304225483 29844384897337476456338225)
    ·
      refine ⟨22383288673003107342253669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29844384897337476456338225 22383288673003107342253669)
      ·
        refine ⟨4196866626188082626672563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22383288673003107342253669 4196866626188082626672563)
        ·
          refine ⟨6295299939282123940008845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4196866626188082626672563 6295299939282123940008845)
          ·
            refine ⟨2360737477230796477503317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6295299939282123940008845 2360737477230796477503317)
            ·
              refine ⟨13832446155649198110371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2360737477230796477503317 13832446155649198110371)
              ·
                rfl

theorem cell23_2182026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 9].length) (baseStart_2182026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182026 prefixEnd_2182026 := by exact prefixLift 2182026
  have htrace : WordTrace (prefixWord ++ tailWord_2182026) baseStart_2182026 baseEnd_2182026 := by
    simpa [prefixWord, tailWord_2182026, baseEnd_2182026] using wordTrace_append hprefix tailTrace_2182026
  have hstable : (prefixWord ++ tailWord_2182026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182026).length < 2 ^ (prefixWord ++ tailWord_2182026).sum := by decide
  have hdescent : baseEnd_2182026 < baseStart_2182026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182039 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 2, 7]
def baseStart_2182039 : Nat := 118140960795 + 2182039 * 2 ^ 59
def prefixEnd_2182039 : Nat := 4983230072969 + 3 ^ 40 * 2182039 * 2
def baseEnd_2182039 : Nat := 373478271285364498692497

theorem tailTrace_2182039 : CollatzResearch.WordTrace tailWord_2182039 prefixEnd_2182039 373478271285364498692497 := by
  unfold tailWord_2182039
  simp only [CollatzResearch.WordTrace]
  refine ⟨79585500541852840437125171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53057000361235226958083447 79585500541852840437125171)
  ·
    refine ⟨119378250812779260655687757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79585500541852840437125171 119378250812779260655687757)
    ·
      refine ⟨44766844054792222745882909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119378250812779260655687757 44766844054792222745882909)
      ·
        refine ⟨16787566520547083529706091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44766844054792222745882909 16787566520547083529706091)
        ·
          refine ⟨25181349780820625294559137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16787566520547083529706091 25181349780820625294559137)
          ·
            refine ⟨18886012335615468970919353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25181349780820625294559137 18886012335615468970919353)
            ·
              refine ⟨14164509251711601728189515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18886012335615468970919353 14164509251711601728189515)
              ·
                refine ⟨21246763877567402592284273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14164509251711601728189515 21246763877567402592284273)
                ·
                  refine ⟨15935072908175551944213205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21246763877567402592284273 15935072908175551944213205)
                  ·
                    refine ⟨373478271285364498692497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15935072908175551944213205 373478271285364498692497)
                    ·
                      rfl

theorem cell23_2182039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 7].length) (baseStart_2182039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182039 prefixEnd_2182039 := by exact prefixLift 2182039
  have htrace : WordTrace (prefixWord ++ tailWord_2182039) baseStart_2182039 baseEnd_2182039 := by
    simpa [prefixWord, tailWord_2182039, baseEnd_2182039] using wordTrace_append hprefix tailTrace_2182039
  have hstable : (prefixWord ++ tailWord_2182039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182039).length < 2 ^ (prefixWord ++ tailWord_2182039).sum := by decide
  have hdescent : baseEnd_2182039 < baseStart_2182039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182059 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 4]
def baseStart_2182059 : Nat := 118140960795 + 2182059 * 2 ^ 59
def prefixEnd_2182059 : Nat := 4983230072969 + 3 ^ 40 * 2182059 * 2
def baseEnd_2182059 : Nat := 1120445083469183417827399

theorem tailTrace_2182059 : CollatzResearch.WordTrace tailWord_2182059 prefixEnd_2182059 1120445083469183417827399 := by
  unfold tailWord_2182059
  simp only [CollatzResearch.WordTrace]
  refine ⟨79586230001780383852853231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53057486667853589235235487 79586230001780383852853231)
  ·
    refine ⟨119379345002670575779279847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79586230001780383852853231 119379345002670575779279847)
    ·
      refine ⟨179069017504005863668919771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119379345002670575779279847 179069017504005863668919771)
      ·
        refine ⟨268603526256008795503379657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179069017504005863668919771 268603526256008795503379657)
        ·
          refine ⟨201452644692006596627534743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268603526256008795503379657 201452644692006596627534743)
          ·
            refine ⟨302178967038009894941302115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201452644692006596627534743 302178967038009894941302115)
            ·
              refine ⟨453268450557014842411953173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302178967038009894941302115 453268450557014842411953173)
              ·
                refine ⟨21246958619860070738060305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 453268450557014842411953173 21246958619860070738060305)
                ·
                  refine ⟨15935218964895053053545229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21246958619860070738060305 15935218964895053053545229)
                  ·
                    refine ⟨5975707111835644895079461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15935218964895053053545229 5975707111835644895079461)
                    ·
                      refine ⟨1120445083469183417827399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5975707111835644895079461 1120445083469183417827399)
                      ·
                        rfl

theorem cell23_2182059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 4].length) (baseStart_2182059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182059 prefixEnd_2182059 := by exact prefixLift 2182059
  have htrace : WordTrace (prefixWord ++ tailWord_2182059) baseStart_2182059 baseEnd_2182059 := by
    simpa [prefixWord, tailWord_2182059, baseEnd_2182059] using wordTrace_append hprefix tailTrace_2182059
  have hstable : (prefixWord ++ tailWord_2182059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182059).length < 2 ^ (prefixWord ++ tailWord_2182059).sum := by decide
  have hdescent : baseEnd_2182059 < baseStart_2182059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182063 : List Nat := [1, 1, 2, 1, 2, 2, 2, 6, 1, 3, 2]
def baseStart_2182063 : Nat := 118140960795 + 2182063 * 2 ^ 59
def prefixEnd_2182063 : Nat := 4983230072969 + 3 ^ 40 * 2182063 * 2
def baseEnd_2182063 : Nat := 1120447137391801402177381

theorem tailTrace_2182063 : CollatzResearch.WordTrace tailWord_2182063 prefixEnd_2182063 1120447137391801402177381 := by
  unfold tailWord_2182063
  simp only [CollatzResearch.WordTrace]
  refine ⟨79586375893765892535998843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53057583929177261690665895 79586375893765892535998843)
  ·
    refine ⟨119379563840648838803998265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79586375893765892535998843 119379563840648838803998265)
    ·
      refine ⟨89534672880486629102998699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119379563840648838803998265 89534672880486629102998699)
      ·
        refine ⟨134302009320729943654498049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89534672880486629102998699 134302009320729943654498049)
        ·
          refine ⟨100726506990547457740873537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134302009320729943654498049 100726506990547457740873537)
          ·
            refine ⟨75544880242910593305655153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100726506990547457740873537 75544880242910593305655153)
            ·
              refine ⟨56658660182182944979241365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75544880242910593305655153 56658660182182944979241365)
              ·
                refine ⟨2655874696039825545901939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56658660182182944979241365 2655874696039825545901939)
                ·
                  refine ⟨3983812044059738318852909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2655874696039825545901939 3983812044059738318852909)
                  ·
                    refine ⟨1493929516522401869569841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3983812044059738318852909 1493929516522401869569841)
                    ·
                      refine ⟨1120447137391801402177381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1493929516522401869569841 1120447137391801402177381)
                      ·
                        rfl

theorem cell23_2182063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 3, 2].length) (baseStart_2182063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182063 prefixEnd_2182063 := by exact prefixLift 2182063
  have htrace : WordTrace (prefixWord ++ tailWord_2182063) baseStart_2182063 baseEnd_2182063 := by
    simpa [prefixWord, tailWord_2182063, baseEnd_2182063] using wordTrace_append hprefix tailTrace_2182063
  have hstable : (prefixWord ++ tailWord_2182063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182063).length < 2 ^ (prefixWord ++ tailWord_2182063).sum := by decide
  have hdescent : baseEnd_2182063 < baseStart_2182063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182079 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 5]
def baseStart_2182079 : Nat := 118140960795 + 2182079 * 2 ^ 59
def prefixEnd_2182079 : Nat := 4983230072969 + 3 ^ 40 * 2182079 * 2
def baseEnd_2182079 : Nat := 1120455353082273339577307

theorem tailTrace_2182079 : CollatzResearch.WordTrace tailWord_2182079 prefixEnd_2182079 1120455353082273339577307 := by
  unfold tailWord_2182079
  simp only [CollatzResearch.WordTrace]
  refine ⟨79586959461707927268581291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53057972974471951512387527 79586959461707927268581291)
  ·
    refine ⟨119380439192561890902871937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79586959461707927268581291 119380439192561890902871937)
    ·
      refine ⟨89535329394421418177153953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119380439192561890902871937 89535329394421418177153953)
      ·
        refine ⟨67151497045816063632865465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89535329394421418177153953 67151497045816063632865465)
        ·
          refine ⟨50363622784362047724649099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67151497045816063632865465 50363622784362047724649099)
          ·
            refine ⟨75545434176543071586973649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50363622784362047724649099 75545434176543071586973649)
            ·
              refine ⟨56659075632407303690230237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75545434176543071586973649 56659075632407303690230237)
              ·
                refine ⟨21247153362152738883836339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56659075632407303690230237 21247153362152738883836339)
                ·
                  refine ⟨31870730043229108325754509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21247153362152738883836339 31870730043229108325754509)
                  ·
                    refine ⟨11951523766210915622157941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31870730043229108325754509 11951523766210915622157941)
                    ·
                      refine ⟨1120455353082273339577307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11951523766210915622157941 1120455353082273339577307)
                      ·
                        rfl

theorem cell23_2182079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_2182079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182079 prefixEnd_2182079 := by exact prefixLift 2182079
  have htrace : WordTrace (prefixWord ++ tailWord_2182079) baseStart_2182079 baseEnd_2182079 := by
    simpa [prefixWord, tailWord_2182079, baseEnd_2182079] using wordTrace_append hprefix tailTrace_2182079
  have hstable : (prefixWord ++ tailWord_2182079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182079).length < 2 ^ (prefixWord ++ tailWord_2182079).sum := by decide
  have hdescent : baseEnd_2182079 < baseStart_2182079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182106 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 1, 4, 4]
def baseStart_2182106 : Nat := 118140960795 + 2182106 * 2 ^ 59
def prefixEnd_2182106 : Nat := 4983230072969 + 3 ^ 40 * 2182106 * 2
def baseEnd_2182106 : Nat := 1120469217059944733939683

theorem tailTrace_2182106 : CollatzResearch.WordTrace tailWord_2182106 prefixEnd_2182106 1120469217059944733939683 := by
  unfold tailWord_2182106
  simp only [CollatzResearch.WordTrace]
  refine ⟨19896986058152527719953543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53058629488406740586542781 19896986058152527719953543)
  ·
    refine ⟨29845479087228791579930315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19896986058152527719953543 29845479087228791579930315)
    ·
      refine ⟨44768218630843187369895473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29845479087228791579930315 44768218630843187369895473)
      ·
        refine ⟨33576163973132390527421605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44768218630843187369895473 33576163973132390527421605)
        ·
          refine ⟨6295530744962323223891551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33576163973132390527421605 6295530744962323223891551)
          ·
            refine ⟨9443296117443484835837327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6295530744962323223891551 9443296117443484835837327)
            ·
              refine ⟨14164944176165227253755991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9443296117443484835837327 14164944176165227253755991)
              ·
                refine ⟨21247416264247840880633987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14164944176165227253755991 21247416264247840880633987)
                ·
                  refine ⟨31871124396371761320950981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21247416264247840880633987 31871124396371761320950981)
                  ·
                    refine ⟨5975835824319705247678309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31871124396371761320950981 5975835824319705247678309)
                    ·
                      refine ⟨1120469217059944733939683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5975835824319705247678309 1120469217059944733939683)
                      ·
                        rfl

theorem cell23_2182106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_2182106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182106 prefixEnd_2182106 := by exact prefixLift 2182106
  have htrace : WordTrace (prefixWord ++ tailWord_2182106) baseStart_2182106 baseEnd_2182106 := by
    simpa [prefixWord, tailWord_2182106, baseEnd_2182106] using wordTrace_append hprefix tailTrace_2182106
  have hstable : (prefixWord ++ tailWord_2182106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182106).length < 2 ^ (prefixWord ++ tailWord_2182106).sum := by decide
  have hdescent : baseEnd_2182106 < baseStart_2182106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182290 : List Nat := [3, 2, 3, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_2182290 : Nat := 118140960795 + 2182290 * 2 ^ 59
def prefixEnd_2182290 : Nat := 4983230072969 + 3 ^ 40 * 2182290 * 2
def baseEnd_2182290 : Nat := 1120563697500372014038837

theorem tailTrace_2182290 : CollatzResearch.WordTrace tailWord_2182290 prefixEnd_2182290 1120563697500372014038837 := by
  unfold tailWord_2182290
  simp only [CollatzResearch.WordTrace]
  refine ⟨19898663815985877576128081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53063103509295673536341549 19898663815985877576128081)
  ·
    refine ⟨14923997861989408182096061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19898663815985877576128081 14923997861989408182096061)
    ·
      refine ⟨5596499198246028068286023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14923997861989408182096061 5596499198246028068286023)
      ·
        refine ⟨8394748797369042102429035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5596499198246028068286023 8394748797369042102429035)
        ·
          refine ⟨12592123196053563153643553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8394748797369042102429035 12592123196053563153643553)
          ·
            refine ⟨9444092397040172365232665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12592123196053563153643553 9444092397040172365232665)
            ·
              refine ⟨7083069297780129273924499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9444092397040172365232665 7083069297780129273924499)
              ·
                refine ⟨10624603946670193910886749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7083069297780129273924499 10624603946670193910886749)
                ·
                  refine ⟨3984226480001322716582531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10624603946670193910886749 3984226480001322716582531)
                  ·
                    refine ⟨5976339720001984074873797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3984226480001322716582531 5976339720001984074873797)
                    ·
                      refine ⟨1120563697500372014038837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5976339720001984074873797 1120563697500372014038837)
                      ·
                        rfl

theorem cell23_2182290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_2182290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182290 prefixEnd_2182290 := by exact prefixLift 2182290
  have htrace : WordTrace (prefixWord ++ tailWord_2182290) baseStart_2182290 baseEnd_2182290 := by
    simpa [prefixWord, tailWord_2182290, baseEnd_2182290] using wordTrace_append hprefix tailTrace_2182290
  have hstable : (prefixWord ++ tailWord_2182290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182290).length < 2 ^ (prefixWord ++ tailWord_2182290).sum := by decide
  have hdescent : baseEnd_2182290 < baseStart_2182290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182317 : List Nat := [1, 5, 2, 1, 3, 1, 1, 1, 4, 4]
def baseStart_2182317 : Nat := 118140960795 + 2182317 * 2 ^ 59
def prefixEnd_2182317 : Nat := 4983230072969 + 3 ^ 40 * 2182317 * 2
def baseEnd_2182317 : Nat := 373525853826014469467071

theorem tailTrace_2182317 : CollatzResearch.WordTrace tailWord_2182317 prefixEnd_2182317 373525853826014469467071 := by
  unfold tailWord_2182317
  simp only [CollatzResearch.WordTrace]
  refine ⟨79595640034845693915745205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53063760023230462610496803 79595640034845693915745205)
  ·
    refine ⟨7462091253266783804601113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79595640034845693915745205 7462091253266783804601113)
    ·
      refine ⟨5596568439950087853450835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7462091253266783804601113 5596568439950087853450835)
      ·
        refine ⟨8394852659925131780176253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5596568439950087853450835 8394852659925131780176253)
        ·
          refine ⟨3148069747471924417566095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8394852659925131780176253 3148069747471924417566095)
          ·
            refine ⟨4722104621207886626349143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3148069747471924417566095 4722104621207886626349143)
            ·
              refine ⟨7083156931811829939523715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4722104621207886626349143 7083156931811829939523715)
              ·
                refine ⟨10624735397717744909285573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7083156931811829939523715 10624735397717744909285573)
                ·
                  refine ⟨1992137887072077170491045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10624735397717744909285573 1992137887072077170491045)
                  ·
                    refine ⟨373525853826014469467071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1992137887072077170491045 373525853826014469467071)
                    ·
                      rfl

theorem cell23_2182317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_2182317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182317 prefixEnd_2182317 := by exact prefixLift 2182317
  have htrace : WordTrace (prefixWord ++ tailWord_2182317) baseStart_2182317 baseEnd_2182317 := by
    simpa [prefixWord, tailWord_2182317, baseEnd_2182317] using wordTrace_append hprefix tailTrace_2182317
  have hstable : (prefixWord ++ tailWord_2182317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182317).length < 2 ^ (prefixWord ++ tailWord_2182317).sum := by decide
  have hdescent : baseEnd_2182317 < baseStart_2182317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182323 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 3, 3, 3]
def baseStart_2182323 : Nat := 118140960795 + 2182323 * 2 ^ 59
def prefixEnd_2182323 : Nat := 4983230072969 + 3 ^ 40 * 2182323 * 2
def baseEnd_2182323 : Nat := 1120580642361970384926185

theorem tailTrace_2182323 : CollatzResearch.WordTrace tailWord_2182323 prefixEnd_2182323 1120580642361970384926185 := by
  unfold tailWord_2182323
  simp only [CollatzResearch.WordTrace]
  refine ⟨79595858872823956940463623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53063905915215971293642415 79595858872823956940463623)
  ·
    refine ⟨119393788309235935410695435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79595858872823956940463623 119393788309235935410695435)
    ·
      refine ⟨179090682463853903116043153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119393788309235935410695435 179090682463853903116043153)
      ·
        refine ⟨134318011847890427337032365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179090682463853903116043153 134318011847890427337032365)
        ·
          refine ⟨50369254442958910251387137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134318011847890427337032365 50369254442958910251387137)
          ·
            refine ⟨37776940832219182688540353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50369254442958910251387137 37776940832219182688540353)
            ·
              refine ⟨28332705624164387016405265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37776940832219182688540353 28332705624164387016405265)
              ·
                refine ⟨21249529218123290262303949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28332705624164387016405265 21249529218123290262303949)
                ·
                  refine ⟨7968573456796233848363981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21249529218123290262303949 7968573456796233848363981)
                  ·
                    refine ⟨2988215046298587693136493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7968573456796233848363981 2988215046298587693136493)
                    ·
                      refine ⟨1120580642361970384926185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2988215046298587693136493 1120580642361970384926185)
                      ·
                        rfl

theorem cell23_2182323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3, 3].length) (baseStart_2182323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182323 prefixEnd_2182323 := by exact prefixLift 2182323
  have htrace : WordTrace (prefixWord ++ tailWord_2182323) baseStart_2182323 baseEnd_2182323 := by
    simpa [prefixWord, tailWord_2182323, baseEnd_2182323] using wordTrace_append hprefix tailTrace_2182323
  have hstable : (prefixWord ++ tailWord_2182323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182323).length < 2 ^ (prefixWord ++ tailWord_2182323).sum := by decide
  have hdescent : baseEnd_2182323 < baseStart_2182323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182334 : List Nat := [4, 2, 1, 1, 3, 2, 3, 1, 2, 4]
def baseStart_2182334 : Nat := 118140960795 + 2182334 * 2 ^ 59
def prefixEnd_2182334 : Nat := 4983230072969 + 3 ^ 40 * 2182334 * 2
def baseEnd_2182334 : Nat := 373528763549723280629545

theorem tailTrace_2182334 : CollatzResearch.WordTrace tailWord_2182334 prefixEnd_2182334 373528763549723280629545 := by
  unfold tailWord_2182334
  simp only [CollatzResearch.WordTrace]
  refine ⟨9949532509473013227389257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53064173383856070546076037 9949532509473013227389257)
  ·
    refine ⟨7462149382104759920541943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9949532509473013227389257 7462149382104759920541943)
    ·
      refine ⟨11193224073157139880812915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7462149382104759920541943 11193224073157139880812915)
      ·
        refine ⟨16789836109735709821219373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11193224073157139880812915 16789836109735709821219373)
        ·
          refine ⟨6296188541150891182957265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16789836109735709821219373 6296188541150891182957265)
          ·
            refine ⟨4722141405863168387217949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6296188541150891182957265 4722141405863168387217949)
            ·
              refine ⟨1770803027198688145206731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4722141405863168387217949 1770803027198688145206731)
              ·
                refine ⟨2656204540798032217810097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1770803027198688145206731 2656204540798032217810097)
                ·
                  refine ⟨1992153405598524163357573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2656204540798032217810097 1992153405598524163357573)
                  ·
                    refine ⟨373528763549723280629545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1992153405598524163357573 373528763549723280629545)
                    ·
                      rfl

theorem cell23_2182334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_2182334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182334 prefixEnd_2182334 := by exact prefixLift 2182334
  have htrace : WordTrace (prefixWord ++ tailWord_2182334) baseStart_2182334 baseEnd_2182334 := by
    simpa [prefixWord, tailWord_2182334, baseEnd_2182334] using wordTrace_append hprefix tailTrace_2182334
  have hstable : (prefixWord ++ tailWord_2182334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182334).length < 2 ^ (prefixWord ++ tailWord_2182334).sum := by decide
  have hdescent : baseEnd_2182334 < baseStart_2182334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182337 : List Nat := [1, 2, 6, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_2182337 : Nat := 118140960795 + 2182337 * 2 ^ 59
def prefixEnd_2182337 : Nat := 4983230072969 + 3 ^ 40 * 2182337 * 2
def baseEnd_2182337 : Nat := 1120587831091133330151121

theorem tailTrace_2182337 : CollatzResearch.WordTrace tailWord_2182337 prefixEnd_2182337 1120587831091133330151121 := by
  unfold tailWord_2182337
  simp only [CollatzResearch.WordTrace]
  refine ⟨79596369494773237331473265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53064246329848824887648843 79596369494773237331473265)
  ·
    refine ⟨59697277121079927998604949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79596369494773237331473265 59697277121079927998604949)
    ·
      refine ⟨2798309865050621624934607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 59697277121079927998604949 2798309865050621624934607)
      ·
        refine ⟨4197464797575932437401911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2798309865050621624934607 4197464797575932437401911)
        ·
          refine ⟨6296197196363898656102867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4197464797575932437401911 6296197196363898656102867)
          ·
            refine ⟨9444295794545847984154301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6296197196363898656102867 9444295794545847984154301)
            ·
              refine ⟨3541610922954692994057863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9444295794545847984154301 3541610922954692994057863)
              ·
                refine ⟨5312416384432039491086795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3541610922954692994057863 5312416384432039491086795)
                ·
                  refine ⟨7968624576648059236630193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5312416384432039491086795 7968624576648059236630193)
                  ·
                    refine ⟨5976468432486044427472645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7968624576648059236630193 5976468432486044427472645)
                    ·
                      refine ⟨1120587831091133330151121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5976468432486044427472645 1120587831091133330151121)
                      ·
                        rfl

theorem cell23_2182337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_2182337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182337 prefixEnd_2182337 := by exact prefixLift 2182337
  have htrace : WordTrace (prefixWord ++ tailWord_2182337) baseStart_2182337 baseEnd_2182337 := by
    simpa [prefixWord, tailWord_2182337, baseEnd_2182337] using wordTrace_append hprefix tailTrace_2182337
  have hstable : (prefixWord ++ tailWord_2182337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182337).length < 2 ^ (prefixWord ++ tailWord_2182337).sum := by decide
  have hdescent : baseEnd_2182337 < baseStart_2182337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182357 : List Nat := [1, 3, 2, 4, 1, 1, 1, 2, 4, 1, 3]
def baseStart_2182357 : Nat := 118140960795 + 2182357 * 2 ^ 59
def prefixEnd_2182357 : Nat := 4983230072969 + 3 ^ 40 * 2182357 * 2
def baseEnd_2182357 : Nat := 1120598100704223251901029

theorem tailTrace_2182357 : CollatzResearch.WordTrace tailWord_2182357 prefixEnd_2182357 1120598100704223251901029 := by
  unfold tailWord_2182357
  simp only [CollatzResearch.WordTrace]
  refine ⟨79597098954700780747201325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53064732636467187164800883 79597098954700780747201325)
  ·
    refine ⟨29848912108012792780200497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79597098954700780747201325 29848912108012792780200497)
    ·
      refine ⟨22386684081009594585150373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29848912108012792780200497 22386684081009594585150373)
      ·
        refine ⟨4197503265189298984715695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22386684081009594585150373 4197503265189298984715695)
        ·
          refine ⟨6296254897783948477073543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4197503265189298984715695 6296254897783948477073543)
          ·
            refine ⟨9444382346675922715610315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6296254897783948477073543 9444382346675922715610315)
            ·
              refine ⟨14166573520013884073415473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9444382346675922715610315 14166573520013884073415473)
              ·
                refine ⟨10624930140010413055061605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14166573520013884073415473 10624930140010413055061605)
                ·
                  refine ⟨1992174401251952447824051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10624930140010413055061605 1992174401251952447824051)
                  ·
                    refine ⟨2988261601877928671736077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1992174401251952447824051 2988261601877928671736077)
                    ·
                      refine ⟨1120598100704223251901029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2988261601877928671736077 1120598100704223251901029)
                      ·
                        rfl

theorem cell23_2182357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_2182357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182357 prefixEnd_2182357 := by exact prefixLift 2182357
  have htrace : WordTrace (prefixWord ++ tailWord_2182357) baseStart_2182357 baseEnd_2182357 := by
    simpa [prefixWord, tailWord_2182357, baseEnd_2182357] using wordTrace_append hprefix tailTrace_2182357
  have hstable : (prefixWord ++ tailWord_2182357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182357).length < 2 ^ (prefixWord ++ tailWord_2182357).sum := by decide
  have hdescent : baseEnd_2182357 < baseStart_2182357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182367 : List Nat := [1, 1, 2, 3, 2, 1, 4, 3, 1, 3, 2]
def baseStart_2182367 : Nat := 118140960795 + 2182367 * 2 ^ 59
def prefixEnd_2182367 : Nat := 4983230072969 + 3 ^ 40 * 2182367 * 2
def baseEnd_2182367 : Nat := 1120603235510768212775983

theorem tailTrace_2182367 : CollatzResearch.WordTrace tailWord_2182367 prefixEnd_2182367 1120603235510768212775983 := by
  unfold tailWord_2182367
  simp only [CollatzResearch.WordTrace]
  refine ⟨79597463684664552455065355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53064975789776368303376903 79597463684664552455065355)
  ·
    refine ⟨119396195526996828682598033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79597463684664552455065355 119396195526996828682598033)
    ·
      refine ⟨89547146645247621511948525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119396195526996828682598033 89547146645247621511948525)
      ·
        refine ⟨33580179991967858066980697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89547146645247621511948525 33580179991967858066980697)
        ·
          refine ⟨25185134993975893550235523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33580179991967858066980697 25185134993975893550235523)
          ·
            refine ⟨37777702490963840325353285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25185134993975893550235523 37777702490963840325353285)
            ·
              refine ⟨7083319217055720061003741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37777702490963840325353285 7083319217055720061003741)
              ·
                refine ⟨2656244706395895022876403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7083319217055720061003741 2656244706395895022876403)
                ·
                  refine ⟨3984367059593842534314605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2656244706395895022876403 3984367059593842534314605)
                  ·
                    refine ⟨1494137647347690950367977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3984367059593842534314605 1494137647347690950367977)
                    ·
                      refine ⟨1120603235510768212775983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1494137647347690950367977 1120603235510768212775983)
                      ·
                        rfl

theorem cell23_2182367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 3, 2].length) (baseStart_2182367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182367 prefixEnd_2182367 := by exact prefixLift 2182367
  have htrace : WordTrace (prefixWord ++ tailWord_2182367) baseStart_2182367 baseEnd_2182367 := by
    simpa [prefixWord, tailWord_2182367, baseEnd_2182367] using wordTrace_append hprefix tailTrace_2182367
  have hstable : (prefixWord ++ tailWord_2182367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182367).length < 2 ^ (prefixWord ++ tailWord_2182367).sum := by decide
  have hdescent : baseEnd_2182367 < baseStart_2182367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182393 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 1, 4, 4]
def baseStart_2182393 : Nat := 118140960795 + 2182393 * 2 ^ 59
def prefixEnd_2182393 : Nat := 4983230072969 + 3 ^ 40 * 2182393 * 2
def baseEnd_2182393 : Nat := 1120616586007785111050863

theorem tailTrace_2182393 : CollatzResearch.WordTrace tailWord_2182393 prefixEnd_2182393 1120616586007785111050863 := by
  unfold tailWord_2182393
  simp only [CollatzResearch.WordTrace]
  refine ⟨79598411982570358895511833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53065607988380239263674555 79598411982570358895511833)
  ·
    refine ⟨59698808986927769171633875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79598411982570358895511833 59698808986927769171633875)
    ·
      refine ⟨89548213480391653757450813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59698808986927769171633875 89548213480391653757450813)
      ·
        refine ⟨33580580055146870159044055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89548213480391653757450813 33580580055146870159044055)
        ·
          refine ⟨50370870082720305238566083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33580580055146870159044055 50370870082720305238566083)
          ·
            refine ⟨75556305124080457857849125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50370870082720305238566083 75556305124080457857849125)
            ·
              refine ⟨14166807210765085848346711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75556305124080457857849125 14166807210765085848346711)
              ·
                refine ⟨21250210816147628772520067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14166807210765085848346711 21250210816147628772520067)
                ·
                  refine ⟨31875316224221443158780101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21250210816147628772520067 31875316224221443158780101)
                  ·
                    refine ⟨5976621792041520592271269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31875316224221443158780101 5976621792041520592271269)
                    ·
                      refine ⟨1120616586007785111050863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5976621792041520592271269 1120616586007785111050863)
                      ·
                        rfl

theorem cell23_2182393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_2182393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182393 prefixEnd_2182393 := by exact prefixLift 2182393
  have htrace : WordTrace (prefixWord ++ tailWord_2182393) baseStart_2182393 baseEnd_2182393 := by
    simpa [prefixWord, tailWord_2182393, baseEnd_2182393] using wordTrace_append hprefix tailTrace_2182393
  have hstable : (prefixWord ++ tailWord_2182393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182393).length < 2 ^ (prefixWord ++ tailWord_2182393).sum := by decide
  have hdescent : baseEnd_2182393 < baseStart_2182393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182431 : List Nat := [1, 1, 2, 4, 4, 1, 2, 2, 2, 2, 2]
def baseStart_2182431 : Nat := 118140960795 + 2182431 * 2 ^ 59
def prefixEnd_2182431 : Nat := 4983230072969 + 3 ^ 40 * 2182431 * 2
def baseEnd_2182431 : Nat := 1120636098272655962375689

theorem tailTrace_2182431 : CollatzResearch.WordTrace tailWord_2182431 prefixEnd_2182431 1120636098272655962375689 := by
  unfold tailWord_2182431
  simp only [CollatzResearch.WordTrace]
  refine ⟨79599797956432691385395147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53066531970955127590263431 79599797956432691385395147)
  ·
    refine ⟨119399696934649037078092721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79599797956432691385395147 119399696934649037078092721)
    ·
      refine ⟨89549772700986777808569541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119399696934649037078092721 89549772700986777808569541)
      ·
        refine ⟨16790582381435020839106789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89549772700986777808569541 16790582381435020839106789)
        ·
          refine ⟨3148234196519066407332523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16790582381435020839106789 3148234196519066407332523)
          ·
            refine ⟨4722351294778599610998785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3148234196519066407332523 4722351294778599610998785)
            ·
              refine ⟨3541763471083949708249089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4722351294778599610998785 3541763471083949708249089)
              ·
                refine ⟨2656322603312962281186817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3541763471083949708249089 2656322603312962281186817)
                ·
                  refine ⟨1992241952484721710890113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2656322603312962281186817 1992241952484721710890113)
                  ·
                    refine ⟨1494181464363541283167585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1992241952484721710890113 1494181464363541283167585)
                    ·
                      refine ⟨1120636098272655962375689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1494181464363541283167585 1120636098272655962375689)
                      ·
                        rfl

theorem cell23_2182431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_2182431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182431 prefixEnd_2182431 := by exact prefixLift 2182431
  have htrace : WordTrace (prefixWord ++ tailWord_2182431) baseStart_2182431 baseEnd_2182431 := by
    simpa [prefixWord, tailWord_2182431, baseEnd_2182431] using wordTrace_append hprefix tailTrace_2182431
  have hstable : (prefixWord ++ tailWord_2182431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182431).length < 2 ^ (prefixWord ++ tailWord_2182431).sum := by decide
  have hdescent : baseEnd_2182431 < baseStart_2182431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182433 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 3, 7]
def baseStart_2182433 : Nat := 118140960795 + 2182433 * 2 ^ 59
def prefixEnd_2182433 : Nat := 4983230072969 + 3 ^ 40 * 2182433 * 2
def baseEnd_2182433 : Nat := 373545708411321651516893

theorem tailTrace_2182433 : CollatzResearch.WordTrace tailWord_2182433 prefixEnd_2182433 373545708411321651516893 := by
  unfold tailWord_2182433
  simp only [CollatzResearch.WordTrace]
  refine ⟨79599870902425445726967953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53066580601616963817978635 79599870902425445726967953)
  ·
    refine ⟨59699903176819084295225965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79599870902425445726967953 59699903176819084295225965)
    ·
      refine ⟨22387463691307156610709737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59699903176819084295225965 22387463691307156610709737)
      ·
        refine ⟨16790597768480367458032303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22387463691307156610709737 16790597768480367458032303)
        ·
          refine ⟨25185896652720551187048455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16790597768480367458032303 25185896652720551187048455)
          ·
            refine ⟨37778844979080826780572683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25185896652720551187048455 37778844979080826780572683)
            ·
              refine ⟨56668267468621240170859025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37778844979080826780572683 56668267468621240170859025)
              ·
                refine ⟨42501200601465930128144269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56668267468621240170859025 42501200601465930128144269)
                ·
                  refine ⟨15937950225549723798054101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42501200601465930128144269 15937950225549723798054101)
                  ·
                    refine ⟨373545708411321651516893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15937950225549723798054101 373545708411321651516893)
                    ·
                      rfl

theorem cell23_2182433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_2182433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182433 prefixEnd_2182433 := by exact prefixLift 2182433
  have htrace : WordTrace (prefixWord ++ tailWord_2182433) baseStart_2182433 baseEnd_2182433 := by
    simpa [prefixWord, tailWord_2182433, baseEnd_2182433] using wordTrace_append hprefix tailTrace_2182433
  have hstable : (prefixWord ++ tailWord_2182433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182433).length < 2 ^ (prefixWord ++ tailWord_2182433).sum := by decide
  have hdescent : baseEnd_2182433 < baseStart_2182433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182437 : List Nat := [1, 3, 1, 2, 4, 2, 1, 4, 5]
def baseStart_2182437 : Nat := 118140960795 + 2182437 * 2 ^ 59
def prefixEnd_2182437 : Nat := 4983230072969 + 3 ^ 40 * 2182437 * 2
def baseEnd_2182437 : Nat := 124515464350731437655629

theorem tailTrace_2182437 : CollatzResearch.WordTrace tailWord_2182437 prefixEnd_2182437 124515464350731437655629 := by
  unfold tailWord_2182437
  simp only [CollatzResearch.WordTrace]
  refine ⟨79600016794410954410113565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53066677862940636273409043 79600016794410954410113565)
  ·
    refine ⟨29850006297904107903792587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79600016794410954410113565 29850006297904107903792587)
    ·
      refine ⟨44775009446856161855688881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29850006297904107903792587 44775009446856161855688881)
      ·
        refine ⟨33581257085142121391766661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44775009446856161855688881 33581257085142121391766661)
        ·
          refine ⟨6296485703464147760956249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33581257085142121391766661 6296485703464147760956249)
          ·
            refine ⟨4722364277598110820717187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6296485703464147760956249 4722364277598110820717187)
            ·
              refine ⟨7083546416397166231075781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4722364277598110820717187 7083546416397166231075781)
              ·
                refine ⟨1328164953074468668326709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7083546416397166231075781 1328164953074468668326709)
                ·
                  refine ⟨124515464350731437655629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1328164953074468668326709 124515464350731437655629)
                  ·
                    rfl

theorem cell23_2182437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 4, 5].length) (baseStart_2182437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182437 prefixEnd_2182437 := by exact prefixLift 2182437
  have htrace : WordTrace (prefixWord ++ tailWord_2182437) baseStart_2182437 baseEnd_2182437 := by
    simpa [prefixWord, tailWord_2182437, baseEnd_2182437] using wordTrace_append hprefix tailTrace_2182437
  have hstable : (prefixWord ++ tailWord_2182437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182437).length < 2 ^ (prefixWord ++ tailWord_2182437).sum := by decide
  have hdescent : baseEnd_2182437 < baseStart_2182437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182454 : List Nat := [5, 1, 2, 3, 1, 1, 1, 2, 7]
def baseStart_2182454 : Nat := 118140960795 + 2182454 * 2 ^ 59
def prefixEnd_2182454 : Nat := 4983230072969 + 3 ^ 40 * 2182454 * 2
def baseEnd_2182454 : Nat := 124516434258634374709787

theorem tailTrace_2182454 : CollatzResearch.WordTrace tailWord_2182454 prefixEnd_2182454 124516434258634374709787 := by
  unfold tailWord_2182454
  simp only [CollatzResearch.WordTrace]
  refine ⟨4975039802209335394592651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53067091223566244208988277 4975039802209335394592651)
  ·
    refine ⟨7462559703314003091888977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4975039802209335394592651 7462559703314003091888977)
    ·
      refine ⟨5596919777485502318916733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7462559703314003091888977 5596919777485502318916733)
      ·
        refine ⟨2098844916557063369593775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5596919777485502318916733 2098844916557063369593775)
        ·
          refine ⟨3148267374835595054390663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2098844916557063369593775 3148267374835595054390663)
          ·
            refine ⟨4722401062253392581585995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3148267374835595054390663 4722401062253392581585995)
            ·
              refine ⟨7083601593380088872378993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4722401062253392581585995 7083601593380088872378993)
              ·
                refine ⟨5312701195035066654284245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7083601593380088872378993 5312701195035066654284245)
                ·
                  refine ⟨124516434258634374709787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5312701195035066654284245 124516434258634374709787)
                  ·
                    rfl

theorem cell23_2182454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_2182454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182454 prefixEnd_2182454 := by exact prefixLift 2182454
  have htrace : WordTrace (prefixWord ++ tailWord_2182454) baseStart_2182454 baseEnd_2182454 := by
    simpa [prefixWord, tailWord_2182454, baseEnd_2182454] using wordTrace_append hprefix tailTrace_2182454
  have hstable : (prefixWord ++ tailWord_2182454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182454).length < 2 ^ (prefixWord ++ tailWord_2182454).sum := by decide
  have hdescent : baseEnd_2182454 < baseStart_2182454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182480 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 5, 4]
def baseStart_2182480 : Nat := 118140960795 + 2182480 * 2 ^ 59
def prefixEnd_2182480 : Nat := 4983230072969 + 3 ^ 40 * 2182480 * 2
def baseEnd_2182480 : Nat := 373553752941575423554321

theorem tailTrace_2182480 : CollatzResearch.WordTrace tailWord_2182480 prefixEnd_2182480 373553752941575423554321 := by
  unfold tailWord_2182480
  simp only [CollatzResearch.WordTrace]
  refine ⟨39800792566627586376964447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53067723422170115169285929 39800792566627586376964447)
  ·
    refine ⟨59701188849941379565446671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39800792566627586376964447 59701188849941379565446671)
    ·
      refine ⟨89551783274912069348170007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59701188849941379565446671 89551783274912069348170007)
      ·
        refine ⟨134327674912368104022255011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89551783274912069348170007 134327674912368104022255011)
        ·
          refine ⟨201491512368552156033382517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134327674912368104022255011 201491512368552156033382517)
          ·
            refine ⟨18889829284551764628129611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 201491512368552156033382517 18889829284551764628129611)
            ·
              refine ⟨28334743926827646942194417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18889829284551764628129611 28334743926827646942194417)
              ·
                refine ⟨21251057945120735206645813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28334743926827646942194417 21251057945120735206645813)
                ·
                  refine ⟨1992286682355068925623045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21251057945120735206645813 1992286682355068925623045)
                  ·
                    refine ⟨373553752941575423554321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1992286682355068925623045 373553752941575423554321)
                    ·
                      rfl

theorem cell23_2182480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 5, 4].length) (baseStart_2182480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182480 prefixEnd_2182480 := by exact prefixLift 2182480
  have htrace : WordTrace (prefixWord ++ tailWord_2182480) baseStart_2182480 baseEnd_2182480 := by
    simpa [prefixWord, tailWord_2182480, baseEnd_2182480] using wordTrace_append hprefix tailTrace_2182480
  have hstable : (prefixWord ++ tailWord_2182480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182480).length < 2 ^ (prefixWord ++ tailWord_2182480).sum := by decide
  have hdescent : baseEnd_2182480 < baseStart_2182480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182483 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 6]
def baseStart_2182483 : Nat := 118140960795 + 2182483 * 2 ^ 59
def prefixEnd_2182483 : Nat := 4983230072969 + 3 ^ 40 * 2182483 * 2
def baseEnd_2182483 : Nat := 1120662799266689758925449

theorem tailTrace_2182483 : CollatzResearch.WordTrace tailWord_2182483 prefixEnd_2182483 1120662799266689758925449 := by
  unfold tailWord_2182483
  simp only [CollatzResearch.WordTrace]
  refine ⟨79601694552244304266288103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53067796368162869510858735 79601694552244304266288103)
  ·
    refine ⟨119402541828366456399432155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79601694552244304266288103 119402541828366456399432155)
    ·
      refine ⟨179103812742549684599148233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119402541828366456399432155 179103812742549684599148233)
      ·
        refine ⟨134327859556912263449361175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179103812742549684599148233 134327859556912263449361175)
        ·
          refine ⟨201491789335368395174041763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134327859556912263449361175 201491789335368395174041763)
          ·
            refine ⟨302237684003052592761062645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201491789335368395174041763 302237684003052592761062645)
            ·
              refine ⟨28334782875286180571349623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 302237684003052592761062645 28334782875286180571349623)
              ·
                refine ⟨42502174312929270857024435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28334782875286180571349623 42502174312929270857024435)
                ·
                  refine ⟨63753261469393906285536653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42502174312929270857024435 63753261469393906285536653)
                  ·
                    refine ⟨23907473051022714857076245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63753261469393906285536653 23907473051022714857076245)
                    ·
                      refine ⟨1120662799266689758925449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23907473051022714857076245 1120662799266689758925449)
                      ·
                        rfl

theorem cell23_2182483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 6].length) (baseStart_2182483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182483 prefixEnd_2182483 := by exact prefixLift 2182483
  have htrace : WordTrace (prefixWord ++ tailWord_2182483) baseStart_2182483 baseEnd_2182483 := by
    simpa [prefixWord, tailWord_2182483, baseEnd_2182483] using wordTrace_append hprefix tailTrace_2182483
  have hstable : (prefixWord ++ tailWord_2182483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182483).length < 2 ^ (prefixWord ++ tailWord_2182483).sum := by decide
  have hdescent : baseEnd_2182483 < baseStart_2182483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182487 : List Nat := [1, 1, 3, 2, 3, 2, 1, 2, 2, 4, 2]
def baseStart_2182487 : Nat := 118140960795 + 2182487 * 2 ^ 59
def prefixEnd_2182487 : Nat := 4983230072969 + 3 ^ 40 * 2182487 * 2
def baseEnd_2182487 : Nat := 1120664853189307743275431

theorem tailTrace_2182487 : CollatzResearch.WordTrace tailWord_2182487 prefixEnd_2182487 1120664853189307743275431 := by
  unfold tailWord_2182487
  simp only [CollatzResearch.WordTrace]
  refine ⟨79601840444229812949433715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53067893629486541966289143 79601840444229812949433715)
  ·
    refine ⟨119402760666344719424150573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79601840444229812949433715 119402760666344719424150573)
    ·
      refine ⟨44776035249879269784056465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119402760666344719424150573 44776035249879269784056465)
      ·
        refine ⟨33582026437409452338042349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44776035249879269784056465 33582026437409452338042349)
        ·
          refine ⟨12593259914028544626765881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33582026437409452338042349 12593259914028544626765881)
          ·
            refine ⟨9444944935521408470074411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12593259914028544626765881 9444944935521408470074411)
            ·
              refine ⟨14167417403282112705111617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9444944935521408470074411 14167417403282112705111617)
              ·
                refine ⟨10625563052461584528833713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14167417403282112705111617 10625563052461584528833713)
                ·
                  refine ⟨7969172289346188396625285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10625563052461584528833713 7969172289346188396625285)
                  ·
                    refine ⟨1494219804252410324367241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7969172289346188396625285 1494219804252410324367241)
                    ·
                      refine ⟨1120664853189307743275431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1494219804252410324367241 1120664853189307743275431)
                      ·
                        rfl

theorem cell23_2182487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 4, 2].length) (baseStart_2182487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182487 prefixEnd_2182487 := by exact prefixLift 2182487
  have htrace : WordTrace (prefixWord ++ tailWord_2182487) baseStart_2182487 baseEnd_2182487 := by
    simpa [prefixWord, tailWord_2182487, baseEnd_2182487] using wordTrace_append hprefix tailTrace_2182487
  have hstable : (prefixWord ++ tailWord_2182487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182487).length < 2 ^ (prefixWord ++ tailWord_2182487).sum := by decide
  have hdescent : baseEnd_2182487 < baseStart_2182487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182531 : List Nat := [1, 1, 1, 3, 5, 3, 1, 3, 1, 4]
def baseStart_2182531 : Nat := 118140960795 + 2182531 * 2 ^ 59
def prefixEnd_2182531 : Nat := 4983230072969 + 3 ^ 40 * 2182531 * 2
def baseEnd_2182531 : Nat := 373562482112701857041743

theorem tailTrace_2182531 : CollatzResearch.WordTrace tailWord_2182531 prefixEnd_2182531 373562482112701857041743 := by
  unfold tailWord_2182531
  simp only [CollatzResearch.WordTrace]
  refine ⟨79603445256070408464035447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53068963504046938976023631 79603445256070408464035447)
  ·
    refine ⟨119405167884105612696053171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79603445256070408464035447 119405167884105612696053171)
    ·
      refine ⟨179107751826158419044079757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119405167884105612696053171 179107751826158419044079757)
      ·
        refine ⟨67165406934809407141529909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179107751826158419044079757 67165406934809407141529909)
        ·
          refine ⟨6296756900138381919518429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67165406934809407141529909 6296756900138381919518429)
          ·
            refine ⟨2361283837551893219819411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6296756900138381919518429 2361283837551893219819411)
            ·
              refine ⟨3541925756327839829729117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2361283837551893219819411 3541925756327839829729117)
              ·
                refine ⟨1328222158622939936148419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3541925756327839829729117 1328222158622939936148419)
                ·
                  refine ⟨1992333237934409904222629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1328222158622939936148419 1992333237934409904222629)
                  ·
                    refine ⟨373562482112701857041743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1992333237934409904222629 373562482112701857041743)
                    ·
                      rfl

theorem cell23_2182531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 3, 1, 4].length) (baseStart_2182531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182531 prefixEnd_2182531 := by exact prefixLift 2182531
  have htrace : WordTrace (prefixWord ++ tailWord_2182531) baseStart_2182531 baseEnd_2182531 := by
    simpa [prefixWord, tailWord_2182531, baseEnd_2182531] using wordTrace_append hprefix tailTrace_2182531
  have hstable : (prefixWord ++ tailWord_2182531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182531).length < 2 ^ (prefixWord ++ tailWord_2182531).sum := by decide
  have hdescent : baseEnd_2182531 < baseStart_2182531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182548 : List Nat := [2, 4, 2, 1, 2, 2, 3, 2, 1, 4]
def baseStart_2182548 : Nat := 118140960795 + 2182548 * 2 ^ 59
def prefixEnd_2182548 : Nat := 4983230072969 + 3 ^ 40 * 2182548 * 2
def baseEnd_2182548 : Nat := 373565391836410668204217

theorem tailTrace_2182548 : CollatzResearch.WordTrace tailWord_2182548 prefixEnd_2182548 373565391836410668204217 := by
  unfold tailWord_2182548
  simp only [CollatzResearch.WordTrace]
  refine ⟨39802032648504410183702149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53069376864672546911602865 39802032648504410183702149)
  ·
    refine ⟨7462881121594576909444153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39802032648504410183702149 7462881121594576909444153)
    ·
      refine ⟨5597160841195932682083115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7462881121594576909444153 5597160841195932682083115)
      ·
        refine ⟨8395741261793899023124673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5597160841195932682083115 8395741261793899023124673)
        ·
          refine ⟨6296805946345424267343505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8395741261793899023124673 6296805946345424267343505)
          ·
            refine ⟨4722604459759068200507629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6296805946345424267343505 4722604459759068200507629)
            ·
              refine ⟨1770976672409650575190361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4722604459759068200507629 1770976672409650575190361)
              ·
                refine ⟨1328232504307237931392771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1770976672409650575190361 1328232504307237931392771)
                ·
                  refine ⟨1992348756460856897089157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1328232504307237931392771 1992348756460856897089157)
                  ·
                    refine ⟨373565391836410668204217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1992348756460856897089157 373565391836410668204217)
                    ·
                      rfl

theorem cell23_2182548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_2182548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182548 prefixEnd_2182548 := by exact prefixLift 2182548
  have htrace : WordTrace (prefixWord ++ tailWord_2182548) baseStart_2182548 baseEnd_2182548 := by
    simpa [prefixWord, tailWord_2182548, baseEnd_2182548] using wordTrace_append hprefix tailTrace_2182548
  have hstable : (prefixWord ++ tailWord_2182548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182548).length < 2 ^ (prefixWord ++ tailWord_2182548).sum := by decide
  have hdescent : baseEnd_2182548 < baseStart_2182548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182577 : List Nat := [1, 2, 2, 4, 1, 1, 3, 1, 3, 1, 4]
def baseStart_2182577 : Nat := 118140960795 + 2182577 * 2 ^ 59
def prefixEnd_2182577 : Nat := 4983230072969 + 3 ^ 40 * 2182577 * 2
def baseEnd_2182577 : Nat := 1120711066448212391150017

theorem tailTrace_2182577 : CollatzResearch.WordTrace tailWord_2182577 prefixEnd_2182577 1120711066448212391150017 := by
  unfold tailWord_2182577
  simp only [CollatzResearch.WordTrace]
  refine ⟨79605123013903758320209985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53070082009269172213473323 79605123013903758320209985)
  ·
    refine ⟨59703842260427818740157489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79605123013903758320209985 59703842260427818740157489)
    ·
      refine ⟨44777881695320864055118117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59703842260427818740157489 44777881695320864055118117)
      ·
        refine ⟨8395852817872662010334647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44777881695320864055118117 8395852817872662010334647)
        ·
          refine ⟨12593779226808993015501971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8395852817872662010334647 12593779226808993015501971)
          ·
            refine ⟨18890668840213489523252957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12593779226808993015501971 18890668840213489523252957)
            ·
              refine ⟨7084000815080058571219859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18890668840213489523252957 7084000815080058571219859)
              ·
                refine ⟨10626001222620087856829789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7084000815080058571219859 10626001222620087856829789)
                ·
                  refine ⟨3984750458482532946311171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10626001222620087856829789 3984750458482532946311171)
                  ·
                    refine ⟨5977125687723799419466757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3984750458482532946311171 5977125687723799419466757)
                    ·
                      refine ⟨1120711066448212391150017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5977125687723799419466757 1120711066448212391150017)
                      ·
                        rfl

theorem cell23_2182577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_2182577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182577 prefixEnd_2182577 := by exact prefixLift 2182577
  have htrace : WordTrace (prefixWord ++ tailWord_2182577) baseStart_2182577 baseEnd_2182577 := by
    simpa [prefixWord, tailWord_2182577, baseEnd_2182577] using wordTrace_append hprefix tailTrace_2182577
  have hstable : (prefixWord ++ tailWord_2182577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182577).length < 2 ^ (prefixWord ++ tailWord_2182577).sum := by decide
  have hdescent : baseEnd_2182577 < baseStart_2182577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182581 : List Nat := [1, 3, 3, 2, 2, 2, 2, 1, 2, 3, 2]
def baseStart_2182581 : Nat := 118140960795 + 2182581 * 2 ^ 59
def prefixEnd_2182581 : Nat := 4983230072969 + 3 ^ 40 * 2182581 * 2
def baseEnd_2182581 : Nat := 1120713120370830375499999

theorem tailTrace_2182581 : CollatzResearch.WordTrace tailWord_2182581 prefixEnd_2182581 1120713120370830375499999 := by
  unfold tailWord_2182581
  simp only [CollatzResearch.WordTrace]
  refine ⟨79605268905889267003355597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53070179270592844668903731 79605268905889267003355597)
  ·
    refine ⟨29851975839708475126258349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79605268905889267003355597 29851975839708475126258349)
    ·
      refine ⟨11194490939890678172346881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29851975839708475126258349 11194490939890678172346881)
      ·
        refine ⟨8395868204918008629260161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11194490939890678172346881 8395868204918008629260161)
        ·
          refine ⟨6296901153688506471945121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8395868204918008629260161 6296901153688506471945121)
          ·
            refine ⟨4722675865266379853958841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6296901153688506471945121 4722675865266379853958841)
            ·
              refine ⟨3542006898949784890469131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4722675865266379853958841 3542006898949784890469131)
              ·
                refine ⟨5313010348424677335703697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3542006898949784890469131 5313010348424677335703697)
                ·
                  refine ⟨3984757761318508001777773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5313010348424677335703697 3984757761318508001777773)
                  ·
                    refine ⟨1494284160494440500666665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3984757761318508001777773 1494284160494440500666665)
                    ·
                      refine ⟨1120713120370830375499999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1494284160494440500666665 1120713120370830375499999)
                      ·
                        rfl

theorem cell23_2182581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_2182581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182581 prefixEnd_2182581 := by exact prefixLift 2182581
  have htrace : WordTrace (prefixWord ++ tailWord_2182581) baseStart_2182581 baseEnd_2182581 := by
    simpa [prefixWord, tailWord_2182581, baseEnd_2182581] using wordTrace_append hprefix tailTrace_2182581
  have hstable : (prefixWord ++ tailWord_2182581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182581).length < 2 ^ (prefixWord ++ tailWord_2182581).sum := by decide
  have hdescent : baseEnd_2182581 < baseStart_2182581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182604 : List Nat := [2, 2, 1, 4, 2, 1, 1, 4, 2, 4]
def baseStart_2182604 : Nat := 118140960795 + 2182604 * 2 ^ 59
def prefixEnd_2182604 : Nat := 4983230072969 + 3 ^ 40 * 2182604 * 2
def baseEnd_2182604 : Nat := 373574976808627928504131

theorem tailTrace_2182604 : CollatzResearch.WordTrace tailWord_2182604 prefixEnd_2182604 373574976808627928504131 := by
  unfold tailWord_2182604
  simp only [CollatzResearch.WordTrace]
  refine ⟨39803053892402970965721433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53070738523203961287628577 39803053892402970965721433)
  ·
    refine ⟨29852290419302228224291075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39803053892402970965721433 29852290419302228224291075)
    ·
      refine ⟨44778435628953342336436613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29852290419302228224291075 44778435628953342336436613)
      ·
        refine ⟨8395956680428751688081865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44778435628953342336436613 8395956680428751688081865)
        ·
          refine ⟨6296967510321563766061399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8395956680428751688081865 6296967510321563766061399)
          ·
            refine ⟨9445451265482345649092099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6296967510321563766061399 9445451265482345649092099)
            ·
              refine ⟨14168176898223518473638149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9445451265482345649092099 14168176898223518473638149)
              ·
                refine ⟨2656533168416909713807153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14168176898223518473638149 2656533168416909713807153)
                ·
                  refine ⟨1992399876312682285355365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2656533168416909713807153 1992399876312682285355365)
                  ·
                    refine ⟨373574976808627928504131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1992399876312682285355365 373574976808627928504131)
                    ·
                      rfl

theorem cell23_2182604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 2, 4].length) (baseStart_2182604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182604 prefixEnd_2182604 := by exact prefixLift 2182604
  have htrace : WordTrace (prefixWord ++ tailWord_2182604) baseStart_2182604 baseEnd_2182604 := by
    simpa [prefixWord, tailWord_2182604, baseEnd_2182604] using wordTrace_append hprefix tailTrace_2182604
  have hstable : (prefixWord ++ tailWord_2182604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182604).length < 2 ^ (prefixWord ++ tailWord_2182604).sum := by decide
  have hdescent : baseEnd_2182604 < baseStart_2182604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182617 : List Nat := [1, 2, 1, 2, 4, 4, 1, 8]
def baseStart_2182617 : Nat := 118140960795 + 2182617 * 2 ^ 59
def prefixEnd_2182617 : Nat := 4983230072969 + 3 ^ 40 * 2182617 * 2
def baseEnd_2182617 : Nat := 41508577987940453135179

theorem tailTrace_2182617 : CollatzResearch.WordTrace tailWord_2182617 prefixEnd_2182617 41508577987940453135179 := by
  unfold tailWord_2182617
  simp only [CollatzResearch.WordTrace]
  refine ⟨79606581933758845151666105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53071054622505896767777403 79606581933758845151666105)
  ·
    refine ⟨59704936450319133863749579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79606581933758845151666105 59704936450319133863749579)
    ·
      refine ⟨89557404675478700795624369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59704936450319133863749579 89557404675478700795624369)
      ·
        refine ⟨67168053506609025596718277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89557404675478700795624369 67168053506609025596718277)
        ·
          refine ⟨12594010032489192299384677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67168053506609025596718277 12594010032489192299384677)
          ·
            refine ⟨2361376881091723556134627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12594010032489192299384677 2361376881091723556134627)
            ·
              refine ⟨3542065321637585334201941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2361376881091723556134627 3542065321637585334201941)
              ·
                refine ⟨41508577987940453135179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3542065321637585334201941 41508577987940453135179)
                ·
                  rfl

theorem cell23_2182617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 8].length) (baseStart_2182617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182617 prefixEnd_2182617 := by exact prefixLift 2182617
  have htrace : WordTrace (prefixWord ++ tailWord_2182617) baseStart_2182617 baseEnd_2182617 := by
    simpa [prefixWord, tailWord_2182617, baseEnd_2182617] using wordTrace_append hprefix tailTrace_2182617
  have hstable : (prefixWord ++ tailWord_2182617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182617).length < 2 ^ (prefixWord ++ tailWord_2182617).sum := by decide
  have hdescent : baseEnd_2182617 < baseStart_2182617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182634 : List Nat := [3, 1, 3, 1, 4, 1, 3, 7]
def baseStart_2182634 : Nat := 118140960795 + 2182634 * 2 ^ 59
def prefixEnd_2182634 : Nat := 4983230072969 + 3 ^ 40 * 2182634 * 2
def baseEnd_2182634 : Nat := 41508901290574765486565

theorem tailTrace_2182634 : CollatzResearch.WordTrace tailWord_2182634 prefixEnd_2182634 41508901290574765486565 := by
  unfold tailWord_2182634
  simp only [CollatzResearch.WordTrace]
  refine ⟨19901800493674314263758739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53071467983131504703356637 19901800493674314263758739)
  ·
    refine ⟨29852700740511471395638109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19901800493674314263758739 29852700740511471395638109)
    ·
      refine ⟨11194762777691801773364291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29852700740511471395638109 11194762777691801773364291)
      ·
        refine ⟨16792144166537702660046437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11194762777691801773364291 16792144166537702660046437)
        ·
          refine ⟨3148527031225819248758707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16792144166537702660046437 3148527031225819248758707)
          ·
            refine ⟨4722790546838728873138061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3148527031225819248758707 4722790546838728873138061)
            ·
              refine ⟨1771046455064523327426773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4722790546838728873138061 1771046455064523327426773)
              ·
                refine ⟨41508901290574765486565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1771046455064523327426773 41508901290574765486565)
                ·
                  rfl

theorem cell23_2182634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 7].length) (baseStart_2182634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182634 prefixEnd_2182634 := by exact prefixLift 2182634
  have htrace : WordTrace (prefixWord ++ tailWord_2182634) baseStart_2182634 baseEnd_2182634 := by
    simpa [prefixWord, tailWord_2182634, baseEnd_2182634] using wordTrace_append hprefix tailTrace_2182634
  have hstable : (prefixWord ++ tailWord_2182634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182634).length < 2 ^ (prefixWord ++ tailWord_2182634).sum := by decide
  have hdescent : baseEnd_2182634 < baseStart_2182634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182645 : List Nat := [1, 3, 5, 1, 1, 1, 1, 5, 1, 2, 2]
def baseStart_2182645 : Nat := 118140960795 + 2182645 * 2 ^ 59
def prefixEnd_2182645 : Nat := 4983230072969 + 3 ^ 40 * 2182645 * 2
def baseEnd_2182645 : Nat := 1120745983132718125099705

theorem tailTrace_2182645 : CollatzResearch.WordTrace tailWord_2182645 prefixEnd_2182645 1120745983132718125099705 := by
  unfold tailWord_2182645
  simp only [CollatzResearch.WordTrace]
  refine ⟨79607603177657405933685389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53071735451771603955790259 79607603177657405933685389)
  ·
    refine ⟨29852851191621527225132021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79607603177657405933685389 29852851191621527225132021)
    ·
      refine ⟨2798704799214518177356127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29852851191621527225132021 2798704799214518177356127)
      ·
        refine ⟨4198057198821777266034191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2798704799214518177356127 4198057198821777266034191)
        ·
          refine ⟨6297085798232665899051287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4198057198821777266034191 6297085798232665899051287)
          ·
            refine ⟨9445628697348998848576931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6297085798232665899051287 9445628697348998848576931)
            ·
              refine ⟨14168443046023498272865397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9445628697348998848576931 14168443046023498272865397)
              ·
                refine ⟨1328291535564702963081131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14168443046023498272865397 1328291535564702963081131)
                ·
                  refine ⟨1992437303347054444621697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1328291535564702963081131 1992437303347054444621697)
                  ·
                    refine ⟨1494327977510290833466273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1992437303347054444621697 1494327977510290833466273)
                    ·
                      refine ⟨1120745983132718125099705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1494327977510290833466273 1120745983132718125099705)
                      ·
                        rfl

theorem cell23_2182645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_2182645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182645 prefixEnd_2182645 := by exact prefixLift 2182645
  have htrace : WordTrace (prefixWord ++ tailWord_2182645) baseStart_2182645 baseEnd_2182645 := by
    simpa [prefixWord, tailWord_2182645, baseEnd_2182645] using wordTrace_append hprefix tailTrace_2182645
  have hstable : (prefixWord ++ tailWord_2182645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182645).length < 2 ^ (prefixWord ++ tailWord_2182645).sum := by decide
  have hdescent : baseEnd_2182645 < baseStart_2182645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182677 : List Nat := [1, 3, 2, 1, 3, 2, 2, 1, 2, 6]
def baseStart_2182677 : Nat := 118140960795 + 2182677 * 2 ^ 59
def prefixEnd_2182677 : Nat := 4983230072969 + 3 ^ 40 * 2182677 * 2
def baseEnd_2182677 : Nat := 373587471504553999966519

theorem tailTrace_2182677 : CollatzResearch.WordTrace tailWord_2182677 prefixEnd_2182677 373587471504553999966519 := by
  unfold tailWord_2182677
  simp only [CollatzResearch.WordTrace]
  refine ⟨79608770313541475398850285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53072513542360983599233523 79608770313541475398850285)
  ·
    refine ⟨29853288867578053274568857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79608770313541475398850285 29853288867578053274568857)
    ·
      refine ⟨22389966650683539955926643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29853288867578053274568857 22389966650683539955926643)
      ·
        refine ⟨33584949976025309933889965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22389966650683539955926643 33584949976025309933889965)
        ·
          refine ⟨12594356241009491225208737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33584949976025309933889965 12594356241009491225208737)
          ·
            refine ⟨9445767180757118418906553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12594356241009491225208737 9445767180757118418906553)
            ·
              refine ⟨7084325385567838814179915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9445767180757118418906553 7084325385567838814179915)
              ·
                refine ⟨10626488078351758221269873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7084325385567838814179915 10626488078351758221269873)
                ·
                  refine ⟨7969866058763818665952405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10626488078351758221269873 7969866058763818665952405)
                  ·
                    refine ⟨373587471504553999966519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7969866058763818665952405 373587471504553999966519)
                    ·
                      rfl

theorem cell23_2182677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_2182677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182677 prefixEnd_2182677 := by exact prefixLift 2182677
  have htrace : WordTrace (prefixWord ++ tailWord_2182677) baseStart_2182677 baseEnd_2182677 := by
    simpa [prefixWord, tailWord_2182677, baseEnd_2182677] using wordTrace_append hprefix tailTrace_2182677
  have hstable : (prefixWord ++ tailWord_2182677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182677).length < 2 ^ (prefixWord ++ tailWord_2182677).sum := by decide
  have hdescent : baseEnd_2182677 < baseStart_2182677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182687 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 2, 4, 3]
def baseStart_2182687 : Nat := 118140960795 + 2182687 * 2 ^ 59
def prefixEnd_2182687 : Nat := 4983230072969 + 3 ^ 40 * 2182687 * 2
def baseEnd_2182687 : Nat := 1120767549320206960774511

theorem tailTrace_2182687 : CollatzResearch.WordTrace tailWord_2182687 prefixEnd_2182687 1120767549320206960774511 := by
  unfold tailWord_2182687
  simp only [CollatzResearch.WordTrace]
  refine ⟨79609135043505247106714315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53072756695670164737809543 79609135043505247106714315)
  ·
    refine ⟨119413702565257870660071473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79609135043505247106714315 119413702565257870660071473)
    ·
      refine ⟨89560276923943402995053605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119413702565257870660071473 89560276923943402995053605)
      ·
        refine ⟨16792551923239388061572551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89560276923943402995053605 16792551923239388061572551)
        ·
          refine ⟨25188827884859082092358827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16792551923239388061572551 25188827884859082092358827)
          ·
            refine ⟨37783241827288623138538241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25188827884859082092358827 37783241827288623138538241)
            ·
              refine ⟨28337431370466467353903681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37783241827288623138538241 28337431370466467353903681)
              ·
                refine ⟨21253073527849850515427761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28337431370466467353903681 21253073527849850515427761)
                ·
                  refine ⟨15939805145887387886570821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21253073527849850515427761 15939805145887387886570821)
                  ·
                    refine ⟨2988713464853885228732029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15939805145887387886570821 2988713464853885228732029)
                    ·
                      refine ⟨1120767549320206960774511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2988713464853885228732029 1120767549320206960774511)
                      ·
                        rfl

theorem cell23_2182687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_2182687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182687 prefixEnd_2182687 := by exact prefixLift 2182687
  have htrace : WordTrace (prefixWord ++ tailWord_2182687) baseStart_2182687 baseEnd_2182687 := by
    simpa [prefixWord, tailWord_2182687, baseEnd_2182687] using wordTrace_append hprefix tailTrace_2182687
  have hstable : (prefixWord ++ tailWord_2182687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182687).length < 2 ^ (prefixWord ++ tailWord_2182687).sum := by decide
  have hdescent : baseEnd_2182687 < baseStart_2182687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182688 : List Nat := [2, 1, 1, 6, 1, 2, 2, 2, 1, 3, 2]
def baseStart_2182688 : Nat := 118140960795 + 2182688 * 2 ^ 59
def prefixEnd_2182688 : Nat := 4983230072969 + 3 ^ 40 * 2182688 * 2
def baseEnd_2182688 : Nat := 1120768062800861456862007

theorem tailTrace_2182688 : CollatzResearch.WordTrace tailWord_2182688 prefixEnd_2182688 1120768062800861456862007 := by
  unfold tailWord_2182688
  simp only [CollatzResearch.WordTrace]
  refine ⟨39804585758250812138750359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53072781011001082851667145 39804585758250812138750359)
  ·
    refine ⟨59706878637376218208125539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39804585758250812138750359 59706878637376218208125539)
    ·
      refine ⟨89560317956064327312188309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59706878637376218208125539 89560317956064327312188309)
      ·
        refine ⟨4198139904190515342758827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 89560317956064327312188309 4198139904190515342758827)
        ·
          refine ⟨6297209856285773014138241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4198139904190515342758827 6297209856285773014138241)
          ·
            refine ⟨4722907392214329760603681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6297209856285773014138241 4722907392214329760603681)
            ·
              refine ⟨3542180544160747320452761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4722907392214329760603681 3542180544160747320452761)
              ·
                refine ⟨2656635408120560490339571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3542180544160747320452761 2656635408120560490339571)
                ·
                  refine ⟨3984953112180840735509357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2656635408120560490339571 3984953112180840735509357)
                  ·
                    refine ⟨1494357417067815275816009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3984953112180840735509357 1494357417067815275816009)
                    ·
                      refine ⟨1120768062800861456862007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1494357417067815275816009 1120768062800861456862007)
                      ·
                        rfl

theorem cell23_2182688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_2182688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182688 prefixEnd_2182688 := by exact prefixLift 2182688
  have htrace : WordTrace (prefixWord ++ tailWord_2182688) baseStart_2182688 baseEnd_2182688 := by
    simpa [prefixWord, tailWord_2182688, baseEnd_2182688] using wordTrace_append hprefix tailTrace_2182688
  have hstable : (prefixWord ++ tailWord_2182688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182688).length < 2 ^ (prefixWord ++ tailWord_2182688).sum := by decide
  have hdescent : baseEnd_2182688 < baseStart_2182688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182737 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 4, 5]
def baseStart_2182737 : Nat := 118140960795 + 2182737 * 2 ^ 59
def prefixEnd_2182737 : Nat := 4983230072969 + 3 ^ 40 * 2182737 * 2
def baseEnd_2182737 : Nat := 373597741117643921716427

theorem tailTrace_2182737 : CollatzResearch.WordTrace tailWord_2182737 prefixEnd_2182737 373597741117643921716427 := by
  unfold tailWord_2182737
  simp only [CollatzResearch.WordTrace]
  refine ⟨79610958693324105646034465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53073972462216070430689643 79610958693324105646034465)
  ·
    refine ⟨59708219019993079234525849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79610958693324105646034465 59708219019993079234525849)
    ·
      refine ⟨44781164264994809425894387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59708219019993079234525849 44781164264994809425894387)
      ·
        refine ⟨67171746397492214138841581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44781164264994809425894387 67171746397492214138841581)
        ·
          refine ⟨25189404899059580302065593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67171746397492214138841581 25189404899059580302065593)
          ·
            refine ⟨18892053674294685226549195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25189404899059580302065593 18892053674294685226549195)
            ·
              refine ⟨28338080511442027839823793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18892053674294685226549195 28338080511442027839823793)
              ·
                refine ⟨21253560383581520879867845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28338080511442027839823793 21253560383581520879867845)
                ·
                  refine ⟨3985042571921535164975221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21253560383581520879867845 3985042571921535164975221)
                  ·
                    refine ⟨373597741117643921716427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3985042571921535164975221 373597741117643921716427)
                    ·
                      rfl

theorem cell23_2182737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 5].length) (baseStart_2182737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182737 prefixEnd_2182737 := by exact prefixLift 2182737
  have htrace : WordTrace (prefixWord ++ tailWord_2182737) baseStart_2182737 baseEnd_2182737 := by
    simpa [prefixWord, tailWord_2182737, baseEnd_2182737] using wordTrace_append hprefix tailTrace_2182737
  have hstable : (prefixWord ++ tailWord_2182737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182737).length < 2 ^ (prefixWord ++ tailWord_2182737).sum := by decide
  have hdescent : baseEnd_2182737 < baseStart_2182737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182777 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 2, 3, 5]
def baseStart_2182777 : Nat := 118140960795 + 2182777 * 2 ^ 59
def prefixEnd_2182777 : Nat := 4983230072969 + 3 ^ 40 * 2182777 * 2
def baseEnd_2182777 : Nat := 1120813762579111608649097

theorem tailTrace_2182777 : CollatzResearch.WordTrace tailWord_2182777 prefixEnd_2182777 1120813762579111608649097 := by
  unfold tailWord_2182777
  simp only [CollatzResearch.WordTrace]
  refine ⟨79612417613179192477490585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53074945075452794984993723 79612417613179192477490585)
  ·
    refine ⟨59709313209884394358117939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79612417613179192477490585 59709313209884394358117939)
    ·
      refine ⟨89563969814826591537176909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59709313209884394358117939 89563969814826591537176909)
      ·
        refine ⟨33586488680559971826441341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89563969814826591537176909 33586488680559971826441341)
        ·
          refine ⟨12594933255209989434915503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33586488680559971826441341 12594933255209989434915503)
          ·
            refine ⟨18892399882814984152373255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12594933255209989434915503 18892399882814984152373255)
            ·
              refine ⟨28338599824222476228559883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18892399882814984152373255 28338599824222476228559883)
              ·
                refine ⟨42507899736333714342839825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28338599824222476228559883 42507899736333714342839825)
                ·
                  refine ⟨31880924802250285757129869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42507899736333714342839825 31880924802250285757129869)
                  ·
                    refine ⟨11955346800843857158923701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31880924802250285757129869 11955346800843857158923701)
                    ·
                      refine ⟨1120813762579111608649097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11955346800843857158923701 1120813762579111608649097)
                      ·
                        rfl

theorem cell23_2182777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_2182777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182777 prefixEnd_2182777 := by exact prefixLift 2182777
  have htrace : WordTrace (prefixWord ++ tailWord_2182777) baseStart_2182777 baseEnd_2182777 := by
    simpa [prefixWord, tailWord_2182777, baseEnd_2182777] using wordTrace_append hprefix tailTrace_2182777
  have hstable : (prefixWord ++ tailWord_2182777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182777).length < 2 ^ (prefixWord ++ tailWord_2182777).sum := by decide
  have hdescent : baseEnd_2182777 < baseStart_2182777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182784 : List Nat := [2, 1, 1, 2, 1, 4, 2, 3, 3, 4]
def baseStart_2182784 : Nat := 118140960795 + 2182784 * 2 ^ 59
def prefixEnd_2182784 : Nat := 4983230072969 + 3 ^ 40 * 2182784 * 2
def baseEnd_2182784 : Nat := 373605785647897693753855

theorem tailTrace_2182784 : CollatzResearch.WordTrace tailWord_2182784 prefixEnd_2182784 373605785647897693753855 := by
  unfold tailWord_2182784
  simp only [CollatzResearch.WordTrace]
  refine ⟨39806336462076916336497703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53075115282769221781996937 39806336462076916336497703)
  ·
    refine ⟨59709504693115374504746555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39806336462076916336497703 59709504693115374504746555)
    ·
      refine ⟨89564257039673061757119833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59709504693115374504746555 89564257039673061757119833)
      ·
        refine ⟨67173192779754796317839875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89564257039673061757119833 67173192779754796317839875)
        ·
          refine ⟨100759789169632194476759813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67173192779754796317839875 100759789169632194476759813)
          ·
            refine ⟨18892460469306036464392465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100759789169632194476759813 18892460469306036464392465)
            ·
              refine ⟨14169345351979527348294349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18892460469306036464392465 14169345351979527348294349)
              ·
                refine ⟨5313504506992322755610381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14169345351979527348294349 5313504506992322755610381)
                ·
                  refine ⟨1992564190122121033353893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5313504506992322755610381 1992564190122121033353893)
                  ·
                    refine ⟨373605785647897693753855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1992564190122121033353893 373605785647897693753855)
                    ·
                      rfl

theorem cell23_2182784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 3, 4].length) (baseStart_2182784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182784 prefixEnd_2182784 := by exact prefixLift 2182784
  have htrace : WordTrace (prefixWord ++ tailWord_2182784) baseStart_2182784 baseEnd_2182784 := by
    simpa [prefixWord, tailWord_2182784, baseEnd_2182784] using wordTrace_append hprefix tailTrace_2182784
  have hstable : (prefixWord ++ tailWord_2182784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182784).length < 2 ^ (prefixWord ++ tailWord_2182784).sum := by decide
  have hdescent : baseEnd_2182784 < baseStart_2182784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182787 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 4]
def baseStart_2182787 : Nat := 118140960795 + 2182787 * 2 ^ 59
def prefixEnd_2182787 : Nat := 4983230072969 + 3 ^ 40 * 2182787 * 2
def baseEnd_2182787 : Nat := 1120818897385656569524051

theorem tailTrace_2182787 : CollatzResearch.WordTrace tailWord_2182787 prefixEnd_2182787 1120818897385656569524051 := by
  unfold tailWord_2182787
  simp only [CollatzResearch.WordTrace]
  refine ⟨79612782343142964185354615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53075188228761976123569743 79612782343142964185354615)
  ·
    refine ⟨119419173514714446278031923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79612782343142964185354615 119419173514714446278031923)
    ·
      refine ⟨179128760272071669417047885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119419173514714446278031923 179128760272071669417047885)
      ·
        refine ⟨67173285102026876031392957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179128760272071669417047885 67173285102026876031392957)
        ·
          refine ⟨25189981913260078511772359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67173285102026876031392957 25189981913260078511772359)
          ·
            refine ⟨37784972869890117767658539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25189981913260078511772359 37784972869890117767658539)
            ·
              refine ⟨56677459304835176651487809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37784972869890117767658539 56677459304835176651487809)
              ·
                refine ⟨42508094478626382488615857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56677459304835176651487809 42508094478626382488615857)
                ·
                  refine ⟨31881070858969786866461893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42508094478626382488615857 31881070858969786866461893)
                  ·
                    refine ⟨5977700786056835037461605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31881070858969786866461893 5977700786056835037461605)
                    ·
                      refine ⟨1120818897385656569524051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5977700786056835037461605 1120818897385656569524051)
                      ·
                        rfl

theorem cell23_2182787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_2182787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182787 prefixEnd_2182787 := by exact prefixLift 2182787
  have htrace : WordTrace (prefixWord ++ tailWord_2182787) baseStart_2182787 baseEnd_2182787 := by
    simpa [prefixWord, tailWord_2182787, baseEnd_2182787] using wordTrace_append hprefix tailTrace_2182787
  have hstable : (prefixWord ++ tailWord_2182787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182787).length < 2 ^ (prefixWord ++ tailWord_2182787).sum := by decide
  have hdescent : baseEnd_2182787 < baseStart_2182787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182791 : List Nat := [1, 1, 4, 2, 1, 4, 1, 1, 2, 4, 2]
def baseStart_2182791 : Nat := 118140960795 + 2182791 * 2 ^ 59
def prefixEnd_2182791 : Nat := 4983230072969 + 3 ^ 40 * 2182791 * 2
def baseEnd_2182791 : Nat := 1120820951308274553874033

theorem tailTrace_2182791 : CollatzResearch.WordTrace tailWord_2182791 prefixEnd_2182791 1120820951308274553874033 := by
  unfold tailWord_2182791
  simp only [CollatzResearch.WordTrace]
  refine ⟨79612928235128472868500227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53075285490085648579000151 79612928235128472868500227)
  ·
    refine ⟨119419392352692709302750341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79612928235128472868500227 119419392352692709302750341)
    ·
      refine ⟨22391136066129882994265689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119419392352692709302750341 22391136066129882994265689)
      ·
        refine ⟨16793352049597412245699267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22391136066129882994265689 16793352049597412245699267)
        ·
          refine ⟨25190028074396118368548901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16793352049597412245699267 25190028074396118368548901)
          ·
            refine ⟨4723130263949272194102919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25190028074396118368548901 4723130263949272194102919)
            ·
              refine ⟨7084695395923908291154379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4723130263949272194102919 7084695395923908291154379)
              ·
                refine ⟨10627043093885862436731569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7084695395923908291154379 10627043093885862436731569)
                ·
                  refine ⟨7970282320414396827548677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10627043093885862436731569 7970282320414396827548677)
                  ·
                    refine ⟨1494427935077699405165377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7970282320414396827548677 1494427935077699405165377)
                    ·
                      refine ⟨1120820951308274553874033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1494427935077699405165377 1120820951308274553874033)
                      ·
                        rfl

theorem cell23_2182791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_2182791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182791 prefixEnd_2182791 := by exact prefixLift 2182791
  have htrace : WordTrace (prefixWord ++ tailWord_2182791) baseStart_2182791 baseEnd_2182791 := by
    simpa [prefixWord, tailWord_2182791, baseEnd_2182791] using wordTrace_append hprefix tailTrace_2182791
  have hstable : (prefixWord ++ tailWord_2182791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182791).length < 2 ^ (prefixWord ++ tailWord_2182791).sum := by decide
  have hdescent : baseEnd_2182791 < baseStart_2182791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182841 : List Nat := [1, 2, 1, 4, 1, 1, 3, 3, 3, 1, 3]
def baseStart_2182841 : Nat := 118140960795 + 2182841 * 2 ^ 59
def prefixEnd_2182841 : Nat := 4983230072969 + 3 ^ 40 * 2182841 * 2
def baseEnd_2182841 : Nat := 1120846625340999358248803

theorem tailTrace_2182841 : CollatzResearch.WordTrace tailWord_2182841 prefixEnd_2182841 1120846625340999358248803 := by
  unfold tailWord_2182841
  simp only [CollatzResearch.WordTrace]
  refine ⟨79614751884947331407820377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53076501256631554271880251 79614751884947331407820377)
  ·
    refine ⟨59711063913710498555865283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79614751884947331407820377 59711063913710498555865283)
    ·
      refine ⟨89566595870565747833797925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59711063913710498555865283 89566595870565747833797925)
      ·
        refine ⟨16793736725731077718837111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89566595870565747833797925 16793736725731077718837111)
        ·
          refine ⟨25190605088596616578255667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16793736725731077718837111 25190605088596616578255667)
          ·
            refine ⟨37785907632894924867383501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25190605088596616578255667 37785907632894924867383501)
            ·
              refine ⟨14169715362335596825268813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37785907632894924867383501 14169715362335596825268813)
              ·
                refine ⟨5313643260875848809475805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14169715362335596825268813 5313643260875848809475805)
                ·
                  refine ⟨1992616222828443303553427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5313643260875848809475805 1992616222828443303553427)
                  ·
                    refine ⟨2988924334242664955330141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1992616222828443303553427 2988924334242664955330141)
                    ·
                      refine ⟨1120846625340999358248803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2988924334242664955330141 1120846625340999358248803)
                      ·
                        rfl

theorem cell23_2182841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_2182841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182841 prefixEnd_2182841 := by exact prefixLift 2182841
  have htrace : WordTrace (prefixWord ++ tailWord_2182841) baseStart_2182841 baseEnd_2182841 := by
    simpa [prefixWord, tailWord_2182841, baseEnd_2182841] using wordTrace_append hprefix tailTrace_2182841
  have hstable : (prefixWord ++ tailWord_2182841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182841).length < 2 ^ (prefixWord ++ tailWord_2182841).sum := by decide
  have hdescent : baseEnd_2182841 < baseStart_2182841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182868 : List Nat := [2, 4, 1, 3, 1, 1, 2, 1, 1, 5, 2]
def baseStart_2182868 : Nat := 118140960795 + 2182868 * 2 ^ 59
def prefixEnd_2182868 : Nat := 4983230072969 + 3 ^ 40 * 2182868 * 2
def baseEnd_2182868 : Nat := 1120860489318670752611179

theorem tailTrace_2182868 : CollatzResearch.WordTrace tailWord_2182868 prefixEnd_2182868 1120860489318670752611179 := by
  unfold tailWord_2182868
  simp only [CollatzResearch.WordTrace]
  refine ⟨39807868327924757509526629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53077157770566343346035505 39807868327924757509526629)
  ·
    refine ⟨7463975311485892033036243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39807868327924757509526629 7463975311485892033036243)
    ·
      refine ⟨11195962967228838049554365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7463975311485892033036243 11195962967228838049554365)
      ·
        refine ⟨4198486112710814268582887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11195962967228838049554365 4198486112710814268582887)
        ·
          refine ⟨6297729169066221402874331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4198486112710814268582887 6297729169066221402874331)
          ·
            refine ⟨9446593753599332104311497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6297729169066221402874331 9446593753599332104311497)
            ·
              refine ⟨7084945315199499078233623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9446593753599332104311497 7084945315199499078233623)
              ·
                refine ⟨10627417972799248617350435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7084945315199499078233623 10627417972799248617350435)
                ·
                  refine ⟨15941126959198872926025653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10627417972799248617350435 15941126959198872926025653)
                  ·
                    refine ⟨1494480652424894336814905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15941126959198872926025653 1494480652424894336814905)
                    ·
                      refine ⟨1120860489318670752611179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1494480652424894336814905 1120860489318670752611179)
                      ·
                        rfl

theorem cell23_2182868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_2182868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182868 prefixEnd_2182868 := by exact prefixLift 2182868
  have htrace : WordTrace (prefixWord ++ tailWord_2182868) baseStart_2182868 baseEnd_2182868 := by
    simpa [prefixWord, tailWord_2182868, baseEnd_2182868] using wordTrace_append hprefix tailTrace_2182868
  have hstable : (prefixWord ++ tailWord_2182868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182868).length < 2 ^ (prefixWord ++ tailWord_2182868).sum := by decide
  have hdescent : baseEnd_2182868 < baseStart_2182868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182894 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 3, 1, 6]
def baseStart_2182894 : Nat := 118140960795 + 2182894 * 2 ^ 59
def prefixEnd_2182894 : Nat := 4983230072969 + 3 ^ 40 * 2182894 * 2
def baseEnd_2182894 : Nat := 1120873839815687650886059

theorem tailTrace_2182894 : CollatzResearch.WordTrace tailWord_2182894 prefixEnd_2182894 1120873839815687650886059 := by
  unfold tailWord_2182894
  simp only [CollatzResearch.WordTrace]
  refine ⟨9952085619219415182437467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53077789969170214306333157 9952085619219415182437467)
  ·
    refine ⟨14928128428829122773656201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9952085619219415182437467 14928128428829122773656201)
    ·
      refine ⟨11196096321621842080242151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14928128428829122773656201 11196096321621842080242151)
      ·
        refine ⟨16794144482432763120363227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11196096321621842080242151 16794144482432763120363227)
        ·
          refine ⟨25191216723649144680544841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16794144482432763120363227 25191216723649144680544841)
          ·
            refine ⟨18893412542736858510408631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25191216723649144680544841 18893412542736858510408631)
            ·
              refine ⟨28340118814105287765612947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18893412542736858510408631 28340118814105287765612947)
              ·
                refine ⟨42510178221157931648419421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28340118814105287765612947 42510178221157931648419421)
                ·
                  refine ⟨15941316832934224368157283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42510178221157931648419421 15941316832934224368157283)
                  ·
                    refine ⟨23911975249401336552235925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15941316832934224368157283 23911975249401336552235925)
                    ·
                      refine ⟨1120873839815687650886059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23911975249401336552235925 1120873839815687650886059)
                      ·
                        rfl

theorem cell23_2182894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_2182894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182894 prefixEnd_2182894 := by exact prefixLift 2182894
  have htrace : WordTrace (prefixWord ++ tailWord_2182894) baseStart_2182894 baseEnd_2182894 := by
    simpa [prefixWord, tailWord_2182894, baseEnd_2182894] using wordTrace_append hprefix tailTrace_2182894
  have hstable : (prefixWord ++ tailWord_2182894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182894).length < 2 ^ (prefixWord ++ tailWord_2182894).sum := by decide
  have hdescent : baseEnd_2182894 < baseStart_2182894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182931 : List Nat := [1, 1, 1, 2, 1, 3, 2, 4, 4, 1, 3]
def baseStart_2182931 : Nat := 118140960795 + 2182931 * 2 ^ 59
def prefixEnd_2182931 : Nat := 4983230072969 + 3 ^ 40 * 2182931 * 2
def baseEnd_2182931 : Nat := 1120892838599904006123389

theorem tailTrace_2182931 : CollatzResearch.WordTrace tailWord_2182931 prefixEnd_2182931 1120892838599904006123389 := by
  unfold tailWord_2182931
  simp only [CollatzResearch.WordTrace]
  refine ⟨79618034454621276778596647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53078689636414184519064431 79618034454621276778596647)
  ·
    refine ⟨119427051681931915167894971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79618034454621276778596647 119427051681931915167894971)
    ·
      refine ⟨179140577522897872751842457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119427051681931915167894971 179140577522897872751842457)
      ·
        refine ⟨134355433142173404563881843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179140577522897872751842457 134355433142173404563881843)
        ·
          refine ⟨201533149713260106845822765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134355433142173404563881843 201533149713260106845822765)
          ·
            refine ⟨75574931142472540067183537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201533149713260106845822765 75574931142472540067183537)
            ·
              refine ⟨56681198356854405050387653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75574931142472540067183537 56681198356854405050387653)
              ·
                refine ⟨10627724691910200946947685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56681198356854405050387653 10627724691910200946947685)
                ·
                  refine ⟨1992698379733162677552691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10627724691910200946947685 1992698379733162677552691)
                  ·
                    refine ⟨2989047569599744016329037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1992698379733162677552691 2989047569599744016329037)
                    ·
                      refine ⟨1120892838599904006123389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2989047569599744016329037 1120892838599904006123389)
                      ·
                        rfl

theorem cell23_2182931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 4, 1, 3].length) (baseStart_2182931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182931 prefixEnd_2182931 := by exact prefixLift 2182931
  have htrace : WordTrace (prefixWord ++ tailWord_2182931) baseStart_2182931 baseEnd_2182931 := by
    simpa [prefixWord, tailWord_2182931, baseEnd_2182931] using wordTrace_append hprefix tailTrace_2182931
  have hstable : (prefixWord ++ tailWord_2182931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182931).length < 2 ^ (prefixWord ++ tailWord_2182931).sum := by decide
  have hdescent : baseEnd_2182931 < baseStart_2182931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182935 : List Nat := [1, 1, 3, 4, 2, 2, 3, 1, 1, 2, 3]
def baseStart_2182935 : Nat := 118140960795 + 2182935 * 2 ^ 59
def prefixEnd_2182935 : Nat := 4983230072969 + 3 ^ 40 * 2182935 * 2
def baseEnd_2182935 : Nat := 1120894892522521990473371

theorem tailTrace_2182935 : CollatzResearch.WordTrace tailWord_2182935 prefixEnd_2182935 1120894892522521990473371 := by
  unfold tailWord_2182935
  simp only [CollatzResearch.WordTrace]
  refine ⟨79618180346606785461742259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53078786897737856974494839 79618180346606785461742259)
  ·
    refine ⟨119427270519910178192613389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79618180346606785461742259 119427270519910178192613389)
    ·
      refine ⟨44785226444966316822230021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119427270519910178192613389 44785226444966316822230021)
      ·
        refine ⟨8397229958431184404168129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44785226444966316822230021 8397229958431184404168129)
        ·
          refine ⟨6297922468823388303126097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8397229958431184404168129 6297922468823388303126097)
          ·
            refine ⟨4723441851617541227344573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6297922468823388303126097 4723441851617541227344573)
            ·
              refine ⟨1771290694356577960254215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4723441851617541227344573 1771290694356577960254215)
              ·
                refine ⟨2656936041534866940381323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1771290694356577960254215 2656936041534866940381323)
                ·
                  refine ⟨3985404062302300410571985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2656936041534866940381323 3985404062302300410571985)
                  ·
                    refine ⟨2989053046726725307928989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3985404062302300410571985 2989053046726725307928989)
                    ·
                      refine ⟨1120894892522521990473371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2989053046726725307928989 1120894892522521990473371)
                      ·
                        rfl

theorem cell23_2182935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_2182935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182935 prefixEnd_2182935 := by exact prefixLift 2182935
  have htrace : WordTrace (prefixWord ++ tailWord_2182935) baseStart_2182935 baseEnd_2182935 := by
    simpa [prefixWord, tailWord_2182935, baseEnd_2182935] using wordTrace_append hprefix tailTrace_2182935
  have hstable : (prefixWord ++ tailWord_2182935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182935).length < 2 ^ (prefixWord ++ tailWord_2182935).sum := by decide
  have hdescent : baseEnd_2182935 < baseStart_2182935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2182949 : List Nat := [1, 3, 1, 2, 3, 4, 2, 2, 1, 2, 2]
def baseStart_2182949 : Nat := 118140960795 + 2182949 * 2 ^ 59
def prefixEnd_2182949 : Nat := 4983230072969 + 3 ^ 40 * 2182949 * 2
def baseEnd_2182949 : Nat := 1120902081251684935698307

theorem tailTrace_2182949 : CollatzResearch.WordTrace tailWord_2182949 prefixEnd_2182949 1120902081251684935698307 := by
  unfold tailWord_2182949
  simp only [CollatzResearch.WordTrace]
  refine ⟨79618690968556065852751901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53079127312370710568501267 79618690968556065852751901)
  ·
    refine ⟨29857009113208524694781963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79618690968556065852751901 29857009113208524694781963)
    ·
      refine ⟨44785513669812787042172945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29857009113208524694781963 44785513669812787042172945)
      ·
        refine ⟨33589135252359590281629709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44785513669812787042172945 33589135252359590281629709)
        ·
          refine ⟨12595925719634846355611141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33589135252359590281629709 12595925719634846355611141)
          ·
            refine ⟨2361736072431533691677089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12595925719634846355611141 2361736072431533691677089)
            ·
              refine ⟨1771302054323650268757817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2361736072431533691677089 1771302054323650268757817)
              ·
                refine ⟨1328476540742737701568363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1771302054323650268757817 1328476540742737701568363)
                ·
                  refine ⟨1992714811114106552352545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1328476540742737701568363 1992714811114106552352545)
                  ·
                    refine ⟨1494536108335579914264409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1992714811114106552352545 1494536108335579914264409)
                    ·
                      refine ⟨1120902081251684935698307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1494536108335579914264409 1120902081251684935698307)
                      ·
                        rfl

theorem cell23_2182949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 2, 1, 2, 2].length) (baseStart_2182949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2182949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2182949 prefixEnd_2182949 := by exact prefixLift 2182949
  have htrace : WordTrace (prefixWord ++ tailWord_2182949) baseStart_2182949 baseEnd_2182949 := by
    simpa [prefixWord, tailWord_2182949, baseEnd_2182949] using wordTrace_append hprefix tailTrace_2182949
  have hstable : (prefixWord ++ tailWord_2182949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2182949).length < 2 ^ (prefixWord ++ tailWord_2182949).sum := by decide
  have hdescent : baseEnd_2182949 < baseStart_2182949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2182949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183022 : List Nat := [4, 1, 2, 3, 1, 3, 1, 1, 1, 4, 2]
def baseStart_2183022 : Nat := 118140960795 + 2183022 * 2 ^ 59
def prefixEnd_2183022 : Nat := 4983230072969 + 3 ^ 40 * 2183022 * 2
def baseEnd_2183022 : Nat := 1120939565339463150085471

theorem tailTrace_2183022 : CollatzResearch.WordTrace tailWord_2183022 prefixEnd_2183022 1120939565339463150085471 := by
  unfold tailWord_2183022
  simp only [CollatzResearch.WordTrace]
  refine ⟨9952669187161449915019915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53080902331527732880106213 9952669187161449915019915)
  ·
    refine ⟨14929003780742174872529873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9952669187161449915019915 14929003780742174872529873)
    ·
      refine ⟨11196752835556631154397405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14929003780742174872529873 11196752835556631154397405)
      ·
        refine ⟨4198782313333736682899027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11196752835556631154397405 4198782313333736682899027)
        ·
          refine ⟨6298173470000605024348541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4198782313333736682899027 6298173470000605024348541)
          ·
            refine ⟨2361815051250226884130703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6298173470000605024348541 2361815051250226884130703)
            ·
              refine ⟨3542722576875340326196055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2361815051250226884130703 3542722576875340326196055)
              ·
                refine ⟨5314083865313010489294083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3542722576875340326196055 5314083865313010489294083)
                ·
                  refine ⟨7971125797969515733941125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5314083865313010489294083 7971125797969515733941125)
                  ·
                    refine ⟨1494586087119284200113961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7971125797969515733941125 1494586087119284200113961)
                    ·
                      refine ⟨1120939565339463150085471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1494586087119284200113961 1120939565339463150085471)
                      ·
                        rfl

theorem cell23_2183022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_2183022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183022 prefixEnd_2183022 := by exact prefixLift 2183022
  have htrace : WordTrace (prefixWord ++ tailWord_2183022) baseStart_2183022 baseEnd_2183022 := by
    simpa [prefixWord, tailWord_2183022, baseEnd_2183022] using wordTrace_append hprefix tailTrace_2183022
  have hstable : (prefixWord ++ tailWord_2183022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183022).length < 2 ^ (prefixWord ++ tailWord_2183022).sum := by decide
  have hdescent : baseEnd_2183022 < baseStart_2183022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183058 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 4, 5]
def baseStart_2183058 : Nat := 118140960795 + 2183058 * 2 ^ 59
def prefixEnd_2183058 : Nat := 4983230072969 + 3 ^ 40 * 2183058 * 2
def baseEnd_2183058 : Nat := 373652683547675003078435

theorem tailTrace_2183058 : CollatzResearch.WordTrace tailWord_2183058 prefixEnd_2183058 373652683547675003078435 := by
  unfold tailWord_2183058
  simp only [CollatzResearch.WordTrace]
  refine ⟨19905666631290294367117457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53081777683440784978979885 19905666631290294367117457)
  ·
    refine ⟨14929249973467720775338093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19905666631290294367117457 14929249973467720775338093)
    ·
      refine ⟨5598468740050395290751785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14929249973467720775338093 5598468740050395290751785)
      ·
        refine ⟨4198851555037796468063839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5598468740050395290751785 4198851555037796468063839)
        ·
          refine ⟨6298277332556694702095759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4198851555037796468063839 6298277332556694702095759)
          ·
            refine ⟨9447415998835042053143639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6298277332556694702095759 9447415998835042053143639)
            ·
              refine ⟨14171123998252563079715459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9447415998835042053143639 14171123998252563079715459)
              ·
                refine ⟨21256685997378844619573189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14171123998252563079715459 21256685997378844619573189)
                ·
                  refine ⟨3985628624508533366169973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21256685997378844619573189 3985628624508533366169973)
                  ·
                    refine ⟨373652683547675003078435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3985628624508533366169973 373652683547675003078435)
                    ·
                      rfl

theorem cell23_2183058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_2183058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183058 prefixEnd_2183058 := by exact prefixLift 2183058
  have htrace : WordTrace (prefixWord ++ tailWord_2183058) baseStart_2183058 baseEnd_2183058 := by
    simpa [prefixWord, tailWord_2183058, baseEnd_2183058] using wordTrace_append hprefix tailTrace_2183058
  have hstable : (prefixWord ++ tailWord_2183058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183058).length < 2 ^ (prefixWord ++ tailWord_2183058).sum := by decide
  have hdescent : baseEnd_2183058 < baseStart_2183058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183068 : List Nat := [2, 2, 3, 3, 1, 2, 1, 1, 1, 2, 5]
def baseStart_2183068 : Nat := 118140960795 + 2183068 * 2 ^ 59
def prefixEnd_2183068 : Nat := 4983230072969 + 3 ^ 40 * 2183068 * 2
def baseEnd_2183068 : Nat := 1120963185449569970110259

theorem tailTrace_2183068 : CollatzResearch.WordTrace tailWord_2183068 prefixEnd_2183068 1120963185449569970110259 := by
  unfold tailWord_2183068
  simp only [CollatzResearch.WordTrace]
  refine ⟨39811515627562474588166929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53082020836749966117555905 39811515627562474588166929)
  ·
    refine ⟨29858636720671855941125197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39811515627562474588166929 29858636720671855941125197)
    ·
      refine ⟨11196988770251945977921949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29858636720671855941125197 11196988770251945977921949)
      ·
        refine ⟨4198870788844479741720731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11196988770251945977921949 4198870788844479741720731)
        ·
          refine ⟨6298306183266719612581097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4198870788844479741720731 6298306183266719612581097)
          ·
            refine ⟨4723729637450039709435823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6298306183266719612581097 4723729637450039709435823)
            ·
              refine ⟨7085594456175059564153735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4723729637450039709435823 7085594456175059564153735)
              ·
                refine ⟨10628391684262589346230603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7085594456175059564153735 10628391684262589346230603)
                ·
                  refine ⟨15942587526393884019345905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10628391684262589346230603 15942587526393884019345905)
                  ·
                    refine ⟨11956940644795413014509429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15942587526393884019345905 11956940644795413014509429)
                    ·
                      refine ⟨1120963185449569970110259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11956940644795413014509429 1120963185449569970110259)
                      ·
                        rfl

theorem cell23_2183068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_2183068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183068 prefixEnd_2183068 := by exact prefixLift 2183068
  have htrace : WordTrace (prefixWord ++ tailWord_2183068) baseStart_2183068 baseEnd_2183068 := by
    simpa [prefixWord, tailWord_2183068, baseEnd_2183068] using wordTrace_append hprefix tailTrace_2183068
  have hstable : (prefixWord ++ tailWord_2183068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183068).length < 2 ^ (prefixWord ++ tailWord_2183068).sum := by decide
  have hdescent : baseEnd_2183068 < baseStart_2183068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183081 : List Nat := [1, 2, 1, 1, 1, 1, 4, 4, 1, 4, 3]
def baseStart_2183081 : Nat := 118140960795 + 2183081 * 2 ^ 59
def prefixEnd_2183081 : Nat := 4983230072969 + 3 ^ 40 * 2183081 * 2
def baseEnd_2183081 : Nat := 1120969860698078419247699

theorem tailTrace_2183081 : CollatzResearch.WordTrace tailWord_2183081 prefixEnd_2183081 1120969860698078419247699 := by
  unfold tailWord_2183081
  simp only [CollatzResearch.WordTrace]
  refine ⟨79623505404077852396557097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53082336936051901597704731 79623505404077852396557097)
  ·
    refine ⟨59717629053058389297417823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79623505404077852396557097 59717629053058389297417823)
    ·
      refine ⟨89576443579587583946126735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59717629053058389297417823 89576443579587583946126735)
      ·
        refine ⟨134364665369381375919190103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89576443579587583946126735 134364665369381375919190103)
        ·
          refine ⟨201546998054072063878785155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134364665369381375919190103 201546998054072063878785155)
          ·
            refine ⟨302320497081108095818177733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201546998054072063878785155 302320497081108095818177733)
            ·
              refine ⟨56685093202707767965908325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 302320497081108095818177733 56685093202707767965908325)
              ·
                refine ⟨10628454975507706493607811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56685093202707767965908325 10628454975507706493607811)
                ·
                  refine ⟨15942682463261559740411717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10628454975507706493607811 15942682463261559740411717)
                  ·
                    refine ⟨2989252961861542451327197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15942682463261559740411717 2989252961861542451327197)
                    ·
                      refine ⟨1120969860698078419247699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2989252961861542451327197 1120969860698078419247699)
                      ·
                        rfl

theorem cell23_2183081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 4, 3].length) (baseStart_2183081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183081 prefixEnd_2183081 := by exact prefixLift 2183081
  have htrace : WordTrace (prefixWord ++ tailWord_2183081) baseStart_2183081 baseEnd_2183081 := by
    simpa [prefixWord, tailWord_2183081, baseEnd_2183081] using wordTrace_append hprefix tailTrace_2183081
  have hstable : (prefixWord ++ tailWord_2183081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183081).length < 2 ^ (prefixWord ++ tailWord_2183081).sum := by decide
  have hdescent : baseEnd_2183081 < baseStart_2183081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183092 : List Nat := [2, 5, 2, 1, 2, 1, 2, 1, 2, 5]
def baseStart_2183092 : Nat := 118140960795 + 2183092 * 2 ^ 59
def prefixEnd_2183092 : Nat := 4983230072969 + 3 ^ 40 * 2183092 * 2
def baseEnd_2183092 : Nat := 373658502995092625403383

theorem tailTrace_2183092 : CollatzResearch.WordTrace tailWord_2183092 prefixEnd_2183092 373658502995092625403383 := by
  unfold tailWord_2183092
  simp only [CollatzResearch.WordTrace]
  refine ⟨39811953303519000637603765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53082604404692000850138353 39811953303519000637603765)
  ·
    refine ⟨3732370622204906309775353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39811953303519000637603765 3732370622204906309775353)
    ·
      refine ⟨2799277966653679732331515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3732370622204906309775353 2799277966653679732331515)
      ·
        refine ⟨4198916949980519598497273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2799277966653679732331515 4198916949980519598497273)
        ·
          refine ⟨3149187712485389698872955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4198916949980519598497273 3149187712485389698872955)
          ·
            refine ⟨4723781568728084548309433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3149187712485389698872955 4723781568728084548309433)
            ·
              refine ⟨3542836176546063411232075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4723781568728084548309433 3542836176546063411232075)
              ·
                refine ⟨5314254264819095116848113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3542836176546063411232075 5314254264819095116848113)
                ·
                  refine ⟨3985690698614321337636085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5314254264819095116848113 3985690698614321337636085)
                  ·
                    refine ⟨373658502995092625403383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3985690698614321337636085 373658502995092625403383)
                    ·
                      rfl

theorem cell23_2183092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_2183092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183092 prefixEnd_2183092 := by exact prefixLift 2183092
  have htrace : WordTrace (prefixWord ++ tailWord_2183092) baseStart_2183092 baseEnd_2183092 := by
    simpa [prefixWord, tailWord_2183092, baseEnd_2183092] using wordTrace_append hprefix tailTrace_2183092
  have hstable : (prefixWord ++ tailWord_2183092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183092).length < 2 ^ (prefixWord ++ tailWord_2183092).sum := by decide
  have hdescent : baseEnd_2183092 < baseStart_2183092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183118 : List Nat := [4, 1, 1, 1, 2, 2, 4, 2, 6]
def baseStart_2183118 : Nat := 118140960795 + 2183118 * 2 ^ 59
def prefixEnd_2183118 : Nat := 4983230072969 + 3 ^ 40 * 2183118 * 2
def baseEnd_2183118 : Nat := 124554317720254974942781

theorem tailTrace_2183118 : CollatzResearch.WordTrace tailWord_2183118 prefixEnd_2183118 124554317720254974942781 := by
  unfold tailWord_2183118
  simp only [CollatzResearch.WordTrace]
  refine ⟨9953106863117975964456751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53083236603295871810436005 9953106863117975964456751)
  ·
    refine ⟨14929660294676963946685127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9953106863117975964456751 14929660294676963946685127)
    ·
      refine ⟨22394490442015445920027691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14929660294676963946685127 22394490442015445920027691)
      ·
        refine ⟨33591735663023168880041537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22394490442015445920027691 33591735663023168880041537)
        ·
          refine ⟨25193801747267376660031153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33591735663023168880041537 25193801747267376660031153)
          ·
            refine ⟨18895351310450532495023365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25193801747267376660031153 18895351310450532495023365)
            ·
              refine ⟨3542878370709474842816881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18895351310450532495023365 3542878370709474842816881)
              ·
                refine ⟨2657158778032106132112661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3542878370709474842816881 2657158778032106132112661)
                ·
                  refine ⟨124554317720254974942781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2657158778032106132112661 124554317720254974942781)
                  ·
                    rfl

theorem cell23_2183118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 6].length) (baseStart_2183118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183118 prefixEnd_2183118 := by exact prefixLift 2183118
  have htrace : WordTrace (prefixWord ++ tailWord_2183118) baseStart_2183118 baseEnd_2183118 := by
    simpa [prefixWord, tailWord_2183118, baseEnd_2183118] using wordTrace_append hprefix tailTrace_2183118
  have hstable : (prefixWord ++ tailWord_2183118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183118).length < 2 ^ (prefixWord ++ tailWord_2183118).sum := by decide
  have hdescent : baseEnd_2183118 < baseStart_2183118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183149 : List Nat := [1, 5, 1, 4, 1, 2, 1, 1, 2, 2, 3]
def baseStart_2183149 : Nat := 118140960795 + 2183149 * 2 ^ 59
def prefixEnd_2183149 : Nat := 4983230072969 + 3 ^ 40 * 2183149 * 2
def baseEnd_2183149 : Nat := 1121004777382584153197387

theorem tailTrace_2183149 : CollatzResearch.WordTrace tailWord_2183149 prefixEnd_2183149 1121004777382584153197387 := by
  unfold tailWord_2183149
  simp only [CollatzResearch.WordTrace]
  refine ⟨79625985567831500010032501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53083990378554333340021667 79625985567831500010032501)
  ·
    refine ⟨7464936146984203125940547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79625985567831500010032501 7464936146984203125940547)
    ·
      refine ⟨11197404220476304688910821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7464936146984203125940547 11197404220476304688910821)
      ·
        refine ⟨2099513291339307129170779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11197404220476304688910821 2099513291339307129170779)
        ·
          refine ⟨3149269937008960693756169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2099513291339307129170779 3149269937008960693756169)
          ·
            refine ⟨2361952452756720520317127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3149269937008960693756169 2361952452756720520317127)
            ·
              refine ⟨3542928679135080780475691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2361952452756720520317127 3542928679135080780475691)
              ·
                refine ⟨5314393018702621170713537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3542928679135080780475691 5314393018702621170713537)
                ·
                  refine ⟨3985794764026965878035153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5314393018702621170713537 3985794764026965878035153)
                  ·
                    refine ⟨2989346073020224408526365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3985794764026965878035153 2989346073020224408526365)
                    ·
                      refine ⟨1121004777382584153197387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2989346073020224408526365 1121004777382584153197387)
                      ·
                        rfl

theorem cell23_2183149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_2183149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183149 prefixEnd_2183149 := by exact prefixLift 2183149
  have htrace : WordTrace (prefixWord ++ tailWord_2183149) baseStart_2183149 baseEnd_2183149 := by
    simpa [prefixWord, tailWord_2183149, baseEnd_2183149] using wordTrace_append hprefix tailTrace_2183149
  have hstable : (prefixWord ++ tailWord_2183149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183149).length < 2 ^ (prefixWord ++ tailWord_2183149).sum := by decide
  have hdescent : baseEnd_2183149 < baseStart_2183149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183165 : List Nat := [1, 4, 1, 1, 1, 2, 6, 1, 1, 5]
def baseStart_2183165 : Nat := 118140960795 + 2183165 * 2 ^ 59
def prefixEnd_2183165 : Nat := 4983230072969 + 3 ^ 40 * 2183165 * 2
def baseEnd_2183165 : Nat := 373670997691018696865771

theorem tailTrace_2183165 : CollatzResearch.WordTrace tailWord_2183165 prefixEnd_2183165 373670997691018696865771 := by
  unfold tailWord_2183165
  simp only [CollatzResearch.WordTrace]
  refine ⟨79626569135773534742614949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53084379423849023161743299 79626569135773534742614949)
  ·
    refine ⟨14929981712957537764240303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79626569135773534742614949 14929981712957537764240303)
    ·
      refine ⟨22394972569436306646360455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14929981712957537764240303 22394972569436306646360455)
      ·
        refine ⟨33592458854154459969540683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22394972569436306646360455 33592458854154459969540683)
        ·
          refine ⟨50388688281231689954311025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33592458854154459969540683 50388688281231689954311025)
          ·
            refine ⟨37791516210923767465733269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50388688281231689954311025 37791516210923767465733269)
            ·
              refine ⟨1771477322387051599956247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37791516210923767465733269 1771477322387051599956247)
              ·
                refine ⟨2657215983580577399934371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1771477322387051599956247 2657215983580577399934371)
                ·
                  refine ⟨3985823975370866099901557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2657215983580577399934371 3985823975370866099901557)
                  ·
                    refine ⟨373670997691018696865771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3985823975370866099901557 373670997691018696865771)
                    ·
                      rfl

theorem cell23_2183165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_2183165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183165 prefixEnd_2183165 := by exact prefixLift 2183165
  have htrace : WordTrace (prefixWord ++ tailWord_2183165) baseStart_2183165 baseEnd_2183165 := by
    simpa [prefixWord, tailWord_2183165, baseEnd_2183165] using wordTrace_append hprefix tailTrace_2183165
  have hstable : (prefixWord ++ tailWord_2183165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183165).length < 2 ^ (prefixWord ++ tailWord_2183165).sum := by decide
  have hdescent : baseEnd_2183165 < baseStart_2183165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183171 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 5]
def baseStart_2183171 : Nat := 118140960795 + 2183171 * 2 ^ 59
def prefixEnd_2183171 : Nat := 4983230072969 + 3 ^ 40 * 2183171 * 2
def baseEnd_2183171 : Nat := 1121016073956983067122285

theorem tailTrace_2183171 : CollatzResearch.WordTrace tailWord_2183171 prefixEnd_2183171 1121016073956983067122285 := by
  unfold tailWord_2183171
  simp only [CollatzResearch.WordTrace]
  refine ⟨79626787973751797767333367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53084525315834531844888911 79626787973751797767333367)
  ·
    refine ⟨119440181960627696651000051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79626787973751797767333367 119440181960627696651000051)
    ·
      refine ⟨179160272940941544976500077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119440181960627696651000051 179160272940941544976500077)
      ·
        refine ⟨67185102352853079366187529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179160272940941544976500077 67185102352853079366187529)
        ·
          refine ⟨50388826764639809524640647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67185102352853079366187529 50388826764639809524640647)
          ·
            refine ⟨75583240146959714286960971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50388826764639809524640647 75583240146959714286960971)
            ·
              refine ⟨113374860220439571430441457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75583240146959714286960971 113374860220439571430441457)
              ·
                refine ⟨85031145165329678572831093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113374860220439571430441457 85031145165329678572831093)
                ·
                  refine ⟨7971669859249657366202915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85031145165329678572831093 7971669859249657366202915)
                  ·
                    refine ⟨11957504788874486049304373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7971669859249657366202915 11957504788874486049304373)
                    ·
                      refine ⟨1121016073956983067122285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11957504788874486049304373 1121016073956983067122285)
                      ·
                        rfl

theorem cell23_2183171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_2183171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183171 prefixEnd_2183171 := by exact prefixLift 2183171
  have htrace : WordTrace (prefixWord ++ tailWord_2183171) baseStart_2183171 baseEnd_2183171 := by
    simpa [prefixWord, tailWord_2183171, baseEnd_2183171] using wordTrace_append hprefix tailTrace_2183171
  have hstable : (prefixWord ++ tailWord_2183171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183171).length < 2 ^ (prefixWord ++ tailWord_2183171).sum := by decide
  have hdescent : baseEnd_2183171 < baseStart_2183171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183202 : List Nat := [3, 3, 1, 1, 1, 2, 1, 4, 3, 2, 2]
def baseStart_2183202 : Nat := 118140960795 + 2183202 * 2 ^ 59
def prefixEnd_2183202 : Nat := 4983230072969 + 3 ^ 40 * 2183202 * 2
def baseEnd_2183202 : Nat := 1121031991857272445834643

theorem tailTrace_2183202 : CollatzResearch.WordTrace tailWord_2183202 prefixEnd_2183202 1121031991857272445834643 := by
  unfold tailWord_2183202
  simp only [CollatzResearch.WordTrace]
  refine ⟨19906979659159872515427965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53085279091092993374474573 19906979659159872515427965)
  ·
    refine ⟨7465117372184952193285487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19906979659159872515427965 7465117372184952193285487)
    ·
      refine ⟨11197676058277428289928231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7465117372184952193285487 11197676058277428289928231)
      ·
        refine ⟨16796514087416142434892347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11197676058277428289928231 16796514087416142434892347)
        ·
          refine ⟨25194771131124213652338521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16796514087416142434892347 25194771131124213652338521)
          ·
            refine ⟨18896078348343160239253891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25194771131124213652338521 18896078348343160239253891)
            ·
              refine ⟨28344117522514740358880837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18896078348343160239253891 28344117522514740358880837)
              ·
                refine ⟨5314522035471513817290157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28344117522514740358880837 5314522035471513817290157)
                ·
                  refine ⟨1992945763301817681483809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5314522035471513817290157 1992945763301817681483809)
                  ·
                    refine ⟨1494709322476363261112857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1992945763301817681483809 1494709322476363261112857)
                    ·
                      refine ⟨1121031991857272445834643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1494709322476363261112857 1121031991857272445834643)
                      ·
                        rfl

theorem cell23_2183202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_2183202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183202 prefixEnd_2183202 := by exact prefixLift 2183202
  have htrace : WordTrace (prefixWord ++ tailWord_2183202) baseStart_2183202 baseEnd_2183202 := by
    simpa [prefixWord, tailWord_2183202, baseEnd_2183202] using wordTrace_append hprefix tailTrace_2183202
  have hstable : (prefixWord ++ tailWord_2183202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183202).length < 2 ^ (prefixWord ++ tailWord_2183202).sum := by decide
  have hdescent : baseEnd_2183202 < baseStart_2183202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183205 : List Nat := [1, 3, 1, 2, 2, 3, 1, 4, 1, 2, 3]
def baseStart_2183205 : Nat := 118140960795 + 2183205 * 2 ^ 59
def prefixEnd_2183205 : Nat := 4983230072969 + 3 ^ 40 * 2183205 * 2
def baseEnd_2183205 : Nat := 1121033532299235934097129

theorem tailTrace_2183205 : CollatzResearch.WordTrace tailWord_2183205 prefixEnd_2183205 1121033532299235934097129 := by
  unfold tailWord_2183205
  simp only [CollatzResearch.WordTrace]
  refine ⟨79628028055628621574071069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53085352037085747716047379 79628028055628621574071069)
  ·
    refine ⟨29860510520860733090276651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79628028055628621574071069 29860510520860733090276651)
    ·
      refine ⟨44790765781291099635414977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29860510520860733090276651 44790765781291099635414977)
      ·
        refine ⟨33593074335968324726561233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44790765781291099635414977 33593074335968324726561233)
        ·
          refine ⟨25194805751976243544920925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33593074335968324726561233 25194805751976243544920925)
          ·
            refine ⟨9448052156991091329345347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25194805751976243544920925 9448052156991091329345347)
            ·
              refine ⟨14172078235486636994018021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9448052156991091329345347 14172078235486636994018021)
              ·
                refine ⟨2657264669153744436378379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14172078235486636994018021 2657264669153744436378379)
                ·
                  refine ⟨3985897003730616654567569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2657264669153744436378379 3985897003730616654567569)
                  ·
                    refine ⟨2989422752797962490925677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3985897003730616654567569 2989422752797962490925677)
                    ·
                      refine ⟨1121033532299235934097129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2989422752797962490925677 1121033532299235934097129)
                      ·
                        rfl

theorem cell23_2183205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_2183205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183205 prefixEnd_2183205 := by exact prefixLift 2183205
  have htrace : WordTrace (prefixWord ++ tailWord_2183205) baseStart_2183205 baseEnd_2183205 := by
    simpa [prefixWord, tailWord_2183205, baseEnd_2183205] using wordTrace_append hprefix tailTrace_2183205
  have hstable : (prefixWord ++ tailWord_2183205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183205).length < 2 ^ (prefixWord ++ tailWord_2183205).sum := by decide
  have hdescent : baseEnd_2183205 < baseStart_2183205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183219 : List Nat := [1, 1, 1, 2, 4, 1, 5, 3, 1, 2, 2]
def baseStart_2183219 : Nat := 118140960795 + 2183219 * 2 ^ 59
def prefixEnd_2183219 : Nat := 4983230072969 + 3 ^ 40 * 2183219 * 2
def baseEnd_2183219 : Nat := 1121040721028398879322065

theorem tailTrace_2183219 : CollatzResearch.WordTrace tailWord_2183219 prefixEnd_2183219 1121040721028398879322065 := by
  unfold tailWord_2183219
  simp only [CollatzResearch.WordTrace]
  refine ⟨79628538677577901965080711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53085692451718601310053807 79628538677577901965080711)
  ·
    refine ⟨119442808016366852947621067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79628538677577901965080711 119442808016366852947621067)
    ·
      refine ⟨179164212024550279421431601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119442808016366852947621067 179164212024550279421431601)
      ·
        refine ⟨134373159018412709566073701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179164212024550279421431601 134373159018412709566073701)
        ·
          refine ⟨25194967315952383043638819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 134373159018412709566073701 25194967315952383043638819)
          ·
            refine ⟨37792450973928574565458229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25194967315952383043638819 37792450973928574565458229)
            ·
              refine ⟨3543042278805803865511709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37792450973928574565458229 3543042278805803865511709)
              ·
                refine ⟨1328640854552176449566891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3543042278805803865511709 1328640854552176449566891)
                ·
                  refine ⟨1992961281828264674350337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1328640854552176449566891 1992961281828264674350337)
                  ·
                    refine ⟨1494720961371198505762753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1992961281828264674350337 1494720961371198505762753)
                    ·
                      refine ⟨1121040721028398879322065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1494720961371198505762753 1121040721028398879322065)
                      ·
                        rfl

theorem cell23_2183219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 3, 1, 2, 2].length) (baseStart_2183219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183219 prefixEnd_2183219 := by exact prefixLift 2183219
  have htrace : WordTrace (prefixWord ++ tailWord_2183219) baseStart_2183219 baseEnd_2183219 := by
    simpa [prefixWord, tailWord_2183219, baseEnd_2183219] using wordTrace_append hprefix tailTrace_2183219
  have hstable : (prefixWord ++ tailWord_2183219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183219).length < 2 ^ (prefixWord ++ tailWord_2183219).sum := by decide
  have hdescent : baseEnd_2183219 < baseStart_2183219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183222 : List Nat := [5, 1, 2, 1, 1, 1, 1, 5, 1, 2, 3]
def baseStart_2183222 : Nat := 118140960795 + 2183222 * 2 ^ 59
def prefixEnd_2183222 : Nat := 4983230072969 + 3 ^ 40 * 2183222 * 2
def baseEnd_2183222 : Nat := 1121042261470362367584551

theorem tailTrace_2183222 : CollatzResearch.WordTrace tailWord_2183222 prefixEnd_2183222 1121042261470362367584551 := by
  unfold tailWord_2183222
  simp only [CollatzResearch.WordTrace]
  refine ⟨4976790506035439592339995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53085765397711355651626613 4976790506035439592339995)
  ·
    refine ⟨7465185759053159388509993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4976790506035439592339995 7465185759053159388509993)
    ·
      refine ⟨5598889319289869541382495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7465185759053159388509993 5598889319289869541382495)
      ·
        refine ⟨8398333978934804312073743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5598889319289869541382495 8398333978934804312073743)
        ·
          refine ⟨12597500968402206468110615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8398333978934804312073743 12597500968402206468110615)
          ·
            refine ⟨18896251452603309702165923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12597500968402206468110615 18896251452603309702165923)
            ·
              refine ⟨28344377178904964553248885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18896251452603309702165923 28344377178904964553248885)
              ·
                refine ⟨2657285360522340426867083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28344377178904964553248885 2657285360522340426867083)
                ·
                  refine ⟨3985928040783510640300625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2657285360522340426867083 3985928040783510640300625)
                  ·
                    refine ⟨2989446030587632980225469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3985928040783510640300625 2989446030587632980225469)
                    ·
                      refine ⟨1121042261470362367584551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2989446030587632980225469 1121042261470362367584551)
                      ·
                        rfl

theorem cell23_2183222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_2183222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183222 prefixEnd_2183222 := by exact prefixLift 2183222
  have htrace : WordTrace (prefixWord ++ tailWord_2183222) baseStart_2183222 baseEnd_2183222 := by
    simpa [prefixWord, tailWord_2183222, baseEnd_2183222] using wordTrace_append hprefix tailTrace_2183222
  have hstable : (prefixWord ++ tailWord_2183222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183222).length < 2 ^ (prefixWord ++ tailWord_2183222).sum := by decide
  have hdescent : baseEnd_2183222 < baseStart_2183222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183225 : List Nat := [1, 2, 1, 5, 4, 1, 9]
def baseStart_2183225 : Nat := 118140960795 + 2183225 * 2 ^ 59
def prefixEnd_2183225 : Nat := 4983230072969 + 3 ^ 40 * 2183225 * 2
def baseEnd_2183225 : Nat := 13840046937189208096877

theorem tailTrace_2183225 : CollatzResearch.WordTrace tailWord_2183225 prefixEnd_2183225 13840046937189208096877 := by
  unfold tailWord_2183225
  simp only [CollatzResearch.WordTrace]
  refine ⟨79628757515556164989799129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53085838343704109993199419 79628757515556164989799129)
  ·
    refine ⟨59721568136667123742349347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79628757515556164989799129 59721568136667123742349347)
    ·
      refine ⟨89582352205000685613524021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59721568136667123742349347 89582352205000685613524021)
      ·
        refine ⟨8398345519218814276267877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89582352205000685613524021 8398345519218814276267877)
        ·
          refine ⟨1574689784853527676800227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8398345519218814276267877 1574689784853527676800227)
          ·
            refine ⟨2362034677280291515200341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1574689784853527676800227 2362034677280291515200341)
            ·
              refine ⟨13840046937189208096877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2362034677280291515200341 13840046937189208096877)
              ·
                rfl

theorem cell23_2183225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 9].length) (baseStart_2183225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183225 prefixEnd_2183225 := by exact prefixLift 2183225
  have htrace : WordTrace (prefixWord ++ tailWord_2183225) baseStart_2183225 baseEnd_2183225 := by
    simpa [prefixWord, tailWord_2183225, baseEnd_2183225] using wordTrace_append hprefix tailTrace_2183225
  have hstable : (prefixWord ++ tailWord_2183225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183225).length < 2 ^ (prefixWord ++ tailWord_2183225).sum := by decide
  have hdescent : baseEnd_2183225 < baseStart_2183225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183279 : List Nat := [1, 1, 2, 1, 3, 5, 3, 1, 1, 3, 2]
def baseStart_2183279 : Nat := 118140960795 + 2183279 * 2 ^ 59
def prefixEnd_2183279 : Nat := 4983230072969 + 3 ^ 40 * 2183279 * 2
def baseEnd_2183279 : Nat := 1121071529867668644571789

theorem tailTrace_2183279 : CollatzResearch.WordTrace tailWord_2183279 prefixEnd_2183279 1121071529867668644571789 := by
  unfold tailWord_2183279
  simp only [CollatzResearch.WordTrace]
  refine ⟨79630727057360532212264891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53087151371573688141509927 79630727057360532212264891)
  ·
    refine ⟨119446090586040798318397337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79630727057360532212264891 119446090586040798318397337)
    ·
      refine ⟨89584567939530598738798003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119446090586040798318397337 89584567939530598738798003)
      ·
        refine ⟨134376851909295898108197005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89584567939530598738798003 134376851909295898108197005)
        ·
          refine ⟨50391319465985961790573877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134376851909295898108197005 50391319465985961790573877)
          ·
            refine ⟨4724186199936183917866301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50391319465985961790573877 4724186199936183917866301)
            ·
              refine ⟨1771569824976068969199863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4724186199936183917866301 1771569824976068969199863)
              ·
                refine ⟨2657354737464103453799795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1771569824976068969199863 2657354737464103453799795)
                ·
                  refine ⟨3986032106196155180699693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2657354737464103453799795 3986032106196155180699693)
                  ·
                    refine ⟨1494762039823558192762385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3986032106196155180699693 1494762039823558192762385)
                    ·
                      refine ⟨1121071529867668644571789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1494762039823558192762385 1121071529867668644571789)
                      ·
                        rfl

theorem cell23_2183279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 1, 3, 2].length) (baseStart_2183279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183279 prefixEnd_2183279 := by exact prefixLift 2183279
  have htrace : WordTrace (prefixWord ++ tailWord_2183279) baseStart_2183279 baseEnd_2183279 := by
    simpa [prefixWord, tailWord_2183279, baseEnd_2183279] using wordTrace_append hprefix tailTrace_2183279
  have hstable : (prefixWord ++ tailWord_2183279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183279).length < 2 ^ (prefixWord ++ tailWord_2183279).sum := by decide
  have hdescent : baseEnd_2183279 < baseStart_2183279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183288 : List Nat := [2, 1, 2, 1, 1, 1, 3, 4, 2, 2, 4]
def baseStart_2183288 : Nat := 118140960795 + 2183288 * 2 ^ 59
def prefixEnd_2183288 : Nat := 4983230072969 + 3 ^ 40 * 2183288 * 2
def baseEnd_2183288 : Nat := 1121076151193559109359247

theorem tailTrace_2183288 : CollatzResearch.WordTrace tailWord_2183288 prefixEnd_2183288 1121076151193559109359247 := by
  unfold tailWord_2183288
  simp only [CollatzResearch.WordTrace]
  refine ⟨39815527657163963374671259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53087370209551951166228345 39815527657163963374671259)
  ·
    refine ⟨59723291485745945062006889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39815527657163963374671259 59723291485745945062006889)
    ·
      refine ⟨44792468614309458796505167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59723291485745945062006889 44792468614309458796505167)
      ·
        refine ⟨67188702921464188194757751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44792468614309458796505167 67188702921464188194757751)
        ·
          refine ⟨100783054382196282292136627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67188702921464188194757751 100783054382196282292136627)
          ·
            refine ⟨151174581573294423438204941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100783054382196282292136627 151174581573294423438204941)
            ·
              refine ⟨56690468089985408789326853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151174581573294423438204941 56690468089985408789326853)
              ·
                refine ⟨10629462766872264147998785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56690468089985408789326853 10629462766872264147998785)
                ·
                  refine ⟨7972097075154198110999089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10629462766872264147998785 7972097075154198110999089)
                  ·
                    refine ⟨5979072806365648583249317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7972097075154198110999089 5979072806365648583249317)
                    ·
                      refine ⟨1121076151193559109359247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5979072806365648583249317 1121076151193559109359247)
                      ·
                        rfl

theorem cell23_2183288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_2183288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183288 prefixEnd_2183288 := by exact prefixLift 2183288
  have htrace : WordTrace (prefixWord ++ tailWord_2183288) baseStart_2183288 baseEnd_2183288 := by
    simpa [prefixWord, tailWord_2183288, baseEnd_2183288] using wordTrace_append hprefix tailTrace_2183288
  have hstable : (prefixWord ++ tailWord_2183288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183288).length < 2 ^ (prefixWord ++ tailWord_2183288).sum := by decide
  have hdescent : baseEnd_2183288 < baseStart_2183288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183375 : List Nat := [1, 1, 2, 1, 1, 3, 3, 4, 3, 4]
def baseStart_2183375 : Nat := 118140960795 + 2183375 * 2 ^ 59
def prefixEnd_2183375 : Nat := 4983230072969 + 3 ^ 40 * 2183375 * 2
def baseEnd_2183375 : Nat := 373706941336833422990449

theorem tailTrace_2183375 : CollatzResearch.WordTrace tailWord_2183375 prefixEnd_2183375 373706941336833422990449 := by
  unfold tailWord_2183375
  simp only [CollatzResearch.WordTrace]
  refine ⟨79634228465012740607759579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53089485643341827071839719 79634228465012740607759579)
  ·
    refine ⟨119451342697519110911639369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79634228465012740607759579 119451342697519110911639369)
    ·
      refine ⟨89588507023139333183729527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119451342697519110911639369 89588507023139333183729527)
      ·
        refine ⟨134382760534708999775594291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89588507023139333183729527 134382760534708999775594291)
        ·
          refine ⟨201574140802063499663391437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134382760534708999775594291 201574140802063499663391437)
          ·
            refine ⟨75590302800773812373771789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201574140802063499663391437 75590302800773812373771789)
            ·
              refine ⟨28346363550290179640164421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75590302800773812373771789 28346363550290179640164421)
              ·
                refine ⟨5314943165679408682530829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28346363550290179640164421 5314943165679408682530829)
                ·
                  refine ⟨1993103687129778255949061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5314943165679408682530829 1993103687129778255949061)
                  ·
                    refine ⟨373706941336833422990449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1993103687129778255949061 373706941336833422990449)
                    ·
                      rfl

theorem cell23_2183375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 3, 4].length) (baseStart_2183375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183375 prefixEnd_2183375 := by exact prefixLift 2183375
  have htrace : WordTrace (prefixWord ++ tailWord_2183375) baseStart_2183375 baseEnd_2183375 := by
    simpa [prefixWord, tailWord_2183375, baseEnd_2183375] using wordTrace_append hprefix tailTrace_2183375
  have hstable : (prefixWord ++ tailWord_2183375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183375).length < 2 ^ (prefixWord ++ tailWord_2183375).sum := by decide
  have hdescent : baseEnd_2183375 < baseStart_2183375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183385 : List Nat := [1, 2, 1, 2, 3, 1, 4, 1, 1, 4, 3]
def baseStart_2183385 : Nat := 118140960795 + 2183385 * 2 ^ 59
def prefixEnd_2183385 : Nat := 4983230072969 + 3 ^ 40 * 2183385 * 2
def baseEnd_2183385 : Nat := 1121125958817045229846301

theorem tailTrace_2183385 : CollatzResearch.WordTrace tailWord_2183385 prefixEnd_2183385 1121125958817045229846301 := by
  unfold tailWord_2183385
  simp only [CollatzResearch.WordTrace]
  refine ⟨79634593194976512315623609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53089728796651008210415739 79634593194976512315623609)
  ·
    refine ⟨59725944896232384236717707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79634593194976512315623609 59725944896232384236717707)
    ·
      refine ⟨89588917344348576355076561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59725944896232384236717707 89588917344348576355076561)
      ·
        refine ⟨67191688008261432266307421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89588917344348576355076561 67191688008261432266307421)
        ·
          refine ⟨25196883003098037099865283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67191688008261432266307421 25196883003098037099865283)
          ·
            refine ⟨37795324504647055649797925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25196883003098037099865283 37795324504647055649797925)
            ·
              refine ⟨7086623344621322934337111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37795324504647055649797925 7086623344621322934337111)
              ·
                refine ⟨10629935016931984401505667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7086623344621322934337111 10629935016931984401505667)
                ·
                  refine ⟨15944902525397976602258501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10629935016931984401505667 15944902525397976602258501)
                  ·
                    refine ⟨2989669223512120612923469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15944902525397976602258501 2989669223512120612923469)
                    ·
                      refine ⟨1121125958817045229846301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2989669223512120612923469 1121125958817045229846301)
                      ·
                        rfl

theorem cell23_2183385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 4, 3].length) (baseStart_2183385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183385 prefixEnd_2183385 := by exact prefixLift 2183385
  have htrace : WordTrace (prefixWord ++ tailWord_2183385) baseStart_2183385 baseEnd_2183385 := by
    simpa [prefixWord, tailWord_2183385, baseEnd_2183385] using wordTrace_append hprefix tailTrace_2183385
  have hstable : (prefixWord ++ tailWord_2183385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183385).length < 2 ^ (prefixWord ++ tailWord_2183385).sum := by decide
  have hdescent : baseEnd_2183385 < baseStart_2183385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183402 : List Nat := [3, 1, 3, 1, 1, 2, 3, 2, 2, 2, 3]
def baseStart_2183402 : Nat := 118140960795 + 2183402 * 2 ^ 59
def prefixEnd_2183402 : Nat := 4983230072969 + 3 ^ 40 * 2183402 * 2
def baseEnd_2183402 : Nat := 1121134687988171663333723

theorem tailTrace_2183402 : CollatzResearch.WordTrace tailWord_2183402 prefixEnd_2183402 1121134687988171663333723 := by
  unfold tailWord_2183402
  simp only [CollatzResearch.WordTrace]
  refine ⟨19908803308978731054748115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53090142157276616145994973 19908803308978731054748115)
  ·
    refine ⟨29863204963468096582122173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19908803308978731054748115 29863204963468096582122173)
    ·
      refine ⟨11198701861300536218295815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29863204963468096582122173 11198701861300536218295815)
      ·
        refine ⟨16798052791950804327443723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11198701861300536218295815 16798052791950804327443723)
        ·
          refine ⟨25197079187926206491165585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16798052791950804327443723 25197079187926206491165585)
          ·
            refine ⟨18897809390944654868374189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25197079187926206491165585 18897809390944654868374189)
            ·
              refine ⟨7086678521604245575640321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18897809390944654868374189 7086678521604245575640321)
              ·
                refine ⟨5315008891203184181730241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7086678521604245575640321 5315008891203184181730241)
                ·
                  refine ⟨3986256668402388136297681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5315008891203184181730241 3986256668402388136297681)
                  ·
                    refine ⟨2989692501301791102223261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3986256668402388136297681 2989692501301791102223261)
                    ·
                      refine ⟨1121134687988171663333723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2989692501301791102223261 1121134687988171663333723)
                      ·
                        rfl

theorem cell23_2183402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_2183402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183402 prefixEnd_2183402 := by exact prefixLift 2183402
  have htrace : WordTrace (prefixWord ++ tailWord_2183402) baseStart_2183402 baseEnd_2183402 := by
    simpa [prefixWord, tailWord_2183402, baseEnd_2183402] using wordTrace_append hprefix tailTrace_2183402
  have hstable : (prefixWord ++ tailWord_2183402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183402).length < 2 ^ (prefixWord ++ tailWord_2183402).sum := by decide
  have hdescent : baseEnd_2183402 < baseStart_2183402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183408 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 8]
def baseStart_2183408 : Nat := 118140960795 + 2183408 * 2 ^ 59
def prefixEnd_2183408 : Nat := 4983230072969 + 3 ^ 40 * 2183408 * 2
def baseEnd_2183408 : Nat := 1121137768872098639858695

theorem tailTrace_2183408 : CollatzResearch.WordTrace tailWord_2183408 prefixEnd_2183408 1121137768872098639858695 := by
  unfold tailWord_2183408
  simp only [CollatzResearch.WordTrace]
  refine ⟨39817716036946593621855439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53090288049262124829140585 39817716036946593621855439)
  ·
    refine ⟨59726574055419890432783159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39817716036946593621855439 59726574055419890432783159)
    ·
      refine ⟨89589861083129835649174739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59726574055419890432783159 89589861083129835649174739)
      ·
        refine ⟨134384791624694753473762109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89589861083129835649174739 134384791624694753473762109)
        ·
          refine ⟨50394296859260532552660791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134384791624694753473762109 50394296859260532552660791)
          ·
            refine ⟨75591445288890798828991187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50394296859260532552660791 75591445288890798828991187)
            ·
              refine ⟨113387167933336198243486781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75591445288890798828991187 113387167933336198243486781)
              ·
                refine ⟨42520187975001074341307543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113387167933336198243486781 42520187975001074341307543)
                ·
                  refine ⟨63780281962501611511961315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42520187975001074341307543 63780281962501611511961315)
                  ·
                    refine ⟨95670422943752417267941973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63780281962501611511961315 95670422943752417267941973)
                    ·
                      refine ⟨1121137768872098639858695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 95670422943752417267941973 1121137768872098639858695)
                      ·
                        rfl

theorem cell23_2183408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 8].length) (baseStart_2183408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183408 prefixEnd_2183408 := by exact prefixLift 2183408
  have htrace : WordTrace (prefixWord ++ tailWord_2183408) baseStart_2183408 baseEnd_2183408 := by
    simpa [prefixWord, tailWord_2183408, baseEnd_2183408] using wordTrace_append hprefix tailTrace_2183408
  have hstable : (prefixWord ++ tailWord_2183408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183408).length < 2 ^ (prefixWord ++ tailWord_2183408).sum := by decide
  have hdescent : baseEnd_2183408 < baseStart_2183408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183422 : List Nat := [4, 2, 2, 1, 1, 1, 3, 3, 6]
def baseStart_2183422 : Nat := 118140960795 + 2183422 * 2 ^ 59
def prefixEnd_2183422 : Nat := 4983230072969 + 3 ^ 40 * 2183422 * 2
def baseEnd_2183422 : Nat := 124571661955695731675959

theorem tailTrace_2183422 : CollatzResearch.WordTrace tailWord_2183422 prefixEnd_2183422 124571661955695731675959 := by
  unfold tailWord_2183422
  simp only [CollatzResearch.WordTrace]
  refine ⟨9954492836980308454340065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53090628463894978423147013 9954492836980308454340065)
  ·
    refine ⟨7465869627735231340755049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9954492836980308454340065 7465869627735231340755049)
    ·
      refine ⟨5599402220801423505566287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7465869627735231340755049 5599402220801423505566287)
      ·
        refine ⟨8399103331202135258349431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5599402220801423505566287 8399103331202135258349431)
        ·
          refine ⟨12598654996803202887524147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8399103331202135258349431 12598654996803202887524147)
          ·
            refine ⟨18897982495204804331286221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12598654996803202887524147 18897982495204804331286221)
            ·
              refine ⟨7086743435701801624232333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18897982495204804331286221 7086743435701801624232333)
              ·
                refine ⟨2657528788388175609087125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7086743435701801624232333 2657528788388175609087125)
                ·
                  refine ⟨124571661955695731675959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2657528788388175609087125 124571661955695731675959)
                  ·
                    rfl

theorem cell23_2183422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_2183422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183422 prefixEnd_2183422 := by exact prefixLift 2183422
  have htrace : WordTrace (prefixWord ++ tailWord_2183422) baseStart_2183422 baseEnd_2183422 := by
    simpa [prefixWord, tailWord_2183422, baseEnd_2183422] using wordTrace_append hprefix tailTrace_2183422
  have hstable : (prefixWord ++ tailWord_2183422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183422).length < 2 ^ (prefixWord ++ tailWord_2183422).sum := by decide
  have hdescent : baseEnd_2183422 < baseStart_2183422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183435 : List Nat := [1, 1, 1, 1, 5, 2, 3, 1, 3, 5]
def baseStart_2183435 : Nat := 118140960795 + 2183435 * 2 ^ 59
def prefixEnd_2183435 : Nat := 4983230072969 + 3 ^ 40 * 2183435 * 2
def baseEnd_2183435 : Nat := 373717210949923344740357

theorem tailTrace_2183435 : CollatzResearch.WordTrace tailWord_2183435 prefixEnd_2183435 373717210949923344740357 := by
  unfold tailWord_2183435
  simp only [CollatzResearch.WordTrace]
  refine ⟨79636416844795370854943759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53090944563196913903295839 79636416844795370854943759)
  ·
    refine ⟨119454625267193056282415639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79636416844795370854943759 119454625267193056282415639)
    ·
      refine ⟨179181937900789584423623459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119454625267193056282415639 179181937900789584423623459)
      ·
        refine ⟨268772906851184376635435189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179181937900789584423623459 268772906851184376635435189)
        ·
          refine ⟨25197460017298535309572049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 268772906851184376635435189 25197460017298535309572049)
          ·
            refine ⟨18898095012973901482179037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25197460017298535309572049 18898095012973901482179037)
            ·
              refine ⟨7086785629865213055817139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18898095012973901482179037 7086785629865213055817139)
              ·
                refine ⟨10630178444797819583725709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7086785629865213055817139 10630178444797819583725709)
                ·
                  refine ⟨3986316916799182343897141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10630178444797819583725709 3986316916799182343897141)
                  ·
                    refine ⟨373717210949923344740357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3986316916799182343897141 373717210949923344740357)
                    ·
                      rfl

theorem cell23_2183435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 5].length) (baseStart_2183435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183435 prefixEnd_2183435 := by exact prefixLift 2183435
  have htrace : WordTrace (prefixWord ++ tailWord_2183435) baseStart_2183435 baseEnd_2183435 := by
    simpa [prefixWord, tailWord_2183435, baseEnd_2183435] using wordTrace_append hprefix tailTrace_2183435
  have hstable : (prefixWord ++ tailWord_2183435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183435).length < 2 ^ (prefixWord ++ tailWord_2183435).sum := by decide
  have hdescent : baseEnd_2183435 < baseStart_2183435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183475 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 5]
def baseStart_2183475 : Nat := 118140960795 + 2183475 * 2 ^ 59
def prefixEnd_2183475 : Nat := 4983230072969 + 3 ^ 40 * 2183475 * 2
def baseEnd_2183475 : Nat := 1121172172075949877720887

theorem tailTrace_2183475 : CollatzResearch.WordTrace tailWord_2183475 prefixEnd_2183475 1121172172075949877720887 := by
  unfold tailWord_2183475
  simp only [CollatzResearch.WordTrace]
  refine ⟨79637875764650457686399879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53091917176433638457599919 79637875764650457686399879)
  ·
    refine ⟨119456813646975686529599819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79637875764650457686399879 119456813646975686529599819)
    ·
      refine ⟨179185220470463529794399729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119456813646975686529599819 179185220470463529794399729)
      ·
        refine ⟨134388915352847647345799797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179185220470463529794399729 134388915352847647345799797)
        ·
          refine ⟨12598960814329466938668731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 134388915352847647345799797 12598960814329466938668731)
          ·
            refine ⟨18898441221494200408003097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12598960814329466938668731 18898441221494200408003097)
            ·
              refine ⟨14173830916120650306002323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18898441221494200408003097 14173830916120650306002323)
              ·
                refine ⟨21260746374180975459003485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14173830916120650306002323 21260746374180975459003485)
                ·
                  refine ⟨7972779890317865797126307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21260746374180975459003485 7972779890317865797126307)
                  ·
                    refine ⟨11959169835476798695689461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7972779890317865797126307 11959169835476798695689461)
                    ·
                      refine ⟨1121172172075949877720887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11959169835476798695689461 1121172172075949877720887)
                      ·
                        rfl

theorem cell23_2183475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 5].length) (baseStart_2183475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183475 prefixEnd_2183475 := by exact prefixLift 2183475
  have htrace : WordTrace (prefixWord ++ tailWord_2183475) baseStart_2183475 baseEnd_2183475 := by
    simpa [prefixWord, tailWord_2183475, baseEnd_2183475] using wordTrace_append hprefix tailTrace_2183475
  have hstable : (prefixWord ++ tailWord_2183475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183475).length < 2 ^ (prefixWord ++ tailWord_2183475).sum := by decide
  have hdescent : baseEnd_2183475 < baseStart_2183475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183482 : List Nat := [3, 1, 1, 1, 4, 3, 2, 1, 1, 6]
def baseStart_2183482 : Nat := 118140960795 + 2183482 * 2 ^ 59
def prefixEnd_2183482 : Nat := 4983230072969 + 3 ^ 40 * 2183482 * 2
def baseEnd_2183482 : Nat := 373725255480177116777785

theorem tailTrace_2183482 : CollatzResearch.WordTrace tailWord_2183482 prefixEnd_2183482 373725255480177116777785 := by
  unfold tailWord_2183482
  simp only [CollatzResearch.WordTrace]
  refine ⟨19909532768906274470476175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53092087383750065254603133 19909532768906274470476175)
  ·
    refine ⟨29864299153359411705714263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19909532768906274470476175 29864299153359411705714263)
    ·
      refine ⟨44796448730039117558571395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29864299153359411705714263 44796448730039117558571395)
      ·
        refine ⟨67194673095058676337857093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44796448730039117558571395 67194673095058676337857093)
        ·
          refine ⟨12599001205323501813348205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67194673095058676337857093 12599001205323501813348205)
          ·
            refine ⟨4724625451996313180005577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12599001205323501813348205 4724625451996313180005577)
            ·
              refine ⟨3543469088997234885004183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4724625451996313180005577 3543469088997234885004183)
              ·
                refine ⟨5315203633495852327506275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3543469088997234885004183 5315203633495852327506275)
                ·
                  refine ⟨7972805450243778491259413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5315203633495852327506275 7972805450243778491259413)
                  ·
                    refine ⟨373725255480177116777785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7972805450243778491259413 373725255480177116777785)
                    ·
                      rfl

theorem cell23_2183482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 1, 6].length) (baseStart_2183482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183482 prefixEnd_2183482 := by exact prefixLift 2183482
  have htrace : WordTrace (prefixWord ++ tailWord_2183482) baseStart_2183482 baseEnd_2183482 := by
    simpa [prefixWord, tailWord_2183482, baseEnd_2183482] using wordTrace_append hprefix tailTrace_2183482
  have hstable : (prefixWord ++ tailWord_2183482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183482).length < 2 ^ (prefixWord ++ tailWord_2183482).sum := by decide
  have hdescent : baseEnd_2183482 < baseStart_2183482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183516 : List Nat := [2, 2, 4, 3, 1, 1, 1, 1, 4, 4]
def baseStart_2183516 : Nat := 118140960795 + 2183516 * 2 ^ 59
def prefixEnd_2183516 : Nat := 4983230072969 + 3 ^ 40 * 2183516 * 2
def baseEnd_2183516 : Nat := 373731074927594739102733

theorem tailTrace_2183516 : CollatzResearch.WordTrace tailWord_2183516 prefixEnd_2183516 373731074927594739102733 := by
  unfold tailWord_2183516
  simp only [CollatzResearch.WordTrace]
  refine ⟨39819685578750960844321201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53092914105001281125761601 39819685578750960844321201)
  ·
    refine ⟨29864764184063220633240901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39819685578750960844321201 29864764184063220633240901)
    ·
      refine ⟨5599643284511853868732669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29864764184063220633240901 5599643284511853868732669)
      ·
        refine ⟨2099866231691945200774751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5599643284511853868732669 2099866231691945200774751)
        ·
          refine ⟨3149799347537917801162127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2099866231691945200774751 3149799347537917801162127)
          ·
            refine ⟨4724699021306876701743191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3149799347537917801162127 4724699021306876701743191)
            ·
              refine ⟨7087048531960315052614787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4724699021306876701743191 7087048531960315052614787)
              ·
                refine ⟨10630572797940472578922181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7087048531960315052614787 10630572797940472578922181)
                ·
                  refine ⟨1993232399613838608547909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10630572797940472578922181 1993232399613838608547909)
                  ·
                    refine ⟨373731074927594739102733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1993232399613838608547909 373731074927594739102733)
                    ·
                      rfl

theorem cell23_2183516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_2183516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183516 prefixEnd_2183516 := by exact prefixLift 2183516
  have htrace : WordTrace (prefixWord ++ tailWord_2183516) baseStart_2183516 baseEnd_2183516 := by
    simpa [prefixWord, tailWord_2183516, baseEnd_2183516] using wordTrace_append hprefix tailTrace_2183516
  have hstable : (prefixWord ++ tailWord_2183516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183516).length < 2 ^ (prefixWord ++ tailWord_2183516).sum := by decide
  have hdescent : baseEnd_2183516 < baseStart_2183516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183574 : List Nat := [5, 3, 1, 2, 1, 2, 1, 1, 3, 2, 2]
def baseStart_2183574 : Nat := 118140960795 + 2183574 * 2 ^ 59
def prefixEnd_2183574 : Nat := 4983230072969 + 3 ^ 40 * 2183574 * 2
def baseEnd_2183574 : Nat := 1121223006660744990382933

theorem tailTrace_2183574 : CollatzResearch.WordTrace tailWord_2183574 prefixEnd_2183574 1121223006660744990382933 := by
  unfold tailWord_2183574
  simp only [CollatzResearch.WordTrace]
  refine ⟨4977592911955737349640861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53094324394194531729502517 4977592911955737349640861)
  ·
    refine ⟨1866597341983401506115323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4977592911955737349640861 1866597341983401506115323)
    ·
      refine ⟨2799896012975102259172985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1866597341983401506115323 2799896012975102259172985)
      ·
        refine ⟨2099922009731326694379739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2799896012975102259172985 2099922009731326694379739)
        ·
          refine ⟨3149883014596990041569609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2099922009731326694379739 3149883014596990041569609)
          ·
            refine ⟨2362412260947742531177207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3149883014596990041569609 2362412260947742531177207)
            ·
              refine ⟨3543618391421613796765811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2362412260947742531177207 3543618391421613796765811)
              ·
                refine ⟨5315427587132420695148717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3543618391421613796765811 5315427587132420695148717)
                ·
                  refine ⟨1993285345174657760680769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5315427587132420695148717 1993285345174657760680769)
                  ·
                    refine ⟨1494964008880993320510577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1993285345174657760680769 1494964008880993320510577)
                    ·
                      refine ⟨1121223006660744990382933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1494964008880993320510577 1121223006660744990382933)
                      ·
                        rfl

theorem cell23_2183574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_2183574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183574 prefixEnd_2183574 := by exact prefixLift 2183574
  have htrace : WordTrace (prefixWord ++ tailWord_2183574) baseStart_2183574 baseEnd_2183574 := by
    simpa [prefixWord, tailWord_2183574, baseEnd_2183574] using wordTrace_append hprefix tailTrace_2183574
  have hstable : (prefixWord ++ tailWord_2183574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183574).length < 2 ^ (prefixWord ++ tailWord_2183574).sum := by decide
  have hdescent : baseEnd_2183574 < baseStart_2183574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183636 : List Nat := [2, 4, 1, 2, 2, 2, 1, 4, 5]
def baseStart_2183636 : Nat := 118140960795 + 2183636 * 2 ^ 59
def prefixEnd_2183636 : Nat := 4983230072969 + 3 ^ 40 * 2183636 * 2
def baseEnd_2183636 : Nat := 124583871384591527534183

theorem tailTrace_2183636 : CollatzResearch.WordTrace tailWord_2183636 prefixEnd_2183636 124583871384591527534183 := by
  unfold tailWord_2183636
  simp only [CollatzResearch.WordTrace]
  refine ⟨39821873958533591091505381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53095831944711454788673841 39821873958533591091505381)
  ·
    refine ⟨7466601367225048329657259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39821873958533591091505381 7466601367225048329657259)
    ·
      refine ⟨11199902050837572494485889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7466601367225048329657259 11199902050837572494485889)
      ·
        refine ⟨8399926538128179370864417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11199902050837572494485889 8399926538128179370864417)
        ·
          refine ⟨6299944903596134528148313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8399926538128179370864417 6299944903596134528148313)
          ·
            refine ⟨4724958677697100896111235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6299944903596134528148313 4724958677697100896111235)
            ·
              refine ⟨7087438016545651344166853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4724958677697100896111235 7087438016545651344166853)
              ·
                refine ⟨1328894628102309627031285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7087438016545651344166853 1328894628102309627031285)
                ·
                  refine ⟨124583871384591527534183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1328894628102309627031285 124583871384591527534183)
                  ·
                    rfl

theorem cell23_2183636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_2183636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183636 prefixEnd_2183636 := by exact prefixLift 2183636
  have htrace : WordTrace (prefixWord ++ tailWord_2183636) baseStart_2183636 baseEnd_2183636 := by
    simpa [prefixWord, tailWord_2183636, baseEnd_2183636] using wordTrace_append hprefix tailTrace_2183636
  have hstable : (prefixWord ++ tailWord_2183636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183636).length < 2 ^ (prefixWord ++ tailWord_2183636).sum := by decide
  have hdescent : baseEnd_2183636 < baseStart_2183636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183642 : List Nat := [3, 1, 1, 2, 3, 1, 1, 3, 1, 2, 5]
def baseStart_2183642 : Nat := 118140960795 + 2183642 * 2 ^ 59
def prefixEnd_2183642 : Nat := 4983230072969 + 3 ^ 40 * 2183642 * 2
def baseEnd_2183642 : Nat := 1121257923345250724332619

theorem tailTrace_2183642 : CollatzResearch.WordTrace tailWord_2183642 prefixEnd_2183642 1121257923345250724332619 := by
  unfold tailWord_2183642
  simp only [CollatzResearch.WordTrace]
  refine ⟨19910991688761361301932295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53095977836696963471819453 19910991688761361301932295)
  ·
    refine ⟨29866487533142041952898443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19910991688761361301932295 29866487533142041952898443)
    ·
      refine ⟨44799731299713062929347665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29866487533142041952898443 44799731299713062929347665)
      ·
        refine ⟨33599798474784797197010749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44799731299713062929347665 33599798474784797197010749)
        ·
          refine ⟨12599924428044298948879031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33599798474784797197010749 12599924428044298948879031)
          ·
            refine ⟨18899886642066448423318547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12599924428044298948879031 18899886642066448423318547)
            ·
              refine ⟨28349829963099672634977821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18899886642066448423318547 28349829963099672634977821)
              ·
                refine ⟨10631186236162377238116683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28349829963099672634977821 10631186236162377238116683)
                ·
                  refine ⟨15946779354243565857175025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10631186236162377238116683 15946779354243565857175025)
                  ·
                    refine ⟨11960084515682674392881269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15946779354243565857175025 11960084515682674392881269)
                    ·
                      refine ⟨1121257923345250724332619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11960084515682674392881269 1121257923345250724332619)
                      ·
                        rfl

theorem cell23_2183642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_2183642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183642 prefixEnd_2183642 := by exact prefixLift 2183642
  have htrace : WordTrace (prefixWord ++ tailWord_2183642) baseStart_2183642 baseEnd_2183642 := by
    simpa [prefixWord, tailWord_2183642, baseEnd_2183642] using wordTrace_append hprefix tailTrace_2183642
  have hstable : (prefixWord ++ tailWord_2183642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183642).length < 2 ^ (prefixWord ++ tailWord_2183642).sum := by decide
  have hdescent : baseEnd_2183642 < baseStart_2183642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183776 : List Nat := [2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 4]
def baseStart_2183776 : Nat := 118140960795 + 2183776 * 2 ^ 59
def prefixEnd_2183776 : Nat := 4983230072969 + 3 ^ 40 * 2183776 * 2
def baseEnd_2183776 : Nat := 1121326729752953200057003

theorem tailTrace_2183776 : CollatzResearch.WordTrace tailWord_2183776 prefixEnd_2183776 1121326729752953200057003 := by
  unfold tailWord_2183776
  simp only [CollatzResearch.WordTrace]
  refine ⟨39824427068279993046553591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53099236091039990728738121 39824427068279993046553591)
  ·
    refine ⟨59736640602419989569830387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39824427068279993046553591 59736640602419989569830387)
    ·
      refine ⟨89604960903629984354745581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59736640602419989569830387 89604960903629984354745581)
      ·
        refine ⟨33601860338861244133029593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89604960903629984354745581 33601860338861244133029593)
        ·
          refine ⟨25201395254145933099772195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33601860338861244133029593 25201395254145933099772195)
          ·
            refine ⟨37802092881218899649658293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25201395254145933099772195 37802092881218899649658293)
            ·
              refine ⟨3543946207614271842155465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37802092881218899649658293 3543946207614271842155465)
              ·
                refine ⟨2657959655710703881616599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3543946207614271842155465 2657959655710703881616599)
                ·
                  refine ⟨3986939483566055822424899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2657959655710703881616599 3986939483566055822424899)
                  ·
                    refine ⟨5980409225349083733637349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3986939483566055822424899 5980409225349083733637349)
                    ·
                      refine ⟨1121326729752953200057003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5980409225349083733637349 1121326729752953200057003)
                      ·
                        rfl

theorem cell23_2183776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_2183776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183776 prefixEnd_2183776 := by exact prefixLift 2183776
  have htrace : WordTrace (prefixWord ++ tailWord_2183776) baseStart_2183776 baseEnd_2183776 := by
    simpa [prefixWord, tailWord_2183776, baseEnd_2183776] using wordTrace_append hprefix tailTrace_2183776
  have hstable : (prefixWord ++ tailWord_2183776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183776).length < 2 ^ (prefixWord ++ tailWord_2183776).sum := by decide
  have hdescent : baseEnd_2183776 < baseStart_2183776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183859 : List Nat := [1, 1, 1, 2, 3, 4, 1, 2, 2, 6]
def baseStart_2183859 : Nat := 118140960795 + 2183859 * 2 ^ 59
def prefixEnd_2183859 : Nat := 4983230072969 + 3 ^ 40 * 2183859 * 2
def baseEnd_2183859 : Nat := 373789782882425458439707

theorem tailTrace_2183859 : CollatzResearch.WordTrace tailWord_2183859 prefixEnd_2183859 373789782882425458439707 := by
  unfold tailWord_2183859
  simp only [CollatzResearch.WordTrace]
  refine ⟨79651881395259291268378631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53101254263506194178919087 79651881395259291268378631)
  ·
    refine ⟨119477822092888936902567947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79651881395259291268378631 119477822092888936902567947)
    ·
      refine ⟨179216733139333405353851921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119477822092888936902567947 179216733139333405353851921)
      ·
        refine ⟨134412549854500054015388941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179216733139333405353851921 134412549854500054015388941)
        ·
          refine ⟨50404706195437520255770853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134412549854500054015388941 50404706195437520255770853)
          ·
            refine ⟨9450882411644535047957035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50404706195437520255770853 9450882411644535047957035)
            ·
              refine ⟨14176323617466802571935553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9450882411644535047957035 14176323617466802571935553)
              ·
                refine ⟨10632242713100101928951665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14176323617466802571935553 10632242713100101928951665)
                ·
                  refine ⟨7974182034825076446713749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10632242713100101928951665 7974182034825076446713749)
                  ·
                    refine ⟨373789782882425458439707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7974182034825076446713749 373789782882425458439707)
                    ·
                      rfl

theorem cell23_2183859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 6].length) (baseStart_2183859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183859 prefixEnd_2183859 := by exact prefixLift 2183859
  have htrace : WordTrace (prefixWord ++ tailWord_2183859) baseStart_2183859 baseEnd_2183859 := by
    simpa [prefixWord, tailWord_2183859, baseEnd_2183859] using wordTrace_append hprefix tailTrace_2183859
  have hstable : (prefixWord ++ tailWord_2183859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183859).length < 2 ^ (prefixWord ++ tailWord_2183859).sum := by decide
  have hdescent : baseEnd_2183859 < baseStart_2183859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183876 : List Nat := [2, 3, 3, 1, 1, 2, 2, 1, 2, 6]
def baseStart_2183876 : Nat := 118140960795 + 2183876 * 2 ^ 59
def prefixEnd_2183876 : Nat := 4983230072969 + 3 ^ 40 * 2183876 * 2
def baseEnd_2183876 : Nat := 373792692606134269602181

theorem tailTrace_2183876 : CollatzResearch.WordTrace tailWord_2183876 prefixEnd_2183876 373792692606134269602181 := by
  unfold tailWord_2183876
  simp only [CollatzResearch.WordTrace]
  refine ⟨39826250718098851585873741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53101667624131802114498321 39826250718098851585873741)
  ·
    refine ⟨14934844019287069344702653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39826250718098851585873741 14934844019287069344702653)
    ·
      refine ⟨5600566507232651004263495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14934844019287069344702653 5600566507232651004263495)
      ·
        refine ⟨8400849760848976506395243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5600566507232651004263495 8400849760848976506395243)
        ·
          refine ⟨12601274641273464759592865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8400849760848976506395243 12601274641273464759592865)
          ·
            refine ⟨9450955980955098569694649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12601274641273464759592865 9450955980955098569694649)
            ·
              refine ⟨7088216985716323927270987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9450955980955098569694649 7088216985716323927270987)
              ·
                refine ⟨10632325478574485890906481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7088216985716323927270987 10632325478574485890906481)
                ·
                  refine ⟨7974244108930864418179861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10632325478574485890906481 7974244108930864418179861)
                  ·
                    refine ⟨373792692606134269602181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7974244108930864418179861 373792692606134269602181)
                    ·
                      rfl

theorem cell23_2183876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_2183876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183876 prefixEnd_2183876 := by exact prefixLift 2183876
  have htrace : WordTrace (prefixWord ++ tailWord_2183876) baseStart_2183876 baseEnd_2183876 := by
    simpa [prefixWord, tailWord_2183876, baseEnd_2183876] using wordTrace_append hprefix tailTrace_2183876
  have hstable : (prefixWord ++ tailWord_2183876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183876).length < 2 ^ (prefixWord ++ tailWord_2183876).sum := by decide
  have hdescent : baseEnd_2183876 < baseStart_2183876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183879 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 4]
def baseStart_2183879 : Nat := 118140960795 + 2183879 * 2 ^ 59
def prefixEnd_2183879 : Nat := 4983230072969 + 3 ^ 40 * 2183879 * 2
def baseEnd_2183879 : Nat := 1121379618260366297069029

theorem tailTrace_2183879 : CollatzResearch.WordTrace tailWord_2183879 prefixEnd_2183879 1121379618260366297069029 := by
  unfold tailWord_2183879
  simp only [CollatzResearch.WordTrace]
  refine ⟨79652610855186834684106691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53101740570124556456071127 79652610855186834684106691)
  ·
    refine ⟨119478916282780252026160037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79652610855186834684106691 119478916282780252026160037)
    ·
      refine ⟨22402296803021297254905007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119478916282780252026160037 22402296803021297254905007)
      ·
        refine ⟨33603445204531945882357511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22402296803021297254905007 33603445204531945882357511)
        ·
          refine ⟨50405167806797918823536267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33603445204531945882357511 50405167806797918823536267)
          ·
            refine ⟨75607751710196878235304401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50405167806797918823536267 75607751710196878235304401)
            ·
              refine ⟨56705813782647658676478301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75607751710196878235304401 56705813782647658676478301)
              ·
                refine ⟨21264680168492872003679363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56705813782647658676478301 21264680168492872003679363)
                ·
                  refine ⟨31897020252739308005519045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21264680168492872003679363 31897020252739308005519045)
                  ·
                    refine ⟨5980691297388620251034821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31897020252739308005519045 5980691297388620251034821)
                    ·
                      refine ⟨1121379618260366297069029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5980691297388620251034821 1121379618260366297069029)
                      ·
                        rfl

theorem cell23_2183879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_2183879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183879 prefixEnd_2183879 := by exact prefixLift 2183879
  have htrace : WordTrace (prefixWord ++ tailWord_2183879) baseStart_2183879 baseEnd_2183879 := by
    simpa [prefixWord, tailWord_2183879, baseEnd_2183879] using wordTrace_append hprefix tailTrace_2183879
  have hstable : (prefixWord ++ tailWord_2183879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183879).length < 2 ^ (prefixWord ++ tailWord_2183879).sum := by decide
  have hdescent : baseEnd_2183879 < baseStart_2183879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183889 : List Nat := [1, 2, 2, 1, 2, 3, 1, 4, 7]
def baseStart_2183889 : Nat := 118140960795 + 2183889 * 2 ^ 59
def prefixEnd_2183889 : Nat := 4983230072969 + 3 ^ 40 * 2183889 * 2
def baseEnd_2183889 : Nat := 124598305896323473104887

theorem tailTrace_2183889 : CollatzResearch.WordTrace tailWord_2183889 prefixEnd_2183889 124598305896323473104887 := by
  unfold tailWord_2183889
  simp only [CollatzResearch.WordTrace]
  refine ⟨79652975585150606391970721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53101983723433737594647147 79652975585150606391970721)
  ·
    refine ⟨59739731688862954793978041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79652975585150606391970721 59739731688862954793978041)
    ·
      refine ⟨44804798766647216095483531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59739731688862954793978041 44804798766647216095483531)
      ·
        refine ⟨67207198149970824143225297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44804798766647216095483531 67207198149970824143225297)
        ·
          refine ⟨50405398612478118107418973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67207198149970824143225297 50405398612478118107418973)
          ·
            refine ⟨18902024479679294290282115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50405398612478118107418973 18902024479679294290282115)
            ·
              refine ⟨28353036719518941435423173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18902024479679294290282115 28353036719518941435423173)
              ·
                refine ⟨5316194384909801519141845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28353036719518941435423173 5316194384909801519141845)
                ·
                  refine ⟨124598305896323473104887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5316194384909801519141845 124598305896323473104887)
                  ·
                    rfl

theorem cell23_2183889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 7].length) (baseStart_2183889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183889 prefixEnd_2183889 := by exact prefixLift 2183889
  have htrace : WordTrace (prefixWord ++ tailWord_2183889) baseStart_2183889 baseEnd_2183889 := by
    simpa [prefixWord, tailWord_2183889, baseEnd_2183889] using wordTrace_append hprefix tailTrace_2183889
  have hstable : (prefixWord ++ tailWord_2183889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183889).length < 2 ^ (prefixWord ++ tailWord_2183889).sum := by decide
  have hdescent : baseEnd_2183889 < baseStart_2183889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183934 : List Nat := [4, 2, 2, 1, 2, 1, 4, 1, 2, 2, 2]
def baseStart_2183934 : Nat := 118140960795 + 2183934 * 2 ^ 59
def prefixEnd_2183934 : Nat := 4983230072969 + 3 ^ 40 * 2183934 * 2
def baseEnd_2183934 : Nat := 1121407859696363581881277

theorem tailTrace_2183934 : CollatzResearch.WordTrace tailWord_2183934 prefixEnd_2183934 1121407859696363581881277 := by
  unfold tailWord_2183934
  simp only [CollatzResearch.WordTrace]
  refine ⟨9956827108748447384669857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53103077913325052718239237 9956827108748447384669857)
  ·
    refine ⟨7467620331561335538502393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9956827108748447384669857 7467620331561335538502393)
    ·
      refine ⟨5600715248671001653876795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7467620331561335538502393 5600715248671001653876795)
      ·
        refine ⟨8401072873006502480815193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5600715248671001653876795 8401072873006502480815193)
        ·
          refine ⟨6300804654754876860611395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8401072873006502480815193 6300804654754876860611395)
          ·
            refine ⟨9451206982132315290917093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6300804654754876860611395 9451206982132315290917093)
            ·
              refine ⟨1772101309149809117046955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9451206982132315290917093 1772101309149809117046955)
              ·
                refine ⟨2658151963724713675570433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1772101309149809117046955 2658151963724713675570433)
                ·
                  refine ⟨1993613972793535256677825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2658151963724713675570433 1993613972793535256677825)
                  ·
                    refine ⟨1495210479595151442508369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1993613972793535256677825 1495210479595151442508369)
                    ·
                      refine ⟨1121407859696363581881277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1495210479595151442508369 1121407859696363581881277)
                      ·
                        rfl

theorem cell23_2183934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_2183934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183934 prefixEnd_2183934 := by exact prefixLift 2183934
  have htrace : WordTrace (prefixWord ++ tailWord_2183934) baseStart_2183934 baseEnd_2183934 := by
    simpa [prefixWord, tailWord_2183934, baseEnd_2183934] using wordTrace_append hprefix tailTrace_2183934
  have hstable : (prefixWord ++ tailWord_2183934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183934).length < 2 ^ (prefixWord ++ tailWord_2183934).sum := by decide
  have hdescent : baseEnd_2183934 < baseStart_2183934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183973 : List Nat := [1, 3, 1, 2, 3, 1, 2, 2, 2, 4, 2]
def baseStart_2183973 : Nat := 118140960795 + 2183973 * 2 ^ 59
def prefixEnd_2183973 : Nat := 4983230072969 + 3 ^ 40 * 2183973 * 2
def baseEnd_2183973 : Nat := 1121427885441888929293597

theorem tailTrace_2183973 : CollatzResearch.WordTrace tailWord_2183973 prefixEnd_2183973 1121427885441888929293597 := by
  unfold tailWord_2183973
  simp only [CollatzResearch.WordTrace]
  refine ⟨79656039316846288738028573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53104026211230859158685715 79656039316846288738028573)
  ·
    refine ⟨29871014743817358276760715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79656039316846288738028573 29871014743817358276760715)
    ·
      refine ⟨44806522115726037415141073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29871014743817358276760715 44806522115726037415141073)
      ·
        refine ⟨33604891586794528061355805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44806522115726037415141073 33604891586794528061355805)
        ·
          refine ⟨12601834345047948023008427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33604891586794528061355805 12601834345047948023008427)
          ·
            refine ⟨18902751517571922034512641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12601834345047948023008427 18902751517571922034512641)
            ·
              refine ⟨14177063638178941525884481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18902751517571922034512641 14177063638178941525884481)
              ·
                refine ⟨10632797728634206144413361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14177063638178941525884481 10632797728634206144413361)
                ·
                  refine ⟨7974598296475654608310021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10632797728634206144413361 7974598296475654608310021)
                  ·
                    refine ⟨1495237180589185239058129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7974598296475654608310021 1495237180589185239058129)
                    ·
                      refine ⟨1121427885441888929293597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1495237180589185239058129 1121427885441888929293597)
                      ·
                        rfl

theorem cell23_2183973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 4, 2].length) (baseStart_2183973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183973 prefixEnd_2183973 := by exact prefixLift 2183973
  have htrace : WordTrace (prefixWord ++ tailWord_2183973) baseStart_2183973 baseEnd_2183973 := by
    simpa [prefixWord, tailWord_2183973, baseEnd_2183973] using wordTrace_append hprefix tailTrace_2183973
  have hstable : (prefixWord ++ tailWord_2183973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183973).length < 2 ^ (prefixWord ++ tailWord_2183973).sum := by decide
  have hdescent : baseEnd_2183973 < baseStart_2183973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2183976 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_2183976 : Nat := 118140960795 + 2183976 * 2 ^ 59
def prefixEnd_2183976 : Nat := 4983230072969 + 3 ^ 40 * 2183976 * 2
def baseEnd_2183976 : Nat := 1121429425883852417556083

theorem tailTrace_2183976 : CollatzResearch.WordTrace tailWord_2183976 prefixEnd_2183976 1121429425883852417556083 := by
  unfold tailWord_2183976
  simp only [CollatzResearch.WordTrace]
  refine ⟨39828074367917710125193891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53104099157223613500258521 39828074367917710125193891)
  ·
    refine ⟨59742111551876565187790837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39828074367917710125193891 59742111551876565187790837)
    ·
      refine ⟨5600822957988427986355391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59742111551876565187790837 5600822957988427986355391)
      ·
        refine ⟨8401234436982641979533087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5600822957988427986355391 8401234436982641979533087)
        ·
          refine ⟨12601851655473962969299631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8401234436982641979533087 12601851655473962969299631)
          ·
            refine ⟨18902777483210944453949447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12601851655473962969299631 18902777483210944453949447)
            ·
              refine ⟨28354166224816416680924171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18902777483210944453949447 28354166224816416680924171)
              ·
                refine ⟨42531249337224625021386257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28354166224816416680924171 42531249337224625021386257)
                ·
                  refine ⟨31898437002918468766039693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42531249337224625021386257 31898437002918468766039693)
                  ·
                    refine ⟨11961913876094425787264885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31898437002918468766039693 11961913876094425787264885)
                    ·
                      refine ⟨1121429425883852417556083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11961913876094425787264885 1121429425883852417556083)
                      ·
                        rfl

theorem cell23_2183976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_2183976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2183976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2183976 prefixEnd_2183976 := by exact prefixLift 2183976
  have htrace : WordTrace (prefixWord ++ tailWord_2183976) baseStart_2183976 baseEnd_2183976 := by
    simpa [prefixWord, tailWord_2183976, baseEnd_2183976] using wordTrace_append hprefix tailTrace_2183976
  have hstable : (prefixWord ++ tailWord_2183976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2183976).length < 2 ^ (prefixWord ++ tailWord_2183976).sum := by decide
  have hdescent : baseEnd_2183976 < baseStart_2183976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2183976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184004 : List Nat := [2, 3, 4, 2, 2, 1, 1, 1, 2, 5]
def baseStart_2184004 : Nat := 118140960795 + 2184004 * 2 ^ 59
def prefixEnd_2184004 : Nat := 4983230072969 + 3 ^ 40 * 2184004 * 2
def baseEnd_2184004 : Nat := 373814601114059436001985

theorem tailTrace_2184004 : CollatzResearch.WordTrace tailWord_2184004 prefixEnd_2184004 373814601114059436001985 := by
  unfold tailWord_2184004
  simp only [CollatzResearch.WordTrace]
  refine ⟨39828584989866990516203533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53104779986489320688271377 39828584989866990516203533)
  ·
    refine ⟨14935719371200121443576325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39828584989866990516203533 14935719371200121443576325)
    ·
      refine ⟨2800447382100022770670561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14935719371200121443576325 2800447382100022770670561)
      ·
        refine ⟨2100335536575017078002921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2800447382100022770670561 2100335536575017078002921)
        ·
          refine ⟨1575251652431262808502191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2100335536575017078002921 1575251652431262808502191)
          ·
            refine ⟨2362877478646894212753287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1575251652431262808502191 2362877478646894212753287)
            ·
              refine ⟨3544316217970341319129931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2362877478646894212753287 3544316217970341319129931)
              ·
                refine ⟨5316474326955511978694897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3544316217970341319129931 5316474326955511978694897)
                ·
                  refine ⟨3987355745216633984021173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5316474326955511978694897 3987355745216633984021173)
                  ·
                    refine ⟨373814601114059436001985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3987355745216633984021173 373814601114059436001985)
                    ·
                      rfl

theorem cell23_2184004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_2184004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184004 prefixEnd_2184004 := by exact prefixLift 2184004
  have htrace : WordTrace (prefixWord ++ tailWord_2184004) baseStart_2184004 baseEnd_2184004 := by
    simpa [prefixWord, tailWord_2184004, baseEnd_2184004] using wordTrace_append hprefix tailTrace_2184004
  have hstable : (prefixWord ++ tailWord_2184004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184004).length < 2 ^ (prefixWord ++ tailWord_2184004).sum := by decide
  have hdescent : baseEnd_2184004 < baseStart_2184004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184017 : List Nat := [1, 2, 2, 1, 6, 1, 2, 3, 1, 4]
def baseStart_2184017 : Nat := 118140960795 + 2184017 * 2 ^ 59
def prefixEnd_2184017 : Nat := 4983230072969 + 3 ^ 40 * 2184017 * 2
def baseEnd_2184017 : Nat := 373816826196895585714465

theorem tailTrace_2184017 : CollatzResearch.WordTrace tailWord_2184017 prefixEnd_2184017 373816826196895585714465 := by
  unfold tailWord_2184017
  simp only [CollatzResearch.WordTrace]
  refine ⟨79657644128686884252630305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53105096085791256168420203 79657644128686884252630305)
  ·
    refine ⟨59743233096515163189472729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79657644128686884252630305 59743233096515163189472729)
    ·
      refine ⟨44807424822386372392104547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59743233096515163189472729 44807424822386372392104547)
      ·
        refine ⟨67211137233579558588156821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44807424822386372392104547 67211137233579558588156821)
        ·
          refine ⟨3150522057824041808819851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 67211137233579558588156821 3150522057824041808819851)
          ·
            refine ⟨4725783086736062713229777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3150522057824041808819851 4725783086736062713229777)
            ·
              refine ⟨3544337315052047034922333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4725783086736062713229777 3544337315052047034922333)
              ·
                refine ⟨1329126493144517638095875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3544337315052047034922333 1329126493144517638095875)
                ·
                  refine ⟨1993689739716776457143813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1329126493144517638095875 1993689739716776457143813)
                  ·
                    refine ⟨373816826196895585714465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1993689739716776457143813 373816826196895585714465)
                    ·
                      rfl

theorem cell23_2184017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 3, 1, 4].length) (baseStart_2184017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184017 prefixEnd_2184017 := by exact prefixLift 2184017
  have htrace : WordTrace (prefixWord ++ tailWord_2184017) baseStart_2184017 baseEnd_2184017 := by
    simpa [prefixWord, tailWord_2184017, baseEnd_2184017] using wordTrace_append hprefix tailTrace_2184017
  have hstable : (prefixWord ++ tailWord_2184017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184017).length < 2 ^ (prefixWord ++ tailWord_2184017).sum := by decide
  have hdescent : baseEnd_2184017 < baseStart_2184017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184040 : List Nat := [2, 1, 4, 2, 1, 2, 1, 3, 3, 1, 3]
def baseStart_2184040 : Nat := 118140960795 + 2184040 * 2 ^ 59
def prefixEnd_2184040 : Nat := 4983230072969 + 3 ^ 40 * 2184040 * 2
def baseEnd_2184040 : Nat := 1121462288645740167155789

theorem tailTrace_2184040 : CollatzResearch.WordTrace tailWord_2184040 prefixEnd_2184040 1121462288645740167155789 := by
  unfold tailWord_2184040
  simp only [CollatzResearch.WordTrace]
  refine ⟨39829241503801779590358787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53105655338402372787145049 39829241503801779590358787)
  ·
    refine ⟨59743862255702669385538181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39829241503801779590358787 59743862255702669385538181)
    ·
      refine ⟨11201974172944250509788409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59743862255702669385538181 11201974172944250509788409)
      ·
        refine ⟨8401480629708187882341307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11201974172944250509788409 8401480629708187882341307)
        ·
          refine ⟨12602220944562281823511961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8401480629708187882341307 12602220944562281823511961)
          ·
            refine ⟨9451665708421711367633971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12602220944562281823511961 9451665708421711367633971)
            ·
              refine ⟨14177498562632567051450957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9451665708421711367633971 14177498562632567051450957)
              ·
                refine ⟨5316561960987212644294109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14177498562632567051450957 5316561960987212644294109)
                ·
                  refine ⟨1993710735370204741610291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5316561960987212644294109 1993710735370204741610291)
                  ·
                    refine ⟨2990566103055307112415437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1993710735370204741610291 2990566103055307112415437)
                    ·
                      refine ⟨1121462288645740167155789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2990566103055307112415437 1121462288645740167155789)
                      ·
                        rfl

theorem cell23_2184040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_2184040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184040 prefixEnd_2184040 := by exact prefixLift 2184040
  have htrace : WordTrace (prefixWord ++ tailWord_2184040) baseStart_2184040 baseEnd_2184040 := by
    simpa [prefixWord, tailWord_2184040, baseEnd_2184040] using wordTrace_append hprefix tailTrace_2184040
  have hstable : (prefixWord ++ tailWord_2184040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184040).length < 2 ^ (prefixWord ++ tailWord_2184040).sum := by decide
  have hdescent : baseEnd_2184040 < baseStart_2184040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184056 : List Nat := [2, 1, 2, 1, 1, 1, 1, 7, 1, 6]
def baseStart_2184056 : Nat := 118140960795 + 2184056 * 2 ^ 59
def prefixEnd_2184056 : Nat := 4983230072969 + 3 ^ 40 * 2184056 * 2
def baseEnd_2184056 : Nat := 373823501445404034851905

theorem tailTrace_2184056 : CollatzResearch.WordTrace tailWord_2184056 prefixEnd_2184056 373823501445404034851905 := by
  unfold tailWord_2184056
  simp only [CollatzResearch.WordTrace]
  refine ⟨39829533287772796956650011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53106044383697062608866681 39829533287772796956650011)
  ·
    refine ⟨59744299931659195434975017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39829533287772796956650011 59744299931659195434975017)
    ·
      refine ⟨44808224948744396576231263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59744299931659195434975017 44808224948744396576231263)
      ·
        refine ⟨67212337423116594864346895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44808224948744396576231263 67212337423116594864346895)
        ·
          refine ⟨100818506134674892296520343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67212337423116594864346895 100818506134674892296520343)
          ·
            refine ⟨151227759202012338444780515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100818506134674892296520343 151227759202012338444780515)
            ·
              refine ⟨226841638803018507667170773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151227759202012338444780515 226841638803018507667170773)
              ·
                refine ⟨5316600909445746273449315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 226841638803018507667170773 5316600909445746273449315)
                ·
                  refine ⟨7974901364168619410173973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5316600909445746273449315 7974901364168619410173973)
                  ·
                    refine ⟨373823501445404034851905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7974901364168619410173973 373823501445404034851905)
                    ·
                      rfl

theorem cell23_2184056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 1, 6].length) (baseStart_2184056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184056 prefixEnd_2184056 := by exact prefixLift 2184056
  have htrace : WordTrace (prefixWord ++ tailWord_2184056) baseStart_2184056 baseEnd_2184056 := by
    simpa [prefixWord, tailWord_2184056, baseEnd_2184056] using wordTrace_append hprefix tailTrace_2184056
  have hstable : (prefixWord ++ tailWord_2184056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184056).length < 2 ^ (prefixWord ++ tailWord_2184056).sum := by decide
  have hdescent : baseEnd_2184056 < baseStart_2184056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184063 : List Nat := [1, 1, 2, 2, 1, 1, 5, 4, 1, 1, 4]
def baseStart_2184063 : Nat := 118140960795 + 2184063 * 2 ^ 59
def prefixEnd_2184063 : Nat := 4983230072969 + 3 ^ 40 * 2184063 * 2
def baseEnd_2184063 : Nat := 1121474098700793577168183

theorem tailTrace_2184063 : CollatzResearch.WordTrace tailWord_2184063 prefixEnd_2184063 1121474098700793577168183 := by
  unfold tailWord_2184063
  simp only [CollatzResearch.WordTrace]
  refine ⟨79659321886520234108804843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53106214591013489405869895 79659321886520234108804843)
  ·
    refine ⟨119488982829780351163207265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79659321886520234108804843 119488982829780351163207265)
    ·
      refine ⟨89616737122335263372405449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119488982829780351163207265 89616737122335263372405449)
      ·
        refine ⟨67212552841751447529304087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89616737122335263372405449 67212552841751447529304087)
        ·
          refine ⟨100818829262627171293956131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67212552841751447529304087 100818829262627171293956131)
          ·
            refine ⟨151228243893940756940934197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100818829262627171293956131 151228243893940756940934197)
            ·
              refine ⟨14177647865056945963212581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 151228243893940756940934197 14177647865056945963212581)
              ·
                refine ⟨2658308974698177368102359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14177647865056945963212581 2658308974698177368102359)
                ·
                  refine ⟨3987463462047266052153539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2658308974698177368102359 3987463462047266052153539)
                  ·
                    refine ⟨5981195193070899078230309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3987463462047266052153539 5981195193070899078230309)
                    ·
                      refine ⟨1121474098700793577168183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5981195193070899078230309 1121474098700793577168183)
                      ·
                        rfl

theorem cell23_2184063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 1, 4].length) (baseStart_2184063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184063 prefixEnd_2184063 := by exact prefixLift 2184063
  have htrace : WordTrace (prefixWord ++ tailWord_2184063) baseStart_2184063 baseEnd_2184063 := by
    simpa [prefixWord, tailWord_2184063, baseEnd_2184063] using wordTrace_append hprefix tailTrace_2184063
  have hstable : (prefixWord ++ tailWord_2184063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184063).length < 2 ^ (prefixWord ++ tailWord_2184063).sum := by decide
  have hdescent : baseEnd_2184063 < baseStart_2184063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184073 : List Nat := [1, 2, 1, 1, 5, 2, 1, 2, 4, 4]
def baseStart_2184073 : Nat := 118140960795 + 2184073 * 2 ^ 59
def prefixEnd_2184073 : Nat := 4983230072969 + 3 ^ 40 * 2184073 * 2
def baseEnd_2184073 : Nat := 373826411169112846014379

theorem tailTrace_2184073 : CollatzResearch.WordTrace tailWord_2184073 prefixEnd_2184073 373826411169112846014379 := by
  unfold tailWord_2184073
  simp only [CollatzResearch.WordTrace]
  refine ⟨79659686616484005816668873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53106457744322670544445915 79659686616484005816668873)
  ·
    refine ⟨59744764962363004362501655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79659686616484005816668873 59744764962363004362501655)
    ·
      refine ⟨89617147443544506543752483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59744764962363004362501655 89617147443544506543752483)
      ·
        refine ⟨134425721165316759815628725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89617147443544506543752483 134425721165316759815628725)
        ·
          refine ⟨12602411359248446232715193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 134425721165316759815628725 12602411359248446232715193)
          ·
            refine ⟨9451808519436334674536395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12602411359248446232715193 9451808519436334674536395)
            ·
              refine ⟨14177712779154502011804593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9451808519436334674536395 14177712779154502011804593)
              ·
                refine ⟨10633284584365876508853445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14177712779154502011804593 10633284584365876508853445)
                ·
                  refine ⟨1993740859568601845410021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10633284584365876508853445 1993740859568601845410021)
                  ·
                    refine ⟨373826411169112846014379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1993740859568601845410021 373826411169112846014379)
                    ·
                      rfl

theorem cell23_2184073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 4, 4].length) (baseStart_2184073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184073 prefixEnd_2184073 := by exact prefixLift 2184073
  have htrace : WordTrace (prefixWord ++ tailWord_2184073) baseStart_2184073 baseEnd_2184073 := by
    simpa [prefixWord, tailWord_2184073, baseEnd_2184073] using wordTrace_append hprefix tailTrace_2184073
  have hstable : (prefixWord ++ tailWord_2184073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184073).length < 2 ^ (prefixWord ++ tailWord_2184073).sum := by decide
  have hdescent : baseEnd_2184073 < baseStart_2184073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184074 : List Nat := [3, 1, 2, 4, 1, 1, 3, 3, 1, 1, 3]
def baseStart_2184074 : Nat := 118140960795 + 2184074 * 2 ^ 59
def prefixEnd_2184074 : Nat := 4983230072969 + 3 ^ 40 * 2184074 * 2
def baseEnd_2184074 : Nat := 1121479746987993034130633

theorem tailTrace_2184074 : CollatzResearch.WordTrace tailWord_2184074 prefixEnd_2184074 1121479746987993034130633 := by
  unfold tailWord_2184074
  simp only [CollatzResearch.WordTrace]
  refine ⟨19914930772370095746863819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53106482059653588658303517 19914930772370095746863819)
  ·
    refine ⟨29872396158555143620295729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19914930772370095746863819 29872396158555143620295729)
    ·
      refine ⟨22404297118916357715221797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29872396158555143620295729 22404297118916357715221797)
      ·
        refine ⟨4200805709796817071604087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22404297118916357715221797 4200805709796817071604087)
        ·
          refine ⟨6301208564695225607406131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4200805709796817071604087 6301208564695225607406131)
          ·
            refine ⟨9451812847042838411109197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6301208564695225607406131 9451812847042838411109197)
            ·
              refine ⟨3544429817641064404165949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9451812847042838411109197 3544429817641064404165949)
              ·
                refine ⟨1329161181615399151562231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3544429817641064404165949 1329161181615399151562231)
                ·
                  refine ⟨1993741772423098727343347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1329161181615399151562231 1993741772423098727343347)
                  ·
                    refine ⟨2990612658634648091015021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1993741772423098727343347 2990612658634648091015021)
                    ·
                      refine ⟨1121479746987993034130633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2990612658634648091015021 1121479746987993034130633)
                      ·
                        rfl

theorem cell23_2184074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_2184074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184074 prefixEnd_2184074 := by exact prefixLift 2184074
  have htrace : WordTrace (prefixWord ++ tailWord_2184074) baseStart_2184074 baseEnd_2184074 := by
    simpa [prefixWord, tailWord_2184074, baseEnd_2184074] using wordTrace_append hprefix tailTrace_2184074
  have hstable : (prefixWord ++ tailWord_2184074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184074).length < 2 ^ (prefixWord ++ tailWord_2184074).sum := by decide
  have hdescent : baseEnd_2184074 < baseStart_2184074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184118 : List Nat := [5, 1, 4, 1, 1, 1, 2, 1, 2, 3, 2]
def baseStart_2184118 : Nat := 118140960795 + 2184118 * 2 ^ 59
def prefixEnd_2184118 : Nat := 4983230072969 + 3 ^ 40 * 2184118 * 2
def baseEnd_2184118 : Nat := 1121502340136790861980431

theorem tailTrace_2184118 : CollatzResearch.WordTrace tailWord_2184118 prefixEnd_2184118 1121502340136790861980431 := by
  unfold tailWord_2184118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4978832993832561156378563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53107551934213985668038005 4978832993832561156378563)
  ·
    refine ⟨7468249490748841734567845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4978832993832561156378563 7468249490748841734567845)
    ·
      refine ⟨1400296779515407825231471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7468249490748841734567845 1400296779515407825231471)
      ·
        refine ⟨2100445169273111737847207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1400296779515407825231471 2100445169273111737847207)
        ·
          refine ⟨3150667753909667606770811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2100445169273111737847207 3150667753909667606770811)
          ·
            refine ⟨4726001630864501410156217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3150667753909667606770811 4726001630864501410156217)
            ·
              refine ⟨3544501223148376057617163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4726001630864501410156217 3544501223148376057617163)
              ·
                refine ⟨5316751834722564086425745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3544501223148376057617163 5316751834722564086425745)
                ·
                  refine ⟨3987563876041923064819309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5316751834722564086425745 3987563876041923064819309)
                  ·
                    refine ⟨1495336453515721149307241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3987563876041923064819309 1495336453515721149307241)
                    ·
                      refine ⟨1121502340136790861980431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1495336453515721149307241 1121502340136790861980431)
                      ·
                        rfl

theorem cell23_2184118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_2184118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184118 prefixEnd_2184118 := by exact prefixLift 2184118
  have htrace : WordTrace (prefixWord ++ tailWord_2184118) baseStart_2184118 baseEnd_2184118 := by
    simpa [prefixWord, tailWord_2184118, baseEnd_2184118] using wordTrace_append hprefix tailTrace_2184118
  have hstable : (prefixWord ++ tailWord_2184118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184118).length < 2 ^ (prefixWord ++ tailWord_2184118).sum := by decide
  have hdescent : baseEnd_2184118 < baseStart_2184118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184148 : List Nat := [2, 4, 1, 2, 1, 4, 2, 2, 1, 2, 2]
def baseStart_2184148 : Nat := 118140960795 + 2184148 * 2 ^ 59
def prefixEnd_2184148 : Nat := 4983230072969 + 3 ^ 40 * 2184148 * 2
def baseEnd_2184148 : Nat := 1121517744556425744605293

theorem tailTrace_2184148 : CollatzResearch.WordTrace tailWord_2184148 prefixEnd_2184148 1121517744556425744605293 := by
  unfold tailWord_2184148
  simp only [CollatzResearch.WordTrace]
  refine ⟨39831211045606146812824549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53108281394141529083766065 39831211045606146812824549)
  ·
    refine ⟨7468352071051152527404603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39831211045606146812824549 7468352071051152527404603)
    ·
      refine ⟨11202528106576728791106905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7468352071051152527404603 11202528106576728791106905)
      ·
        refine ⟨8401896079932546593330179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11202528106576728791106905 8401896079932546593330179)
        ·
          refine ⟨12602844119898819889995269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8401896079932546593330179 12602844119898819889995269)
          ·
            refine ⟨2363033272481028729374113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12602844119898819889995269 2363033272481028729374113)
            ·
              refine ⟨1772274954360771547030585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2363033272481028729374113 1772274954360771547030585)
              ·
                refine ⟨1329206215770578660272939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1772274954360771547030585 1329206215770578660272939)
                ·
                  refine ⟨1993809323655867990409409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1329206215770578660272939 1993809323655867990409409)
                  ·
                    refine ⟨1495356992741900992807057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1993809323655867990409409 1495356992741900992807057)
                    ·
                      refine ⟨1121517744556425744605293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1495356992741900992807057 1121517744556425744605293)
                      ·
                        rfl

theorem cell23_2184148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_2184148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184148 prefixEnd_2184148 := by exact prefixLift 2184148
  have htrace : WordTrace (prefixWord ++ tailWord_2184148) baseStart_2184148 baseEnd_2184148 := by
    simpa [prefixWord, tailWord_2184148, baseEnd_2184148] using wordTrace_append hprefix tailTrace_2184148
  have hstable : (prefixWord ++ tailWord_2184148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184148).length < 2 ^ (prefixWord ++ tailWord_2184148).sum := by decide
  have hdescent : baseEnd_2184148 < baseStart_2184148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184150 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 2, 7]
def baseStart_2184150 : Nat := 118140960795 + 2184150 * 2 ^ 59
def prefixEnd_2184150 : Nat := 4983230072969 + 3 ^ 40 * 2184150 * 2
def baseEnd_2184150 : Nat := 373839590505911578926761

theorem tailTrace_2184150 : CollatzResearch.WordTrace tailWord_2184150 prefixEnd_2184150 373839590505911578926761 := by
  unfold tailWord_2184150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4978905939825315497951369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53108330024803365311481269 4978905939825315497951369)
  ·
    refine ⟨3734179454868986623463527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4978905939825315497951369 3734179454868986623463527)
    ·
      refine ⟨5601269182303479935195291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3734179454868986623463527 5601269182303479935195291)
      ·
        refine ⟨8401903773455219902792937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5601269182303479935195291 8401903773455219902792937)
        ·
          refine ⟨6301427830091414927094703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8401903773455219902792937 6301427830091414927094703)
          ·
            refine ⟨9452141745137122390642055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6301427830091414927094703 9452141745137122390642055)
            ·
              refine ⟨14178212617705683585963083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9452141745137122390642055 14178212617705683585963083)
              ·
                refine ⟨21267318926558525378944625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14178212617705683585963083 21267318926558525378944625)
                ·
                  refine ⟨15950489194918894034208469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21267318926558525378944625 15950489194918894034208469)
                  ·
                    refine ⟨373839590505911578926761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15950489194918894034208469 373839590505911578926761)
                    ·
                      rfl

theorem cell23_2184150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_2184150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184150 prefixEnd_2184150 := by exact prefixLift 2184150
  have htrace : WordTrace (prefixWord ++ tailWord_2184150) baseStart_2184150 baseEnd_2184150 := by
    simpa [prefixWord, tailWord_2184150, baseEnd_2184150] using wordTrace_append hprefix tailTrace_2184150
  have hstable : (prefixWord ++ tailWord_2184150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184150).length < 2 ^ (prefixWord ++ tailWord_2184150).sum := by decide
  have hdescent : baseEnd_2184150 < baseStart_2184150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184153 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 2, 3, 4]
def baseStart_2184153 : Nat := 118140960795 + 2184153 * 2 ^ 59
def prefixEnd_2184153 : Nat := 4983230072969 + 3 ^ 40 * 2184153 * 2
def baseEnd_2184153 : Nat := 1121520311959698225042769

theorem tailTrace_2184153 : CollatzResearch.WordTrace tailWord_2184153 prefixEnd_2184153 1121520311959698225042769 := by
  unfold tailWord_2184153
  simp only [CollatzResearch.WordTrace]
  refine ⟨79662604456194179479581113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53108402970796119653054075 79662604456194179479581113)
  ·
    refine ⟨59746953342145634609685835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79662604456194179479581113 59746953342145634609685835)
    ·
      refine ⟨89620430013218451914528753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59746953342145634609685835 89620430013218451914528753)
      ·
        refine ⟨67215322509913838935896565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89620430013218451914528753 67215322509913838935896565)
        ·
          refine ⟨6301436485304422400240303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67215322509913838935896565 6301436485304422400240303)
          ·
            refine ⟨9452154727956633600360455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6301436485304422400240303 9452154727956633600360455)
            ·
              refine ⟨14178232091934950400540683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9452154727956633600360455 14178232091934950400540683)
              ·
                refine ⟨21267348137902425600811025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14178232091934950400540683 21267348137902425600811025)
                ·
                  refine ⟨15950511103426819200608269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21267348137902425600811025 15950511103426819200608269)
                  ·
                    refine ⟨5981441663785057200228101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15950511103426819200608269 5981441663785057200228101)
                    ·
                      refine ⟨1121520311959698225042769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5981441663785057200228101 1121520311959698225042769)
                      ·
                        rfl

theorem cell23_2184153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_2184153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184153 prefixEnd_2184153 := by exact prefixLift 2184153
  have htrace : WordTrace (prefixWord ++ tailWord_2184153) baseStart_2184153 baseEnd_2184153 := by
    simpa [prefixWord, tailWord_2184153, baseEnd_2184153] using wordTrace_append hprefix tailTrace_2184153
  have hstable : (prefixWord ++ tailWord_2184153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184153).length < 2 ^ (prefixWord ++ tailWord_2184153).sum := by decide
  have hdescent : baseEnd_2184153 < baseStart_2184153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184157 : List Nat := [1, 4, 3, 1, 2, 1, 1, 2, 3, 3, 2]
def baseStart_2184157 : Nat := 118140960795 + 2184157 * 2 ^ 59
def prefixEnd_2184157 : Nat := 4983230072969 + 3 ^ 40 * 2184157 * 2
def baseEnd_2184157 : Nat := 1121522365882316209392751

theorem tailTrace_2184157 : CollatzResearch.WordTrace tailWord_2184157 prefixEnd_2184157 1121522365882316209392751 := by
  unfold tailWord_2184157
  simp only [CollatzResearch.WordTrace]
  refine ⟨79662750348179688162726725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53108500232119792108484483 79662750348179688162726725)
  ·
    refine ⟨14936765690283691530511261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79662750348179688162726725 14936765690283691530511261)
    ·
      refine ⟨5601287133856384323941723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14936765690283691530511261 5601287133856384323941723)
      ·
        refine ⟨8401930700784576485912585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5601287133856384323941723 8401930700784576485912585)
        ·
          refine ⟨6301448025588432364434439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8401930700784576485912585 6301448025588432364434439)
          ·
            refine ⟨9452172038382648546651659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6301448025588432364434439 9452172038382648546651659)
            ·
              refine ⟨14178258057573972819977489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9452172038382648546651659 14178258057573972819977489)
              ·
                refine ⟨10633693543180479614983117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14178258057573972819977489 10633693543180479614983117)
                ·
                  refine ⟨3987635078692679855618669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10633693543180479614983117 3987635078692679855618669)
                  ·
                    refine ⟨1495363154509754945857001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3987635078692679855618669 1495363154509754945857001)
                    ·
                      refine ⟨1121522365882316209392751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1495363154509754945857001 1121522365882316209392751)
                      ·
                        rfl

theorem cell23_2184157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_2184157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184157 prefixEnd_2184157 := by exact prefixLift 2184157
  have htrace : WordTrace (prefixWord ++ tailWord_2184157) baseStart_2184157 baseEnd_2184157 := by
    simpa [prefixWord, tailWord_2184157, baseEnd_2184157] using wordTrace_append hprefix tailTrace_2184157
  have hstable : (prefixWord ++ tailWord_2184157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184157).length < 2 ^ (prefixWord ++ tailWord_2184157).sum := by decide
  have hdescent : baseEnd_2184157 < baseStart_2184157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184163 : List Nat := [1, 1, 1, 6, 1, 1, 3, 1, 2, 6]
def baseStart_2184163 : Nat := 118140960795 + 2184163 * 2 ^ 59
def prefixEnd_2184163 : Nat := 4983230072969 + 3 ^ 40 * 2184163 * 2
def baseEnd_2184163 : Nat := 373841815588747728639241

theorem tailTrace_2184163 : CollatzResearch.WordTrace tailWord_2184163 prefixEnd_2184163 373841815588747728639241 := by
  unfold tailWord_2184163
  simp only [CollatzResearch.WordTrace]
  refine ⟨79662969186157951187445143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53108646124105300791630095 79662969186157951187445143)
  ·
    refine ⟨119494453779236926781167715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79662969186157951187445143 119494453779236926781167715)
    ·
      refine ⟨179241680668855390171751573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119494453779236926781167715 179241680668855390171751573)
      ·
        refine ⟨8401953781352596414300855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 179241680668855390171751573 8401953781352596414300855)
        ·
          refine ⟨12602930672028894621451283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8401953781352596414300855 12602930672028894621451283)
          ·
            refine ⟨18904396008043341932176925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12602930672028894621451283 18904396008043341932176925)
            ·
              refine ⟨7089148503016253224566347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18904396008043341932176925 7089148503016253224566347)
              ·
                refine ⟨10633722754524379836849521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7089148503016253224566347 10633722754524379836849521)
                ·
                  refine ⟨7975292065893284877637141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10633722754524379836849521 7975292065893284877637141)
                  ·
                    refine ⟨373841815588747728639241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7975292065893284877637141 373841815588747728639241)
                    ·
                      rfl

theorem cell23_2184163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 6].length) (baseStart_2184163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184163 prefixEnd_2184163 := by exact prefixLift 2184163
  have htrace : WordTrace (prefixWord ++ tailWord_2184163) baseStart_2184163 baseEnd_2184163 := by
    simpa [prefixWord, tailWord_2184163, baseEnd_2184163] using wordTrace_append hprefix tailTrace_2184163
  have hstable : (prefixWord ++ tailWord_2184163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184163).length < 2 ^ (prefixWord ++ tailWord_2184163).sum := by decide
  have hdescent : baseEnd_2184163 < baseStart_2184163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184204 : List Nat := [2, 2, 1, 2, 3, 2, 3, 2, 2, 2, 2]
def baseStart_2184204 : Nat := 118140960795 + 2184204 * 2 ^ 59
def prefixEnd_2184204 : Nat := 4983230072969 + 3 ^ 40 * 2184204 * 2
def baseEnd_2184204 : Nat := 1121546499473077525505035

theorem tailTrace_2184204 : CollatzResearch.WordTrace tailWord_2184204 prefixEnd_2184204 1121546499473077525505035 := by
  unfold tailWord_2184204
  simp only [CollatzResearch.WordTrace]
  refine ⟨39832232289504707594843833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53109643052672943459791777 39832232289504707594843833)
  ·
    refine ⟨29874174217128530696132875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39832232289504707594843833 29874174217128530696132875)
    ·
      refine ⟨44811261325692796044199313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29874174217128530696132875 44811261325692796044199313)
      ·
        refine ⟨33608445994269597033149485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44811261325692796044199313 33608445994269597033149485)
        ·
          refine ⟨12603167247851098887431057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33608445994269597033149485 12603167247851098887431057)
          ·
            refine ⟨9452375435888324165573293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12603167247851098887431057 9452375435888324165573293)
            ·
              refine ⟨3544640788458121562089985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9452375435888324165573293 3544640788458121562089985)
              ·
                refine ⟨2658480591343591171567489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3544640788458121562089985 2658480591343591171567489)
                ·
                  refine ⟨1993860443507693378675617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2658480591343591171567489 1993860443507693378675617)
                  ·
                    refine ⟨1495395332630770034006713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1993860443507693378675617 1495395332630770034006713)
                    ·
                      refine ⟨1121546499473077525505035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1495395332630770034006713 1121546499473077525505035)
                      ·
                        rfl

theorem cell23_2184204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 2, 2, 2].length) (baseStart_2184204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184204 prefixEnd_2184204 := by exact prefixLift 2184204
  have htrace : WordTrace (prefixWord ++ tailWord_2184204) baseStart_2184204 baseEnd_2184204 := by
    simpa [prefixWord, tailWord_2184204, baseEnd_2184204] using wordTrace_append hprefix tailTrace_2184204
  have hstable : (prefixWord ++ tailWord_2184204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184204).length < 2 ^ (prefixWord ++ tailWord_2184204).sum := by decide
  have hdescent : baseEnd_2184204 < baseStart_2184204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184221 : List Nat := [1, 4, 2, 2, 4, 1, 1, 1, 1, 4, 2]
def baseStart_2184221 : Nat := 118140960795 + 2184221 * 2 ^ 59
def prefixEnd_2184221 : Nat := 4983230072969 + 3 ^ 40 * 2184221 * 2
def baseEnd_2184221 : Nat := 1121555228644203958992457

theorem tailTrace_2184221 : CollatzResearch.WordTrace tailWord_2184221 prefixEnd_2184221 1121555228644203958992457 := by
  unfold tailWord_2184221
  simp only [CollatzResearch.WordTrace]
  refine ⟨79665084619947827093056517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53110056413298551395371011 79665084619947827093056517)
  ·
    refine ⟨14937203366240217579948097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79665084619947827093056517 14937203366240217579948097)
    ·
      refine ⟨11202902524680163184961073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14937203366240217579948097 11202902524680163184961073)
      ·
        refine ⟨8402176893510122388720805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11202902524680163184961073 8402176893510122388720805)
        ·
          refine ⟨1575408167533147947885151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8402176893510122388720805 1575408167533147947885151)
          ·
            refine ⟨2363112251299721921827727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1575408167533147947885151 2363112251299721921827727)
            ·
              refine ⟨3544668376949582882741591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2363112251299721921827727 3544668376949582882741591)
              ·
                refine ⟨5317002565424374324112387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3544668376949582882741591 5317002565424374324112387)
                ·
                  refine ⟨7975503848136561486168581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5317002565424374324112387 7975503848136561486168581)
                  ·
                    refine ⟨1495406971525605278656609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7975503848136561486168581 1495406971525605278656609)
                    ·
                      refine ⟨1121555228644203958992457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1495406971525605278656609 1121555228644203958992457)
                      ·
                        rfl

theorem cell23_2184221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_2184221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184221 prefixEnd_2184221 := by exact prefixLift 2184221
  have htrace : WordTrace (prefixWord ++ tailWord_2184221) baseStart_2184221 baseEnd_2184221 := by
    simpa [prefixWord, tailWord_2184221, baseEnd_2184221] using wordTrace_append hprefix tailTrace_2184221
  have hstable : (prefixWord ++ tailWord_2184221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184221).length < 2 ^ (prefixWord ++ tailWord_2184221).sum := by decide
  have hdescent : baseEnd_2184221 < baseStart_2184221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184223 : List Nat := [1, 1, 2, 4, 1, 3, 1, 2, 1, 7]
def baseStart_2184223 : Nat := 118140960795 + 2184223 * 2 ^ 59
def prefixEnd_2184223 : Nat := 4983230072969 + 3 ^ 40 * 2184223 * 2
def baseEnd_2184223 : Nat := 373852085201837650389149

theorem tailTrace_2184223 : CollatzResearch.WordTrace tailWord_2184223 prefixEnd_2184223 373852085201837650389149 := by
  unfold tailWord_2184223
  simp only [CollatzResearch.WordTrace]
  refine ⟨79665157565940581434629323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53110105043960387623086215 79665157565940581434629323)
  ·
    refine ⟨119497736348910872151943985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79665157565940581434629323 119497736348910872151943985)
    ·
      refine ⟨89623302261683154113957989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119497736348910872151943985 89623302261683154113957989)
      ·
        refine ⟨16804369174065591396367123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89623302261683154113957989 16804369174065591396367123)
        ·
          refine ⟨25206553761098387094550685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16804369174065591396367123 25206553761098387094550685)
          ·
            refine ⟨9452457660411895160456507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25206553761098387094550685 9452457660411895160456507)
            ·
              refine ⟨14178686490617842740684761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9452457660411895160456507 14178686490617842740684761)
              ·
                refine ⟨10634014867963382055513571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14178686490617842740684761 10634014867963382055513571)
                ·
                  refine ⟨15951022301945073083270357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10634014867963382055513571 15951022301945073083270357)
                  ·
                    refine ⟨373852085201837650389149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15951022301945073083270357 373852085201837650389149)
                    ·
                      rfl

theorem cell23_2184223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 7].length) (baseStart_2184223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184223 prefixEnd_2184223 := by exact prefixLift 2184223
  have htrace : WordTrace (prefixWord ++ tailWord_2184223) baseStart_2184223 baseEnd_2184223 := by
    simpa [prefixWord, tailWord_2184223, baseEnd_2184223] using wordTrace_append hprefix tailTrace_2184223
  have hstable : (prefixWord ++ tailWord_2184223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184223).length < 2 ^ (prefixWord ++ tailWord_2184223).sum := by decide
  have hdescent : baseEnd_2184223 < baseStart_2184223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184244 : List Nat := [2, 5, 1, 2, 1, 1, 3, 3, 5]
def baseStart_2184244 : Nat := 118140960795 + 2184244 * 2 ^ 59
def prefixEnd_2184244 : Nat := 4983230072969 + 3 ^ 40 * 2184244 * 2
def baseEnd_2184244 : Nat := 124618559855473041000539

theorem tailTrace_2184244 : CollatzResearch.WordTrace tailWord_2184244 prefixEnd_2184244 124618559855473041000539 := by
  unfold tailWord_2184244
  simp only [CollatzResearch.WordTrace]
  refine ⟨39832961749432251010571893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53110615665909668014095857 39832961749432251010571893)
  ·
    refine ⟨3734340164009273532241115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39832961749432251010571893 3734340164009273532241115)
    ·
      refine ⟨5601510246013910298361673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3734340164009273532241115 5601510246013910298361673)
      ·
        refine ⟨4201132684510432723771255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5601510246013910298361673 4201132684510432723771255)
        ·
          refine ⟨6301699026765649085656883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4201132684510432723771255 6301699026765649085656883)
          ·
            refine ⟨9452548540148473628485325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6301699026765649085656883 9452548540148473628485325)
            ·
              refine ⟨3544705702555677610681997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9452548540148473628485325 3544705702555677610681997)
              ·
                refine ⟨1329264638458379104005749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3544705702555677610681997 1329264638458379104005749)
                ·
                  refine ⟨124618559855473041000539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1329264638458379104005749 124618559855473041000539)
                  ·
                    rfl

theorem cell23_2184244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_2184244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184244 prefixEnd_2184244 := by exact prefixLift 2184244
  have htrace : WordTrace (prefixWord ++ tailWord_2184244) baseStart_2184244 baseEnd_2184244 := by
    simpa [prefixWord, tailWord_2184244, baseEnd_2184244] using wordTrace_append hprefix tailTrace_2184244
  have hstable : (prefixWord ++ tailWord_2184244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184244).length < 2 ^ (prefixWord ++ tailWord_2184244).sum := by decide
  have hdescent : baseEnd_2184244 < baseStart_2184244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184257 : List Nat := [1, 2, 5, 1, 3, 1, 1, 2, 2, 5]
def baseStart_2184257 : Nat := 118140960795 + 2184257 * 2 ^ 59
def prefixEnd_2184257 : Nat := 4983230072969 + 3 ^ 40 * 2184257 * 2
def baseEnd_2184257 : Nat := 373857904649255272714097

theorem tailTrace_2184257 : CollatzResearch.WordTrace tailWord_2184257 prefixEnd_2184257 373857904649255272714097 := by
  unfold tailWord_2184257
  simp only [CollatzResearch.WordTrace]
  refine ⟨79666397647817405241367025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53110931765211603494244683 79666397647817405241367025)
  ·
    refine ⟨59749798235863053931025269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79666397647817405241367025 59749798235863053931025269)
    ·
      refine ⟨5601543584612161306033619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59749798235863053931025269 5601543584612161306033619)
      ·
        refine ⟨8402315376918241959050429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5601543584612161306033619 8402315376918241959050429)
        ·
          refine ⟨3150868266344340734643911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8402315376918241959050429 3150868266344340734643911)
          ·
            refine ⟨4726302399516511101965867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3150868266344340734643911 4726302399516511101965867)
            ·
              refine ⟨7089453599274766652948801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4726302399516511101965867 7089453599274766652948801)
              ·
                refine ⟨5317090199456074989711601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7089453599274766652948801 5317090199456074989711601)
                ·
                  refine ⟨3987817649592056242283701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5317090199456074989711601 3987817649592056242283701)
                  ·
                    refine ⟨373857904649255272714097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3987817649592056242283701 373857904649255272714097)
                    ·
                      rfl

theorem cell23_2184257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_2184257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184257 prefixEnd_2184257 := by exact prefixLift 2184257
  have htrace : WordTrace (prefixWord ++ tailWord_2184257) baseStart_2184257 baseEnd_2184257 := by
    simpa [prefixWord, tailWord_2184257, baseEnd_2184257] using wordTrace_append hprefix tailTrace_2184257
  have hstable : (prefixWord ++ tailWord_2184257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184257).length < 2 ^ (prefixWord ++ tailWord_2184257).sum := by decide
  have hdescent : baseEnd_2184257 < baseStart_2184257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184273 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 2, 1, 6]
def baseStart_2184273 : Nat := 118140960795 + 2184273 * 2 ^ 59
def prefixEnd_2184273 : Nat := 4983230072969 + 3 ^ 40 * 2184273 * 2
def baseEnd_2184273 : Nat := 1121581929638237755542217

theorem tailTrace_2184273 : CollatzResearch.WordTrace tailWord_2184273 prefixEnd_2184273 1121581929638237755542217 := by
  unfold tailWord_2184273
  simp only [CollatzResearch.WordTrace]
  refine ⟨79666981215759439973949473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53111320810506293315966315 79666981215759439973949473)
  ·
    refine ⟨59750235911819579980462105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79666981215759439973949473 59750235911819579980462105)
    ·
      refine ⟨44812676933864684985346579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59750235911819579980462105 44812676933864684985346579)
      ·
        refine ⟨67219015400797027478019869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44812676933864684985346579 67219015400797027478019869)
        ·
          refine ⟨25207130775298885304257451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67219015400797027478019869 25207130775298885304257451)
          ·
            refine ⟨37810696162948327956386177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25207130775298885304257451 37810696162948327956386177)
            ·
              refine ⟨28358022122211245967289633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37810696162948327956386177 28358022122211245967289633)
              ·
                refine ⟨21268516591658434475467225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28358022122211245967289633 21268516591658434475467225)
                ·
                  refine ⟨15951387443743825856600419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21268516591658434475467225 15951387443743825856600419)
                  ·
                    refine ⟨23927081165615738784900629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15951387443743825856600419 23927081165615738784900629)
                    ·
                      refine ⟨1121581929638237755542217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23927081165615738784900629 1121581929638237755542217)
                      ·
                        rfl

theorem cell23_2184273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_2184273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184273 prefixEnd_2184273 := by exact prefixLift 2184273
  have htrace : WordTrace (prefixWord ++ tailWord_2184273) baseStart_2184273 baseEnd_2184273 := by
    simpa [prefixWord, tailWord_2184273, baseEnd_2184273] using wordTrace_append hprefix tailTrace_2184273
  have hstable : (prefixWord ++ tailWord_2184273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184273).length < 2 ^ (prefixWord ++ tailWord_2184273).sum := by decide
  have hdescent : baseEnd_2184273 < baseStart_2184273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184280 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 4, 2, 3]
def baseStart_2184280 : Nat := 118140960795 + 2184280 * 2 ^ 59
def prefixEnd_2184280 : Nat := 4983230072969 + 3 ^ 40 * 2184280 * 2
def baseEnd_2184280 : Nat := 1121585524002819228154685

theorem tailTrace_2184280 : CollatzResearch.WordTrace tailWord_2184280 prefixEnd_2184280 1121585524002819228154685 := by
  unfold tailWord_2184280
  simp only [CollatzResearch.WordTrace]
  refine ⟨39833618263367040084727147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53111491017822720112969529 39833618263367040084727147)
  ·
    refine ⟨59750427395050560127090721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39833618263367040084727147 59750427395050560127090721)
    ·
      refine ⟨44812820546287920095318041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59750427395050560127090721 44812820546287920095318041)
      ·
        refine ⟨33609615409715940071488531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44812820546287920095318041 33609615409715940071488531)
        ·
          refine ⟨50414423114573910107232797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33609615409715940071488531 50414423114573910107232797)
          ·
            refine ⟨18905408667965216290212299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50414423114573910107232797 18905408667965216290212299)
            ·
              refine ⟨28358113001947824435318449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18905408667965216290212299 28358113001947824435318449)
              ·
                refine ⟨21268584751460868326488837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28358113001947824435318449 21268584751460868326488837)
                ·
                  refine ⟨3987859640898912811216657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21268584751460868326488837 3987859640898912811216657)
                  ·
                    refine ⟨2990894730674184608412493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3987859640898912811216657 2990894730674184608412493)
                    ·
                      refine ⟨1121585524002819228154685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2990894730674184608412493 1121585524002819228154685)
                      ·
                        rfl

theorem cell23_2184280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_2184280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184280 prefixEnd_2184280 := by exact prefixLift 2184280
  have htrace : WordTrace (prefixWord ++ tailWord_2184280) baseStart_2184280 baseEnd_2184280 := by
    simpa [prefixWord, tailWord_2184280, baseEnd_2184280] using wordTrace_append hprefix tailTrace_2184280
  have hstable : (prefixWord ++ tailWord_2184280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184280).length < 2 ^ (prefixWord ++ tailWord_2184280).sum := by decide
  have hdescent : baseEnd_2184280 < baseStart_2184280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184297 : List Nat := [1, 2, 1, 1, 1, 7, 2, 1, 2, 2, 3]
def baseStart_2184297 : Nat := 118140960795 + 2184297 * 2 ^ 59
def prefixEnd_2184297 : Nat := 4983230072969 + 3 ^ 40 * 2184297 * 2
def baseEnd_2184297 : Nat := 1121594253173945661642107

theorem tailTrace_2184297 : CollatzResearch.WordTrace tailWord_2184297 prefixEnd_2184297 1121594253173945661642107 := by
  unfold tailWord_2184297
  simp only [CollatzResearch.WordTrace]
  refine ⟨79667856567672492072823145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53111904378448328048548763 79667856567672492072823145)
  ·
    refine ⟨59750892425754369054617359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79667856567672492072823145 59750892425754369054617359)
    ·
      refine ⟨89626338638631553581926039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59750892425754369054617359 89626338638631553581926039)
      ·
        refine ⟨134439507957947330372889059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89626338638631553581926039 134439507957947330372889059)
        ·
          refine ⟨201659261936920995559333589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134439507957947330372889059 201659261936920995559333589)
          ·
            refine ⟨4726388951646585833421881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 201659261936920995559333589 4726388951646585833421881)
            ·
              refine ⟨3544791713734939375066411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4726388951646585833421881 3544791713734939375066411)
              ·
                refine ⟨5317187570602409062599617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3544791713734939375066411 5317187570602409062599617)
                ·
                  refine ⟨3987890677951806796949713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5317187570602409062599617 3987890677951806796949713)
                  ·
                    refine ⟨2990918008463855097712285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3987890677951806796949713 2990918008463855097712285)
                    ·
                      refine ⟨1121594253173945661642107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2990918008463855097712285 1121594253173945661642107)
                      ·
                        rfl

theorem cell23_2184297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 2, 3].length) (baseStart_2184297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184297 prefixEnd_2184297 := by exact prefixLift 2184297
  have htrace : WordTrace (prefixWord ++ tailWord_2184297) baseStart_2184297 baseEnd_2184297 := by
    simpa [prefixWord, tailWord_2184297, baseEnd_2184297] using wordTrace_append hprefix tailTrace_2184297
  have hstable : (prefixWord ++ tailWord_2184297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184297).length < 2 ^ (prefixWord ++ tailWord_2184297).sum := by decide
  have hdescent : baseEnd_2184297 < baseStart_2184297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184321 : List Nat := [1, 2, 4, 2, 2, 1, 4, 2, 1, 4]
def baseStart_2184321 : Nat := 118140960795 + 2184321 * 2 ^ 59
def prefixEnd_2184321 : Nat := 4983230072969 + 3 ^ 40 * 2184321 * 2
def baseEnd_2184321 : Nat := 373868858903217855913999

theorem tailTrace_2184321 : CollatzResearch.WordTrace tailWord_2184321 prefixEnd_2184321 373868858903217855913999 := by
  unfold tailWord_2184321
  simp only [CollatzResearch.WordTrace]
  refine ⟨79668731919585544171696817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53112487946390362781131211 79668731919585544171696817)
  ·
    refine ⟨59751548939689158128772613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79668731919585544171696817 59751548939689158128772613)
    ·
      refine ⟨11203415426191717149144865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59751548939689158128772613 11203415426191717149144865)
      ·
        refine ⟨8402561569643787861858649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11203415426191717149144865 8402561569643787861858649)
        ·
          refine ⟨6301921177232840896393987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8402561569643787861858649 6301921177232840896393987)
          ·
            refine ⟨9452881765849261344590981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6301921177232840896393987 9452881765849261344590981)
            ·
              refine ⟨1772415331096736502110809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9452881765849261344590981 1772415331096736502110809)
              ·
                refine ⟨1329311498322552376583107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1772415331096736502110809 1329311498322552376583107)
                ·
                  refine ⟨1993967247483828564874661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1329311498322552376583107 1993967247483828564874661)
                  ·
                    refine ⟨373868858903217855913999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1993967247483828564874661 373868858903217855913999)
                    ·
                      rfl

theorem cell23_2184321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_2184321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184321 prefixEnd_2184321 := by exact prefixLift 2184321
  have htrace : WordTrace (prefixWord ++ tailWord_2184321) baseStart_2184321 baseEnd_2184321 := by
    simpa [prefixWord, tailWord_2184321, baseEnd_2184321] using wordTrace_append hprefix tailTrace_2184321
  have hstable : (prefixWord ++ tailWord_2184321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184321).length < 2 ^ (prefixWord ++ tailWord_2184321).sum := by decide
  have hdescent : baseEnd_2184321 < baseStart_2184321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184327 : List Nat := [1, 1, 4, 2, 1, 1, 1, 5, 3, 1, 3]
def baseStart_2184327 : Nat := 118140960795 + 2184327 * 2 ^ 59
def prefixEnd_2184327 : Nat := 4983230072969 + 3 ^ 40 * 2184327 * 2
def baseEnd_2184327 : Nat := 1121609657593580544266969

theorem tailTrace_2184327 : CollatzResearch.WordTrace tailWord_2184327 prefixEnd_2184327 1121609657593580544266969 := by
  unfold tailWord_2184327
  simp only [CollatzResearch.WordTrace]
  refine ⟨79668950757563807196415235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53112633838375871464276823 79668950757563807196415235)
  ·
    refine ⟨119503426136345710794622853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79668950757563807196415235 119503426136345710794622853)
    ·
      refine ⟨22406892400564820773991785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119503426136345710794622853 22406892400564820773991785)
      ·
        refine ⟨16805169300423615580493839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22406892400564820773991785 16805169300423615580493839)
        ·
          refine ⟨25207753950635423370740759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16805169300423615580493839 25207753950635423370740759)
          ·
            refine ⟨37811630925953135056111139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25207753950635423370740759 37811630925953135056111139)
            ·
              refine ⟨56717446388929702584166709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37811630925953135056111139 56717446388929702584166709)
              ·
                refine ⟨5317260598962159617265629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56717446388929702584166709 5317260598962159617265629)
                ·
                  refine ⟨1993972724610809856474611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5317260598962159617265629 1993972724610809856474611)
                  ·
                    refine ⟨2990959086916214784711917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1993972724610809856474611 2990959086916214784711917)
                    ·
                      refine ⟨1121609657593580544266969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2990959086916214784711917 1121609657593580544266969)
                      ·
                        rfl

theorem cell23_2184327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_2184327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184327 prefixEnd_2184327 := by exact prefixLift 2184327
  have htrace : WordTrace (prefixWord ++ tailWord_2184327) baseStart_2184327 baseEnd_2184327 := by
    simpa [prefixWord, tailWord_2184327, baseEnd_2184327] using wordTrace_append hprefix tailTrace_2184327
  have hstable : (prefixWord ++ tailWord_2184327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184327).length < 2 ^ (prefixWord ++ tailWord_2184327).sum := by decide
  have hdescent : baseEnd_2184327 < baseStart_2184327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184330 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 5, 5]
def baseStart_2184330 : Nat := 118140960795 + 2184330 * 2 ^ 59
def prefixEnd_2184330 : Nat := 4983230072969 + 3 ^ 40 * 2184330 * 2
def baseEnd_2184330 : Nat := 373870399345181344176485

theorem tailTrace_2184330 : CollatzResearch.WordTrace tailWord_2184330 prefixEnd_2184330 373870399345181344176485 := by
  unfold tailWord_2184330
  simp only [CollatzResearch.WordTrace]
  refine ⟨19917265044138234677193611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53112706784368625805849629 19917265044138234677193611)
  ·
    refine ⟨29875897566207352015790417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19917265044138234677193611 29875897566207352015790417)
    ·
      refine ⟨22406923174655514011842813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29875897566207352015790417 22406923174655514011842813)
      ·
        refine ⟨8402596190495817754441055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22406923174655514011842813 8402596190495817754441055)
        ·
          refine ⟨12603894285743726631661583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8402596190495817754441055 12603894285743726631661583)
          ·
            refine ⟨18905841428615589947492375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12603894285743726631661583 18905841428615589947492375)
            ·
              refine ⟨28358762142923384921238563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18905841428615589947492375 28358762142923384921238563)
              ·
                refine ⟨42538143214385077381857845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28358762142923384921238563 42538143214385077381857845)
                ·
                  refine ⟨3987950926348601004549173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42538143214385077381857845 3987950926348601004549173)
                  ·
                    refine ⟨373870399345181344176485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3987950926348601004549173 373870399345181344176485)
                    ·
                      rfl

theorem cell23_2184330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_2184330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184330 prefixEnd_2184330 := by exact prefixLift 2184330
  have htrace : WordTrace (prefixWord ++ tailWord_2184330) baseStart_2184330 baseEnd_2184330 := by
    simpa [prefixWord, tailWord_2184330, baseEnd_2184330] using wordTrace_append hprefix tailTrace_2184330
  have hstable : (prefixWord ++ tailWord_2184330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184330).length < 2 ^ (prefixWord ++ tailWord_2184330).sum := by decide
  have hdescent : baseEnd_2184330 < baseStart_2184330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184344 : List Nat := [2, 1, 2, 4, 2, 2, 1, 2, 3, 1, 3]
def baseStart_2184344 : Nat := 118140960795 + 2184344 * 2 ^ 59
def prefixEnd_2184344 : Nat := 4983230072969 + 3 ^ 40 * 2184344 * 2
def baseEnd_2184344 : Nat := 1121618386764706977754391

theorem tailTrace_2184344 : CollatzResearch.WordTrace tailWord_2184344 prefixEnd_2184344 1121618386764706977754391 := by
  unfold tailWord_2184344
  simp only [CollatzResearch.WordTrace]
  refine ⟨39834785399251109549892043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53113047199001479399856057 39834785399251109549892043)
  ·
    refine ⟨59752178098876664324838065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39834785399251109549892043 59752178098876664324838065)
    ·
      refine ⟨44814133574157498243628549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59752178098876664324838065 44814133574157498243628549)
      ·
        refine ⟨8402650045154530920680353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44814133574157498243628549 8402650045154530920680353)
        ·
          refine ⟨6301987533865898190510265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8402650045154530920680353 6301987533865898190510265)
          ·
            refine ⟨4726490650399423642882699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6301987533865898190510265 4726490650399423642882699)
            ·
              refine ⟨7089735975599135464324049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4726490650399423642882699 7089735975599135464324049)
              ·
                refine ⟨5317301981699351598243037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7089735975599135464324049 5317301981699351598243037)
                ·
                  refine ⟨1993988243137256849341139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5317301981699351598243037 1993988243137256849341139)
                  ·
                    refine ⟨2990982364705885274011709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1993988243137256849341139 2990982364705885274011709)
                    ·
                      refine ⟨1121618386764706977754391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2990982364705885274011709 1121618386764706977754391)
                      ·
                        rfl

theorem cell23_2184344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_2184344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184344 prefixEnd_2184344 := by exact prefixLift 2184344
  have htrace : WordTrace (prefixWord ++ tailWord_2184344) baseStart_2184344 baseEnd_2184344 := by
    simpa [prefixWord, tailWord_2184344, baseEnd_2184344] using wordTrace_append hprefix tailTrace_2184344
  have hstable : (prefixWord ++ tailWord_2184344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184344).length < 2 ^ (prefixWord ++ tailWord_2184344).sum := by decide
  have hdescent : baseEnd_2184344 < baseStart_2184344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184377 : List Nat := [1, 2, 1, 4, 1, 4, 1, 1, 4, 4]
def baseStart_2184377 : Nat := 118140960795 + 2184377 * 2 ^ 59
def prefixEnd_2184377 : Nat := 4983230072969 + 3 ^ 40 * 2184377 * 2
def baseEnd_2184377 : Nat := 373878443875435116213913

theorem tailTrace_2184377 : CollatzResearch.WordTrace tailWord_2184377 prefixEnd_2184377 373878443875435116213913 := by
  unfold tailWord_2184377
  simp only [CollatzResearch.WordTrace]
  refine ⟨79670774407382665735735385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53113849604921777157156923 79670774407382665735735385)
  ·
    refine ⟨59753080805536999301801539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79670774407382665735735385 59753080805536999301801539)
    ·
      refine ⟨89629621208305498952702309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59753080805536999301801539 89629621208305498952702309)
      ·
        refine ⟨16805553976557281053631683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89629621208305498952702309 16805553976557281053631683)
        ·
          refine ⟨25208330964835921580447525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16805553976557281053631683 25208330964835921580447525)
          ·
            refine ⟨4726562055906735296333911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25208330964835921580447525 4726562055906735296333911)
            ·
              refine ⟨7089843083860102944500867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4726562055906735296333911 7089843083860102944500867)
              ·
                refine ⟨10634764625790154416751301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7089843083860102944500867 10634764625790154416751301)
                ·
                  refine ⟨1994018367335653953140869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10634764625790154416751301 1994018367335653953140869)
                  ·
                    refine ⟨373878443875435116213913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1994018367335653953140869 373878443875435116213913)
                    ·
                      rfl

theorem cell23_2184377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 4, 4].length) (baseStart_2184377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184377 prefixEnd_2184377 := by exact prefixLift 2184377
  have htrace : WordTrace (prefixWord ++ tailWord_2184377) baseStart_2184377 baseEnd_2184377 := by
    simpa [prefixWord, tailWord_2184377, baseEnd_2184377] using wordTrace_append hprefix tailTrace_2184377
  have hstable : (prefixWord ++ tailWord_2184377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184377).length < 2 ^ (prefixWord ++ tailWord_2184377).sum := by decide
  have hdescent : baseEnd_2184377 < baseStart_2184377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184451 : List Nat := [1, 1, 1, 3, 2, 4, 4, 1, 2, 1, 3]
def baseStart_2184451 : Nat := 118140960795 + 2184451 * 2 ^ 59
def prefixEnd_2184451 : Nat := 4983230072969 + 3 ^ 40 * 2184451 * 2
def baseEnd_2184451 : Nat := 1121673329194738059116399

theorem tailTrace_2184451 : CollatzResearch.WordTrace tailWord_2184451 prefixEnd_2184451 1121673329194738059116399 := by
  unfold tailWord_2184451
  simp only [CollatzResearch.WordTrace]
  refine ⟨79673473409114576373929207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53115648939409717582619471 79673473409114576373929207)
  ·
    refine ⟨119510210113671864560893811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79673473409114576373929207 119510210113671864560893811)
    ·
      refine ⟨179265315170507796841340717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119510210113671864560893811 179265315170507796841340717)
      ·
        refine ⟨67224493188940423815502769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179265315170507796841340717 67224493188940423815502769)
        ·
          refine ⟨50418369891705317861627077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67224493188940423815502769 50418369891705317861627077)
          ·
            refine ⟨9453444354694747099055077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50418369891705317861627077 9453444354694747099055077)
            ·
              refine ⟨1772520816505265081072827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9453444354694747099055077 1772520816505265081072827)
              ·
                refine ⟨2658781224757897621609241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1772520816505265081072827 2658781224757897621609241)
                ·
                  refine ⟨1994085918568423216206931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2658781224757897621609241 1994085918568423216206931)
                  ·
                    refine ⟨2991128877852634824310397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1994085918568423216206931 2991128877852634824310397)
                    ·
                      refine ⟨1121673329194738059116399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2991128877852634824310397 1121673329194738059116399)
                      ·
                        rfl

theorem cell23_2184451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 2, 1, 3].length) (baseStart_2184451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184451 prefixEnd_2184451 := by exact prefixLift 2184451
  have htrace : WordTrace (prefixWord ++ tailWord_2184451) baseStart_2184451 baseEnd_2184451 := by
    simpa [prefixWord, tailWord_2184451, baseEnd_2184451] using wordTrace_append hprefix tailTrace_2184451
  have hstable : (prefixWord ++ tailWord_2184451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184451).length < 2 ^ (prefixWord ++ tailWord_2184451).sum := by decide
  have hdescent : baseEnd_2184451 < baseStart_2184451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184474 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 3, 4, 2]
def baseStart_2184474 : Nat := 118140960795 + 2184474 * 2 ^ 59
def prefixEnd_2184474 : Nat := 4983230072969 + 3 ^ 40 * 2184474 * 2
def baseEnd_2184474 : Nat := 1121685139249791469128793

theorem tailTrace_2184474 : CollatzResearch.WordTrace tailWord_2184474 prefixEnd_2184474 1121685139249791469128793 := by
  unfold tailWord_2184474
  simp only [CollatzResearch.WordTrace]
  refine ⟨19918578072007812825504119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53116208192020834201344317 19918578072007812825504119)
  ·
    refine ⟨29877867108011719238256179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19918578072007812825504119 29877867108011719238256179)
    ·
      refine ⟨44816800662017578857384269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29877867108011719238256179 44816800662017578857384269)
      ·
        refine ⟨16806300248256592071519101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44816800662017578857384269 16806300248256592071519101)
        ·
          refine ⟨6302362593096222026819663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16806300248256592071519101 6302362593096222026819663)
          ·
            refine ⟨9453543889644333040229495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6302362593096222026819663 9453543889644333040229495)
            ·
              refine ⟨14180315834466499560344243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9453543889644333040229495 14180315834466499560344243)
              ·
                refine ⟨21270473751699749340516365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14180315834466499560344243 21270473751699749340516365)
                ·
                  refine ⟨7976427656887406002693637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21270473751699749340516365 7976427656887406002693637)
                  ·
                    refine ⟨1495580185666388625505057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7976427656887406002693637 1495580185666388625505057)
                    ·
                      refine ⟨1121685139249791469128793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1495580185666388625505057 1121685139249791469128793)
                      ·
                        rfl

theorem cell23_2184474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_2184474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184474 prefixEnd_2184474 := by exact prefixLift 2184474
  have htrace : WordTrace (prefixWord ++ tailWord_2184474) baseStart_2184474 baseEnd_2184474 := by
    simpa [prefixWord, tailWord_2184474, baseEnd_2184474] using wordTrace_append hprefix tailTrace_2184474
  have hstable : (prefixWord ++ tailWord_2184474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184474).length < 2 ^ (prefixWord ++ tailWord_2184474).sum := by decide
  have hdescent : baseEnd_2184474 < baseStart_2184474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184567 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 3, 4, 3]
def baseStart_2184567 : Nat := 118140960795 + 2184567 * 2 ^ 59
def prefixEnd_2184567 : Nat := 4983230072969 + 3 ^ 40 * 2184567 * 2
def baseEnd_2184567 : Nat := 1121732892950659605265865

theorem tailTrace_2184567 : CollatzResearch.WordTrace tailWord_2184567 prefixEnd_2184567 1121732892950659605265865 := by
  unfold tailWord_2184567
  simp only [CollatzResearch.WordTrace]
  refine ⟨79677704276694328185151955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53118469517796218790101303 79677704276694328185151955)
  ·
    refine ⟨119516556415041492277727933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79677704276694328185151955 119516556415041492277727933)
    ·
      refine ⟨44818708655640559604147975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119516556415041492277727933 44818708655640559604147975)
      ·
        refine ⟨67228062983460839406221963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44818708655640559604147975 67228062983460839406221963)
        ·
          refine ⟨100842094475191259109332945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67228062983460839406221963 100842094475191259109332945)
          ·
            refine ⟨75631570856393444331999709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100842094475191259109332945 75631570856393444331999709)
            ·
              refine ⟨28361839071147541624499891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75631570856393444331999709 28361839071147541624499891)
              ·
                refine ⟨42542758606721312436749837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28361839071147541624499891 42542758606721312436749837)
                ·
                  refine ⟨15953534477520492163781189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42542758606721312436749837 15953534477520492163781189)
                  ·
                    refine ⟨2991287714535092280708973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15953534477520492163781189 2991287714535092280708973)
                    ·
                      refine ⟨1121732892950659605265865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2991287714535092280708973 1121732892950659605265865)
                      ·
                        rfl

theorem cell23_2184567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 4, 3].length) (baseStart_2184567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184567 prefixEnd_2184567 := by exact prefixLift 2184567
  have htrace : WordTrace (prefixWord ++ tailWord_2184567) baseStart_2184567 baseEnd_2184567 := by
    simpa [prefixWord, tailWord_2184567, baseEnd_2184567] using wordTrace_append hprefix tailTrace_2184567
  have hstable : (prefixWord ++ tailWord_2184567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184567).length < 2 ^ (prefixWord ++ tailWord_2184567).sum := by decide
  have hdescent : baseEnd_2184567 < baseStart_2184567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184584 : List Nat := [2, 1, 3, 3, 1, 2, 2, 1, 1, 4, 3]
def baseStart_2184584 : Nat := 118140960795 + 2184584 * 2 ^ 59
def prefixEnd_2184584 : Nat := 4983230072969 + 3 ^ 40 * 2184584 * 2
def baseEnd_2184584 : Nat := 1121741622121786038753287

theorem tailTrace_2184584 : CollatzResearch.WordTrace tailWord_2184584 prefixEnd_2184584 1121741622121786038753287 := by
  unfold tailWord_2184584
  simp only [CollatzResearch.WordTrace]
  refine ⟨39839162158816370044260403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53118882878421826725680537 39839162158816370044260403)
  ·
    refine ⟨59758743238224555066390605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39839162158816370044260403 59758743238224555066390605)
    ·
      refine ⟨22409528714334208149896477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59758743238224555066390605 22409528714334208149896477)
      ·
        refine ⟨8403573267875328056211179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22409528714334208149896477 8403573267875328056211179)
        ·
          refine ⟨12605359901812992084316769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8403573267875328056211179 12605359901812992084316769)
          ·
            refine ⟨9454019926359744063237577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12605359901812992084316769 9454019926359744063237577)
            ·
              refine ⟨7090514944769808047428183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9454019926359744063237577 7090514944769808047428183)
              ·
                refine ⟨10635772417154712071142275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7090514944769808047428183 10635772417154712071142275)
                ·
                  refine ⟨15953658625732068106713413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10635772417154712071142275 15953658625732068106713413)
                  ·
                    refine ⟨2991310992324762770008765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15953658625732068106713413 2991310992324762770008765)
                    ·
                      refine ⟨1121741622121786038753287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2991310992324762770008765 1121741622121786038753287)
                      ·
                        rfl

theorem cell23_2184584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_2184584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184584 prefixEnd_2184584 := by exact prefixLift 2184584
  have htrace : WordTrace (prefixWord ++ tailWord_2184584) baseStart_2184584 baseEnd_2184584 := by
    simpa [prefixWord, tailWord_2184584, baseEnd_2184584] using wordTrace_append hprefix tailTrace_2184584
  have hstable : (prefixWord ++ tailWord_2184584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184584).length < 2 ^ (prefixWord ++ tailWord_2184584).sum := by decide
  have hdescent : baseEnd_2184584 < baseStart_2184584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184608 : List Nat := [2, 1, 1, 4, 1, 2, 5, 2, 1, 4]
def baseStart_2184608 : Nat := 118140960795 + 2184608 * 2 ^ 59
def prefixEnd_2184608 : Nat := 4983230072969 + 3 ^ 40 * 2184608 * 2
def baseEnd_2184608 : Nat := 373917981885831314951059

theorem tailTrace_2184608 : CollatzResearch.WordTrace tailWord_2184608 prefixEnd_2184608 373917981885831314951059 := by
  unfold tailWord_2184608
  simp only [CollatzResearch.WordTrace]
  refine ⟨39839599834772896093697239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53119466446363861458262985 39839599834772896093697239)
  ·
    refine ⟨59759399752159344140545859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39839599834772896093697239 59759399752159344140545859)
    ·
      refine ⟨89639099628239016210818789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59759399752159344140545859 89639099628239016210818789)
      ·
        refine ⟨16807331180294815539528523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89639099628239016210818789 16807331180294815539528523)
        ·
          refine ⟨25210996770442223309292785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16807331180294815539528523 25210996770442223309292785)
          ·
            refine ⟨18908247577831667481969589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25210996770442223309292785 18908247577831667481969589)
            ·
              refine ⟨1772648210421718826434649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18908247577831667481969589 1772648210421718826434649)
              ·
                refine ⟨1329486157816289119825987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1772648210421718826434649 1329486157816289119825987)
                ·
                  refine ⟨1994229236724433679738981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1329486157816289119825987 1994229236724433679738981)
                  ·
                    refine ⟨373917981885831314951059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1994229236724433679738981 373917981885831314951059)
                    ·
                      rfl

theorem cell23_2184608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 2, 1, 4].length) (baseStart_2184608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184608 prefixEnd_2184608 := by exact prefixLift 2184608
  have htrace : WordTrace (prefixWord ++ tailWord_2184608) baseStart_2184608 baseEnd_2184608 := by
    simpa [prefixWord, tailWord_2184608, baseEnd_2184608] using wordTrace_append hprefix tailTrace_2184608
  have hstable : (prefixWord ++ tailWord_2184608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184608).length < 2 ^ (prefixWord ++ tailWord_2184608).sum := by decide
  have hdescent : baseEnd_2184608 < baseStart_2184608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184621 : List Nat := [1, 5, 2, 2, 1, 2, 1, 3, 6]
def baseStart_2184621 : Nat := 118140960795 + 2184621 * 2 ^ 59
def prefixEnd_2184621 : Nat := 4983230072969 + 3 ^ 40 * 2184621 * 2
def baseEnd_2184621 : Nat := 124640068989555821554513

theorem tailTrace_2184621 : CollatzResearch.WordTrace tailWord_2184621 prefixEnd_2184621 124640068989555821554513 := by
  unfold tailWord_2184621
  simp only [CollatzResearch.WordTrace]
  refine ⟨79679673818498695407617717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53119782545665796938411811 79679673818498695407617717)
  ·
    refine ⟨7469969420484252694464161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79679673818498695407617717 7469969420484252694464161)
    ·
      refine ⟨5602477065363189520848121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7469969420484252694464161 5602477065363189520848121)
      ·
        refine ⟨4201857799022392140636091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5602477065363189520848121 4201857799022392140636091)
        ·
          refine ⟨6302786698533588210954137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4201857799022392140636091 6302786698533588210954137)
          ·
            refine ⟨4727090023900191158215603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6302786698533588210954137 4727090023900191158215603)
            ·
              refine ⟨7090635035850286737323405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4727090023900191158215603 7090635035850286737323405)
              ·
                refine ⟨2658988138443857526496277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7090635035850286737323405 2658988138443857526496277)
                ·
                  refine ⟨124640068989555821554513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2658988138443857526496277 124640068989555821554513)
                  ·
                    rfl

theorem cell23_2184621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_2184621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184621 prefixEnd_2184621 := by exact prefixLift 2184621
  have htrace : WordTrace (prefixWord ++ tailWord_2184621) baseStart_2184621 baseEnd_2184621 := by
    simpa [prefixWord, tailWord_2184621, baseEnd_2184621] using wordTrace_append hprefix tailTrace_2184621
  have hstable : (prefixWord ++ tailWord_2184621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184621).length < 2 ^ (prefixWord ++ tailWord_2184621).sum := by decide
  have hdescent : baseEnd_2184621 < baseStart_2184621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184624 : List Nat := [2, 1, 1, 1, 2, 1, 1, 6, 1, 5, 2]
def baseStart_2184624 : Nat := 118140960795 + 2184624 * 2 ^ 59
def prefixEnd_2184624 : Nat := 4983230072969 + 3 ^ 40 * 2184624 * 2
def baseEnd_2184624 : Nat := 1121762161347965882253103

theorem tailTrace_2184624 : CollatzResearch.WordTrace tailWord_2184624 prefixEnd_2184624 1121762161347965882253103 := by
  unfold tailWord_2184624
  simp only [CollatzResearch.WordTrace]
  refine ⟨39839891618743913459988463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53119855491658551279984617 39839891618743913459988463)
  ·
    refine ⟨59759837428115870189982695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39839891618743913459988463 59759837428115870189982695)
    ·
      refine ⟨89639756142173805284974043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59759837428115870189982695 89639756142173805284974043)
      ·
        refine ⟨134459634213260707927461065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89639756142173805284974043 134459634213260707927461065)
        ·
          refine ⟨100844725659945530945595799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134459634213260707927461065 100844725659945530945595799)
          ·
            refine ⟨151267088489918296418393699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100844725659945530945595799 151267088489918296418393699)
            ·
              refine ⟨226900632734877444627590549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151267088489918296418393699 226900632734877444627590549)
              ·
                refine ⟨10635967159447380216918307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 226900632734877444627590549 10635967159447380216918307)
                ·
                  refine ⟨15953950739171070325377461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10635967159447380216918307 15953950739171070325377461)
                  ·
                    refine ⟨1495682881797287843004137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15953950739171070325377461 1495682881797287843004137)
                    ·
                      refine ⟨1121762161347965882253103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1495682881797287843004137 1121762161347965882253103)
                      ·
                        rfl

theorem cell23_2184624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 1, 5, 2].length) (baseStart_2184624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184624 prefixEnd_2184624 := by exact prefixLift 2184624
  have htrace : WordTrace (prefixWord ++ tailWord_2184624) baseStart_2184624 baseEnd_2184624 := by
    simpa [prefixWord, tailWord_2184624, baseEnd_2184624] using wordTrace_append hprefix tailTrace_2184624
  have hstable : (prefixWord ++ tailWord_2184624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184624).length < 2 ^ (prefixWord ++ tailWord_2184624).sum := by decide
  have hdescent : baseEnd_2184624 < baseStart_2184624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184648 : List Nat := [2, 1, 3, 1, 3, 1, 2, 5, 1, 1, 3]
def baseStart_2184648 : Nat := 118140960795 + 2184648 * 2 ^ 59
def prefixEnd_2184648 : Nat := 4983230072969 + 3 ^ 40 * 2184648 * 2
def baseEnd_2184648 : Nat := 1121774484883673788352993

theorem tailTrace_2184648 : CollatzResearch.WordTrace tailWord_2184648 prefixEnd_2184648 1121774484883673788352993 := by
  unfold tailWord_2184648
  simp only [CollatzResearch.WordTrace]
  refine ⟨39840329294700439509425299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53120439059600586012567065 39840329294700439509425299)
  ·
    refine ⟨59760493942050659264137949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39840329294700439509425299 59760493942050659264137949)
    ·
      refine ⟨22410185228268997224051731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59760493942050659264137949 22410185228268997224051731)
      ·
        refine ⟨33615277842403495836077597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22410185228268997224051731 33615277842403495836077597)
        ·
          refine ⟨12605729190901310938529099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33615277842403495836077597 12605729190901310938529099)
          ·
            refine ⟨18908593786351966407793649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12605729190901310938529099 18908593786351966407793649)
            ·
              refine ⟨14181445339763974805845237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18908593786351966407793649 14181445339763974805845237)
              ·
                refine ⟨1329510500602872638047991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14181445339763974805845237 1329510500602872638047991)
                ·
                  refine ⟨1994265750904308957071987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1329510500602872638047991 1994265750904308957071987)
                  ·
                    refine ⟨2991398626356463435607981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1994265750904308957071987 2991398626356463435607981)
                    ·
                      refine ⟨1121774484883673788352993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2991398626356463435607981 1121774484883673788352993)
                      ·
                        rfl

theorem cell23_2184648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 5, 1, 1, 3].length) (baseStart_2184648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184648 prefixEnd_2184648 := by exact prefixLift 2184648
  have htrace : WordTrace (prefixWord ++ tailWord_2184648) baseStart_2184648 baseEnd_2184648 := by
    simpa [prefixWord, tailWord_2184648, baseEnd_2184648] using wordTrace_append hprefix tailTrace_2184648
  have hstable : (prefixWord ++ tailWord_2184648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184648).length < 2 ^ (prefixWord ++ tailWord_2184648).sum := by decide
  have hdescent : baseEnd_2184648 < baseStart_2184648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184664 : List Nat := [2, 1, 2, 2, 2, 1, 2, 3, 4, 4]
def baseStart_2184664 : Nat := 118140960795 + 2184664 * 2 ^ 59
def prefixEnd_2184664 : Nat := 4983230072969 + 3 ^ 40 * 2184664 * 2
def baseEnd_2184664 : Nat := 373927566858048575250973

theorem tailTrace_2184664 : CollatzResearch.WordTrace tailWord_2184664 prefixEnd_2184664 373927566858048575250973 := by
  unfold tailWord_2184664
  simp only [CollatzResearch.WordTrace]
  refine ⟨39840621078671456875716523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53120828104895275834288697 39840621078671456875716523)
  ·
    refine ⟨59760931618007185313574785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39840621078671456875716523 59760931618007185313574785)
    ·
      refine ⟨44820698713505388985181089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59760931618007185313574785 44820698713505388985181089)
      ·
        refine ⟨33615524035129041738885817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44820698713505388985181089 33615524035129041738885817)
        ·
          refine ⟨25211643026346781304164363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33615524035129041738885817 25211643026346781304164363)
          ·
            refine ⟨37817464539520171956246545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25211643026346781304164363 37817464539520171956246545)
            ·
              refine ⟨28363098404640128967184909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37817464539520171956246545 28363098404640128967184909)
              ·
                refine ⟨10636161901740048362694341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28363098404640128967184909 10636161901740048362694341)
                ·
                  refine ⟨1994280356576259068005189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10636161901740048362694341 1994280356576259068005189)
                  ·
                    refine ⟨373927566858048575250973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1994280356576259068005189 373927566858048575250973)
                    ·
                      rfl

theorem cell23_2184664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 4, 4].length) (baseStart_2184664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184664 prefixEnd_2184664 := by exact prefixLift 2184664
  have htrace : WordTrace (prefixWord ++ tailWord_2184664) baseStart_2184664 baseEnd_2184664 := by
    simpa [prefixWord, tailWord_2184664, baseEnd_2184664] using wordTrace_append hprefix tailTrace_2184664
  have hstable : (prefixWord ++ tailWord_2184664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184664).length < 2 ^ (prefixWord ++ tailWord_2184664).sum := by decide
  have hdescent : baseEnd_2184664 < baseStart_2184664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184665 : List Nat := [1, 2, 1, 2, 4, 2, 4, 2, 1, 1, 3]
def baseStart_2184665 : Nat := 118140960795 + 2184665 * 2 ^ 59
def prefixEnd_2184665 : Nat := 4983230072969 + 3 ^ 40 * 2184665 * 2
def baseEnd_2184665 : Nat := 1121783214054800221840415

theorem tailTrace_2184665 : CollatzResearch.WordTrace tailWord_2184665 prefixEnd_2184665 1121783214054800221840415 := by
  unfold tailWord_2184665
  simp only [CollatzResearch.WordTrace]
  refine ⟨79681278630339290922219449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53120852420226193948146299 79681278630339290922219449)
  ·
    refine ⟨59760958972754468191664587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79681278630339290922219449 59760958972754468191664587)
    ·
      refine ⟨89641438459131702287496881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59760958972754468191664587 89641438459131702287496881)
      ·
        refine ⟨67231078844348776715622661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89641438459131702287496881 67231078844348776715622661)
        ·
          refine ⟨12605827283315395634179249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67231078844348776715622661 12605827283315395634179249)
          ·
            refine ⟨9454370462486546725634437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12605827283315395634179249 9454370462486546725634437)
            ·
              refine ⟨1772694461716227511056457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9454370462486546725634437 1772694461716227511056457)
              ·
                refine ⟨1329520846287170633292343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1772694461716227511056457 1329520846287170633292343)
                ·
                  refine ⟨1994281269430755949938515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1329520846287170633292343 1994281269430755949938515)
                  ·
                    refine ⟨2991421904146133924907773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1994281269430755949938515 2991421904146133924907773)
                    ·
                      refine ⟨1121783214054800221840415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2991421904146133924907773 1121783214054800221840415)
                      ·
                        rfl

theorem cell23_2184665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 2, 1, 1, 3].length) (baseStart_2184665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184665 prefixEnd_2184665 := by exact prefixLift 2184665
  have htrace : WordTrace (prefixWord ++ tailWord_2184665) baseStart_2184665 baseEnd_2184665 := by
    simpa [prefixWord, tailWord_2184665, baseEnd_2184665] using wordTrace_append hprefix tailTrace_2184665
  have hstable : (prefixWord ++ tailWord_2184665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184665).length < 2 ^ (prefixWord ++ tailWord_2184665).sum := by decide
  have hdescent : baseEnd_2184665 < baseStart_2184665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184688 : List Nat := [2, 1, 1, 1, 3, 5, 1, 2, 3, 2, 2]
def baseStart_2184688 : Nat := 118140960795 + 2184688 * 2 ^ 59
def prefixEnd_2184688 : Nat := 4983230072969 + 3 ^ 40 * 2184688 * 2
def baseEnd_2184688 : Nat := 1121795024109853631852809

theorem tailTrace_2184688 : CollatzResearch.WordTrace tailWord_2184688 prefixEnd_2184688 1121795024109853631852809 := by
  unfold tailWord_2184688
  simp only [CollatzResearch.WordTrace]
  refine ⟨39841058754627982925153359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53121411672837310566871145 39841058754627982925153359)
  ·
    refine ⟨59761588131941974387730039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39841058754627982925153359 59761588131941974387730039)
    ·
      refine ⟨89642382197912961581595059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59761588131941974387730039 89642382197912961581595059)
      ·
        refine ⟨134463573296869442372392589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89642382197912961581595059 134463573296869442372392589)
        ·
          refine ⟨50423839986326040889647221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134463573296869442372392589 50423839986326040889647221)
          ·
            refine ⟨4727234998718066333404427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50423839986326040889647221 4727234998718066333404427)
            ·
              refine ⟨7090852498077099500106641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4727234998718066333404427 7090852498077099500106641)
              ·
                refine ⟨5318139373557824625079981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7090852498077099500106641 5318139373557824625079981)
                ·
                  refine ⟨1994302265084184234404993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5318139373557824625079981 1994302265084184234404993)
                  ·
                    refine ⟨1495726698813138175803745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1994302265084184234404993 1495726698813138175803745)
                    ·
                      refine ⟨1121795024109853631852809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1495726698813138175803745 1121795024109853631852809)
                      ·
                        rfl

theorem cell23_2184688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 3, 2, 2].length) (baseStart_2184688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184688 prefixEnd_2184688 := by exact prefixLift 2184688
  have htrace : WordTrace (prefixWord ++ tailWord_2184688) baseStart_2184688 baseEnd_2184688 := by
    simpa [prefixWord, tailWord_2184688, baseEnd_2184688] using wordTrace_append hprefix tailTrace_2184688
  have hstable : (prefixWord ++ tailWord_2184688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184688).length < 2 ^ (prefixWord ++ tailWord_2184688).sum := by decide
  have hdescent : baseEnd_2184688 < baseStart_2184688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184702 : List Nat := [4, 2, 2, 3, 1, 2, 2, 1, 1, 5]
def baseStart_2184702 : Nat := 118140960795 + 2184702 * 2 ^ 59
def prefixEnd_2184702 : Nat := 4983230072969 + 3 ^ 40 * 2184702 * 2
def baseEnd_2184702 : Nat := 373934070946338859025915

theorem tailTrace_2184702 : CollatzResearch.WordTrace tailWord_2184702 prefixEnd_2184702 373934070946338859025915 := by
  unfold tailWord_2184702
  simp only [CollatzResearch.WordTrace]
  refine ⟨9960328516400655780164545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53121752087470164160877573 9960328516400655780164545)
  ·
    refine ⟨7470246387300491835123409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9960328516400655780164545 7470246387300491835123409)
    ·
      refine ⟨5602684790475368876342557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7470246387300491835123409 5602684790475368876342557)
      ·
        refine ⟨2101006796428263328628459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5602684790475368876342557 2101006796428263328628459)
        ·
          refine ⟨3151510194642394992942689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2101006796428263328628459 3151510194642394992942689)
          ·
            refine ⟨2363632645981796244707017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3151510194642394992942689 2363632645981796244707017)
            ·
              refine ⟨1772724484486347183530263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2363632645981796244707017 1772724484486347183530263)
              ·
                refine ⟨2659086726729520775295395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1772724484486347183530263 2659086726729520775295395)
                ·
                  refine ⟨3988630090094281162943093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2659086726729520775295395 3988630090094281162943093)
                  ·
                    refine ⟨373934070946338859025915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3988630090094281162943093 373934070946338859025915)
                    ·
                      rfl

theorem cell23_2184702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_2184702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184702 prefixEnd_2184702 := by exact prefixLift 2184702
  have htrace : WordTrace (prefixWord ++ tailWord_2184702) baseStart_2184702 baseEnd_2184702 := by
    simpa [prefixWord, tailWord_2184702, baseEnd_2184702] using wordTrace_append hprefix tailTrace_2184702
  have hstable : (prefixWord ++ tailWord_2184702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184702).length < 2 ^ (prefixWord ++ tailWord_2184702).sum := by decide
  have hdescent : baseEnd_2184702 < baseStart_2184702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184705 : List Nat := [1, 2, 4, 1, 4, 2, 2, 1, 1, 1, 4]
def baseStart_2184705 : Nat := 118140960795 + 2184705 * 2 ^ 59
def prefixEnd_2184705 : Nat := 4983230072969 + 3 ^ 40 * 2184705 * 2
def baseEnd_2184705 : Nat := 1121803753280980065340231

theorem tailTrace_2184705 : CollatzResearch.WordTrace tailWord_2184705 prefixEnd_2184705 1121803753280980065340231 := by
  unfold tailWord_2184705
  simp only [CollatzResearch.WordTrace]
  refine ⟨79682737550194377753675569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53121825033462918502450379 79682737550194377753675569)
  ·
    refine ⟨59762053162645783315256677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79682737550194377753675569 59762053162645783315256677)
    ·
      refine ⟨11205384967996084371610627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59762053162645783315256677 11205384967996084371610627)
      ·
        refine ⟨16808077451994126557415941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11205384967996084371610627 16808077451994126557415941)
        ·
          refine ⟨3151514522248898729515489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16808077451994126557415941 3151514522248898729515489)
          ·
            refine ⟨2363635891686674047136617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3151514522248898729515489 2363635891686674047136617)
            ·
              refine ⟨1772726918765005535352463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2363635891686674047136617 1772726918765005535352463)
              ·
                refine ⟨2659090378147508303028695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1772726918765005535352463 2659090378147508303028695)
                ·
                  refine ⟨3988635567221262454543043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2659090378147508303028695 3988635567221262454543043)
                  ·
                    refine ⟨5982953350831893681814565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3988635567221262454543043 5982953350831893681814565)
                    ·
                      refine ⟨1121803753280980065340231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5982953350831893681814565 1121803753280980065340231)
                      ·
                        rfl

theorem cell23_2184705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_2184705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184705 prefixEnd_2184705 := by exact prefixLift 2184705
  have htrace : WordTrace (prefixWord ++ tailWord_2184705) baseStart_2184705 baseEnd_2184705 := by
    simpa [prefixWord, tailWord_2184705, baseEnd_2184705] using wordTrace_append hprefix tailTrace_2184705
  have hstable : (prefixWord ++ tailWord_2184705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184705).length < 2 ^ (prefixWord ++ tailWord_2184705).sum := by decide
  have hdescent : baseEnd_2184705 < baseStart_2184705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184707 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 1, 9]
def baseStart_2184707 : Nat := 118140960795 + 2184707 * 2 ^ 59
def prefixEnd_2184707 : Nat := 4983230072969 + 3 ^ 40 * 2184707 * 2
def baseEnd_2184707 : Nat := 373934926747429685838407

theorem tailTrace_2184707 : CollatzResearch.WordTrace tailWord_2184707 prefixEnd_2184707 373934926747429685838407 := by
  unfold tailWord_2184707
  simp only [CollatzResearch.WordTrace]
  refine ⟨79682810496187132095248375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53121873664124754730165583 79682810496187132095248375)
  ·
    refine ⟨119524215744280698142872563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79682810496187132095248375 119524215744280698142872563)
    ·
      refine ⟨179286323616421047214308845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119524215744280698142872563 179286323616421047214308845)
      ·
        refine ⟨67232371356157892705365817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179286323616421047214308845 67232371356157892705365817)
        ·
          refine ⟨50424278517118419529024363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67232371356157892705365817 50424278517118419529024363)
          ·
            refine ⟨75636417775677629293536545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50424278517118419529024363 75636417775677629293536545)
            ·
              refine ⟨56727313331758221970152409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75636417775677629293536545 56727313331758221970152409)
              ·
                refine ⟨42545484998818666477614307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56727313331758221970152409 42545484998818666477614307)
                ·
                  refine ⟨63818227498227999716421461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42545484998818666477614307 63818227498227999716421461)
                  ·
                    refine ⟨373934926747429685838407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 63818227498227999716421461 373934926747429685838407)
                    ·
                      rfl

theorem cell23_2184707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 9].length) (baseStart_2184707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184707 prefixEnd_2184707 := by exact prefixLift 2184707
  have htrace : WordTrace (prefixWord ++ tailWord_2184707) baseStart_2184707 baseEnd_2184707 := by
    simpa [prefixWord, tailWord_2184707, baseEnd_2184707] using wordTrace_append hprefix tailTrace_2184707
  have hstable : (prefixWord ++ tailWord_2184707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184707).length < 2 ^ (prefixWord ++ tailWord_2184707).sum := by decide
  have hdescent : baseEnd_2184707 < baseStart_2184707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184715 : List Nat := [1, 1, 1, 1, 9, 1, 1, 2, 2, 4]
def baseStart_2184715 : Nat := 118140960795 + 2184715 * 2 ^ 59
def prefixEnd_2184715 : Nat := 4983230072969 + 3 ^ 40 * 2184715 * 2
def baseEnd_2184715 : Nat := 373936296029175008738395

theorem tailTrace_2184715 : CollatzResearch.WordTrace tailWord_2184715 prefixEnd_2184715 373936296029175008738395 := by
  unfold tailWord_2184715
  simp only [CollatzResearch.WordTrace]
  refine ⟨79683102280158149461539599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53122068186772099641026399 79683102280158149461539599)
  ·
    refine ⟨119524653420237224192309399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79683102280158149461539599 119524653420237224192309399)
    ·
      refine ⟨179286980130355836288464099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119524653420237224192309399 179286980130355836288464099)
      ·
        refine ⟨268930470195533754432696149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179286980130355836288464099 268930470195533754432696149)
        ·
          refine ⟨1575764473801955592379079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 268930470195533754432696149 1575764473801955592379079)
          ·
            refine ⟨2363646710702933388568619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1575764473801955592379079 2363646710702933388568619)
            ·
              refine ⟨3545470066054400082852929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2363646710702933388568619 3545470066054400082852929)
              ·
                refine ⟨2659102549540800062139697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3545470066054400082852929 2659102549540800062139697)
                ·
                  refine ⟨1994326912155600046604773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2659102549540800062139697 1994326912155600046604773)
                  ·
                    refine ⟨373936296029175008738395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1994326912155600046604773 373936296029175008738395)
                    ·
                      rfl

theorem cell23_2184715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 2, 4].length) (baseStart_2184715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184715 prefixEnd_2184715 := by exact prefixLift 2184715
  have htrace : WordTrace (prefixWord ++ tailWord_2184715) baseStart_2184715 baseEnd_2184715 := by
    simpa [prefixWord, tailWord_2184715, baseEnd_2184715] using wordTrace_append hprefix tailTrace_2184715
  have hstable : (prefixWord ++ tailWord_2184715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184715).length < 2 ^ (prefixWord ++ tailWord_2184715).sum := by decide
  have hdescent : baseEnd_2184715 < baseStart_2184715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184721 : List Nat := [1, 2, 2, 1, 1, 2, 5, 1, 4, 1, 3]
def baseStart_2184721 : Nat := 118140960795 + 2184721 * 2 ^ 59
def prefixEnd_2184721 : Nat := 4983230072969 + 3 ^ 40 * 2184721 * 2
def baseEnd_2184721 : Nat := 1121811968971452002740157

theorem tailTrace_2184721 : CollatzResearch.WordTrace tailWord_2184721 prefixEnd_2184721 1121811968971452002740157 := by
  unfold tailWord_2184721
  simp only [CollatzResearch.WordTrace]
  refine ⟨79683321118136412486258017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53122214078757608324172011 79683321118136412486258017)
  ·
    refine ⟨59762490838602309364693513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79683321118136412486258017 59762490838602309364693513)
    ·
      refine ⟨44821868128951732023520135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59762490838602309364693513 44821868128951732023520135)
      ·
        refine ⟨67232802193427598035280203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44821868128951732023520135 67232802193427598035280203)
        ·
          refine ⟨100849203290141397052920305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67232802193427598035280203 100849203290141397052920305)
          ·
            refine ⟨75636902467606047789690229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100849203290141397052920305 75636902467606047789690229)
            ·
              refine ⟨7090959606338066980283459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75636902467606047789690229 7090959606338066980283459)
              ·
                refine ⟨10636439409507100470425189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7090959606338066980283459 10636439409507100470425189)
                ·
                  refine ⟨1994332389282581338204723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10636439409507100470425189 1994332389282581338204723)
                  ·
                    refine ⟨2991498583923872007307085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1994332389282581338204723 2991498583923872007307085)
                    ·
                      refine ⟨1121811968971452002740157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2991498583923872007307085 1121811968971452002740157)
                      ·
                        rfl

theorem cell23_2184721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 4, 1, 3].length) (baseStart_2184721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184721 prefixEnd_2184721 := by exact prefixLift 2184721
  have htrace : WordTrace (prefixWord ++ tailWord_2184721) baseStart_2184721 baseEnd_2184721 := by
    simpa [prefixWord, tailWord_2184721, baseEnd_2184721] using wordTrace_append hprefix tailTrace_2184721
  have hstable : (prefixWord ++ tailWord_2184721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184721).length < 2 ^ (prefixWord ++ tailWord_2184721).sum := by decide
  have hdescent : baseEnd_2184721 < baseStart_2184721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184738 : List Nat := [3, 3, 1, 1, 1, 1, 2, 5, 2, 1, 3]
def baseStart_2184738 : Nat := 118140960795 + 2184738 * 2 ^ 59
def prefixEnd_2184738 : Nat := 4983230072969 + 3 ^ 40 * 2184738 * 2
def baseEnd_2184738 : Nat := 1121820698142578436227579

theorem tailTrace_2184738 : CollatzResearch.WordTrace tailWord_2184738 prefixEnd_2184738 1121820698142578436227579 := by
  unfold tailWord_2184738
  simp only [CollatzResearch.WordTrace]
  refine ⟨19920985289768706097406717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53122627439383216259751245 19920985289768706097406717)
  ·
    refine ⟨7470369483663264786527519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19920985289768706097406717 7470369483663264786527519)
    ·
      refine ⟨11205554225494897179791279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7470369483663264786527519 11205554225494897179791279)
      ·
        refine ⟨16808331338242345769686919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11205554225494897179791279 16808331338242345769686919)
        ·
          refine ⟨25212497007363518654530379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16808331338242345769686919 25212497007363518654530379)
          ·
            refine ⟨37818745511045277981795569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25212497007363518654530379 37818745511045277981795569)
            ·
              refine ⟨28364059133283958486346677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37818745511045277981795569 28364059133283958486346677)
              ·
                refine ⟨2659130543745371108095001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28364059133283958486346677 2659130543745371108095001)
                ·
                  refine ⟨1994347907809028331071251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2659130543745371108095001 1994347907809028331071251)
                  ·
                    refine ⟨2991521861713542496606877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1994347907809028331071251 2991521861713542496606877)
                    ·
                      refine ⟨1121820698142578436227579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2991521861713542496606877 1121820698142578436227579)
                      ·
                        rfl

theorem cell23_2184738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_2184738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184738 prefixEnd_2184738 := by exact prefixLift 2184738
  have htrace : WordTrace (prefixWord ++ tailWord_2184738) baseStart_2184738 baseEnd_2184738 := by
    simpa [prefixWord, tailWord_2184738, baseEnd_2184738] using wordTrace_append hprefix tailTrace_2184738
  have hstable : (prefixWord ++ tailWord_2184738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184738).length < 2 ^ (prefixWord ++ tailWord_2184738).sum := by decide
  have hdescent : baseEnd_2184738 < baseStart_2184738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184778 : List Nat := [3, 1, 2, 1, 1, 3, 1, 3, 4, 2, 2]
def baseStart_2184778 : Nat := 118140960795 + 2184778 * 2 ^ 59
def prefixEnd_2184778 : Nat := 4983230072969 + 3 ^ 40 * 2184778 * 2
def baseEnd_2184778 : Nat := 1121841237368758279727395

theorem tailTrace_2184778 : CollatzResearch.WordTrace tailWord_2184778 prefixEnd_2184778 1121841237368758279727395 := by
  unfold tailWord_2184778
  simp only [CollatzResearch.WordTrace]
  refine ⟨19921350019732477805270747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53123600052619940814055325 19921350019732477805270747)
  ·
    refine ⟨29882025029598716707906121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19921350019732477805270747 29882025029598716707906121)
    ·
      refine ⟨22411518772199037530929591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29882025029598716707906121 22411518772199037530929591)
      ·
        refine ⟨33617278158298556296394387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22411518772199037530929591 33617278158298556296394387)
        ·
          refine ⟨50425917237447834444591581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33617278158298556296394387 50425917237447834444591581)
          ·
            refine ⟨18909718964042937916721843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50425917237447834444591581 18909718964042937916721843)
            ·
              refine ⟨28364578446064406875082765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18909718964042937916721843 28364578446064406875082765)
              ·
                refine ⟨10636716917274152578156037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28364578446064406875082765 10636716917274152578156037)
                ·
                  refine ⟨1994384421988903608404257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10636716917274152578156037 1994384421988903608404257)
                  ·
                    refine ⟨1495788316491677706303193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1994384421988903608404257 1495788316491677706303193)
                    ·
                      refine ⟨1121841237368758279727395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1495788316491677706303193 1121841237368758279727395)
                      ·
                        rfl

theorem cell23_2184778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 4, 2, 2].length) (baseStart_2184778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184778 prefixEnd_2184778 := by exact prefixLift 2184778
  have htrace : WordTrace (prefixWord ++ tailWord_2184778) baseStart_2184778 baseEnd_2184778 := by
    simpa [prefixWord, tailWord_2184778, baseEnd_2184778] using wordTrace_append hprefix tailTrace_2184778
  have hstable : (prefixWord ++ tailWord_2184778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184778).length < 2 ^ (prefixWord ++ tailWord_2184778).sum := by decide
  have hdescent : baseEnd_2184778 < baseStart_2184778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184868 : List Nat := [2, 3, 1, 2, 2, 2, 3, 1, 2, 1, 4]
def baseStart_2184868 : Nat := 118140960795 + 2184868 * 2 ^ 59
def prefixEnd_2184868 : Nat := 4983230072969 + 3 ^ 40 * 2184868 * 2
def baseEnd_2184868 : Nat := 1121887450627662927601981

theorem tailTrace_2184868 : CollatzResearch.WordTrace tailWord_2184868 prefixEnd_2184868 1121887450627662927601981 := by
  unfold tailWord_2184868
  simp only [CollatzResearch.WordTrace]
  refine ⟨39844341324301928295929629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53125788432402571061239505 39844341324301928295929629)
  ·
    refine ⟨14941627996613223110973611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39844341324301928295929629 14941627996613223110973611)
    ·
      refine ⟨22412441994919834666460417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14941627996613223110973611 22412441994919834666460417)
      ·
        refine ⟨16809331496189875999845313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22412441994919834666460417 16809331496189875999845313)
        ·
          refine ⟨12606998622142406999883985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16809331496189875999845313 12606998622142406999883985)
          ·
            refine ⟨9455248966606805249912989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12606998622142406999883985 9455248966606805249912989)
            ·
              refine ⟨3545718362477551968717371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9455248966606805249912989 3545718362477551968717371)
              ·
                refine ⟨5318577543716327953076057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3545718362477551968717371 5318577543716327953076057)
                ·
                  refine ⟨3988933157787245964807043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5318577543716327953076057 3988933157787245964807043)
                  ·
                    refine ⟨5983399736680868947210565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3988933157787245964807043 5983399736680868947210565)
                    ·
                      refine ⟨1121887450627662927601981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5983399736680868947210565 1121887450627662927601981)
                      ·
                        rfl

theorem cell23_2184868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_2184868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184868 prefixEnd_2184868 := by exact prefixLift 2184868
  have htrace : WordTrace (prefixWord ++ tailWord_2184868) baseStart_2184868 baseEnd_2184868 := by
    simpa [prefixWord, tailWord_2184868, baseEnd_2184868] using wordTrace_append hprefix tailTrace_2184868
  have hstable : (prefixWord ++ tailWord_2184868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184868).length < 2 ^ (prefixWord ++ tailWord_2184868).sum := by decide
  have hdescent : baseEnd_2184868 < baseStart_2184868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184928 : List Nat := [2, 1, 1, 3, 1, 2, 4, 1, 1, 5, 2]
def baseStart_2184928 : Nat := 118140960795 + 2184928 * 2 ^ 59
def prefixEnd_2184928 : Nat := 4983230072969 + 3 ^ 40 * 2184928 * 2
def baseEnd_2184928 : Nat := 1121918259466932692851705

theorem tailTrace_2184928 : CollatzResearch.WordTrace tailWord_2184928 prefixEnd_2184928 1121918259466932692851705 := by
  unfold tailWord_2184928
  simp only [CollatzResearch.WordTrace]
  refine ⟨39845435514193243419521719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53127247352257657892695625 39845435514193243419521719)
  ·
    refine ⟨59768153271289865129282579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39845435514193243419521719 59768153271289865129282579)
    ·
      refine ⟨89652229906934797693923869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59768153271289865129282579 89652229906934797693923869)
      ·
        refine ⟨33619586215100549135221451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89652229906934797693923869 33619586215100549135221451)
        ·
          refine ⟨50429379322650823702832177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33619586215100549135221451 50429379322650823702832177)
          ·
            refine ⟨37822034491988117777124133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50429379322650823702832177 37822034491988117777124133)
            ·
              refine ⟨7091631467247772083210775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37822034491988117777124133 7091631467247772083210775)
              ·
                refine ⟨10637447200871658124816163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7091631467247772083210775 10637447200871658124816163)
                ·
                  refine ⟨15956170801307487187224245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10637447200871658124816163 15956170801307487187224245)
                  ·
                    refine ⟨1495891012622576923802273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15956170801307487187224245 1495891012622576923802273)
                    ·
                      refine ⟨1121918259466932692851705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1495891012622576923802273 1121918259466932692851705)
                      ·
                        rfl

theorem cell23_2184928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 1, 5, 2].length) (baseStart_2184928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184928 prefixEnd_2184928 := by exact prefixLift 2184928
  have htrace : WordTrace (prefixWord ++ tailWord_2184928) baseStart_2184928 baseEnd_2184928 := by
    simpa [prefixWord, tailWord_2184928, baseEnd_2184928] using wordTrace_append hprefix tailTrace_2184928
  have hstable : (prefixWord ++ tailWord_2184928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184928).length < 2 ^ (prefixWord ++ tailWord_2184928).sum := by decide
  have hdescent : baseEnd_2184928 < baseStart_2184928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184929 : List Nat := [1, 2, 3, 1, 6, 1, 1, 3, 1, 4]
def baseStart_2184929 : Nat := 118140960795 + 2184929 * 2 ^ 59
def prefixEnd_2184929 : Nat := 4983230072969 + 3 ^ 40 * 2184929 * 2
def baseEnd_2184929 : Nat := 373972924315862396313067

theorem tailTrace_2184929 : CollatzResearch.WordTrace tailWord_2184929 prefixEnd_2184929 373972924315862396313067 := by
  unfold tailWord_2184929
  simp only [CollatzResearch.WordTrace]
  refine ⟨79690907501382864009829841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53127271667588576006553227 79690907501382864009829841)
  ·
    refine ⟨59768180626037148007372381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79690907501382864009829841 59768180626037148007372381)
    ·
      refine ⟨22413067734763930502764643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59768180626037148007372381 22413067734763930502764643)
      ·
        refine ⟨33619601602145895754146965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22413067734763930502764643 33619601602145895754146965)
        ·
          refine ⟨1575918825100588863475639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33619601602145895754146965 1575918825100588863475639)
          ·
            refine ⟨2363878237650883295213459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1575918825100588863475639 2363878237650883295213459)
            ·
              refine ⟨3545817356476324942820189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2363878237650883295213459 3545817356476324942820189)
              ·
                refine ⟨1329681508678621853557571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3545817356476324942820189 1329681508678621853557571)
                ·
                  refine ⟨1994522263017932780336357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1329681508678621853557571 1994522263017932780336357)
                  ·
                    refine ⟨373972924315862396313067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1994522263017932780336357 373972924315862396313067)
                    ·
                      rfl

theorem cell23_2184929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_2184929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184929 prefixEnd_2184929 := by exact prefixLift 2184929
  have htrace : WordTrace (prefixWord ++ tailWord_2184929) baseStart_2184929 baseEnd_2184929 := by
    simpa [prefixWord, tailWord_2184929, baseEnd_2184929] using wordTrace_append hprefix tailTrace_2184929
  have hstable : (prefixWord ++ tailWord_2184929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184929).length < 2 ^ (prefixWord ++ tailWord_2184929).sum := by decide
  have hdescent : baseEnd_2184929 < baseStart_2184929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184938 : List Nat := [3, 1, 3, 1, 1, 1, 4, 3, 1, 5]
def baseStart_2184938 : Nat := 118140960795 + 2184938 * 2 ^ 59
def prefixEnd_2184938 : Nat := 4983230072969 + 3 ^ 40 * 2184938 * 2
def baseEnd_2184938 : Nat := 373974464757825884575553

theorem tailTrace_2184938 : CollatzResearch.WordTrace tailWord_2184938 prefixEnd_2184938 373974464757825884575553 := by
  unfold tailWord_2184938
  simp only [CollatzResearch.WordTrace]
  refine ⟨19922808939587564636726867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53127490505566839031271645 19922808939587564636726867)
  ·
    refine ⟨29884213409381346955090301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19922808939587564636726867 29884213409381346955090301)
    ·
      refine ⟨11206580028518005108158863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29884213409381346955090301 11206580028518005108158863)
      ·
        refine ⟨16809870042777007662238295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11206580028518005108158863 16809870042777007662238295)
        ·
          refine ⟨25214805064165511493357443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16809870042777007662238295 25214805064165511493357443)
          ·
            refine ⟨37822207596248267240036165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25214805064165511493357443 37822207596248267240036165)
            ·
              refine ⟨7091663924296550107506781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37822207596248267240036165 7091663924296550107506781)
              ·
                refine ⟨2659373971611206290315043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7091663924296550107506781 2659373971611206290315043)
                ·
                  refine ⟨3989060957416809435472565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2659373971611206290315043 3989060957416809435472565)
                  ·
                    refine ⟨373974464757825884575553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3989060957416809435472565 373974464757825884575553)
                    ·
                      rfl

theorem cell23_2184938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_2184938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184938 prefixEnd_2184938 := by exact prefixLift 2184938
  have htrace : WordTrace (prefixWord ++ tailWord_2184938) baseStart_2184938 baseEnd_2184938 := by
    simpa [prefixWord, tailWord_2184938, baseEnd_2184938] using wordTrace_append hprefix tailTrace_2184938
  have hstable : (prefixWord ++ tailWord_2184938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184938).length < 2 ^ (prefixWord ++ tailWord_2184938).sum := by decide
  have hdescent : baseEnd_2184938 < baseStart_2184938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184945 : List Nat := [1, 2, 2, 2, 2, 4, 1, 2, 2, 3, 2]
def baseStart_2184945 : Nat := 118140960795 + 2184945 * 2 ^ 59
def prefixEnd_2184945 : Nat := 4983230072969 + 3 ^ 40 * 2184945 * 2
def baseEnd_2184945 : Nat := 1121926988638059126339127

theorem tailTrace_2184945 : CollatzResearch.WordTrace tailWord_2184945 prefixEnd_2184945 1121926988638059126339127 := by
  unfold tailWord_2184945
  simp only [CollatzResearch.WordTrace]
  refine ⟨79691491069324898742412289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53127660712883265828274859 79691491069324898742412289)
  ·
    refine ⟨59768618301993674056809217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79691491069324898742412289 59768618301993674056809217)
    ·
      refine ⟨44826463726495255542606913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59768618301993674056809217 44826463726495255542606913)
      ·
        refine ⟨33619847794871441656955185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44826463726495255542606913 33619847794871441656955185)
        ·
          refine ⟨25214885846153581242716389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33619847794871441656955185 25214885846153581242716389)
          ·
            refine ⟨4727791096153796483009323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25214885846153581242716389 4727791096153796483009323)
            ·
              refine ⟨7091686644230694724513985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4727791096153796483009323 7091686644230694724513985)
              ·
                refine ⟨5318764983173021043385489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7091686644230694724513985 5318764983173021043385489)
                ·
                  refine ⟨3989073737379765782539117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5318764983173021043385489 3989073737379765782539117)
                  ·
                    refine ⟨1495902651517412168452169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3989073737379765782539117 1495902651517412168452169)
                    ·
                      refine ⟨1121926988638059126339127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1495902651517412168452169 1121926988638059126339127)
                      ·
                        rfl

theorem cell23_2184945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 2, 3, 2].length) (baseStart_2184945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184945 prefixEnd_2184945 := by exact prefixLift 2184945
  have htrace : WordTrace (prefixWord ++ tailWord_2184945) baseStart_2184945 baseEnd_2184945 := by
    simpa [prefixWord, tailWord_2184945, baseEnd_2184945] using wordTrace_append hprefix tailTrace_2184945
  have hstable : (prefixWord ++ tailWord_2184945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184945).length < 2 ^ (prefixWord ++ tailWord_2184945).sum := by decide
  have hdescent : baseEnd_2184945 < baseStart_2184945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184971 : List Nat := [1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 6]
def baseStart_2184971 : Nat := 118140960795 + 2184971 * 2 ^ 59
def prefixEnd_2184971 : Nat := 4983230072969 + 3 ^ 40 * 2184971 * 2
def baseEnd_2184971 : Nat := 1121940339135076024614007

theorem tailTrace_2184971 : CollatzResearch.WordTrace tailWord_2184971 prefixEnd_2184971 1121940339135076024614007 := by
  unfold tailWord_2184971
  simp only [CollatzResearch.WordTrace]
  refine ⟨79692439367230705182858767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53128292911487136788572511 79692439367230705182858767)
  ·
    refine ⟨119538659050846057774288151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79692439367230705182858767 119538659050846057774288151)
    ·
      refine ⟨179307988576269086661432227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119538659050846057774288151 179307988576269086661432227)
      ·
        refine ⟨268961982864403629992148341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179307988576269086661432227 268961982864403629992148341)
        ·
          refine ⟨25215185893537840311763907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 268961982864403629992148341 25215185893537840311763907)
          ·
            refine ⟨37822778840306760467645861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25215185893537840311763907 37822778840306760467645861)
            ·
              refine ⟨7091771032557517587683599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37822778840306760467645861 7091771032557517587683599)
              ·
                refine ⟨10637656548836276381525399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7091771032557517587683599 10637656548836276381525399)
                ·
                  refine ⟨15956484823254414572288099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10637656548836276381525399 15956484823254414572288099)
                  ·
                    refine ⟨23934727234881621858432149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15956484823254414572288099 23934727234881621858432149)
                    ·
                      refine ⟨1121940339135076024614007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23934727234881621858432149 1121940339135076024614007)
                      ·
                        rfl

theorem cell23_2184971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 6].length) (baseStart_2184971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184971 prefixEnd_2184971 := by exact prefixLift 2184971
  have htrace : WordTrace (prefixWord ++ tailWord_2184971) baseStart_2184971 baseEnd_2184971 := by
    simpa [prefixWord, tailWord_2184971, baseEnd_2184971] using wordTrace_append hprefix tailTrace_2184971
  have hstable : (prefixWord ++ tailWord_2184971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184971).length < 2 ^ (prefixWord ++ tailWord_2184971).sum := by decide
  have hdescent : baseEnd_2184971 < baseStart_2184971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184981 : List Nat := [1, 3, 2, 1, 2, 3, 2, 9]
def baseStart_2184981 : Nat := 118140960795 + 2184981 * 2 ^ 59
def prefixEnd_2184981 : Nat := 4983230072969 + 3 ^ 40 * 2184981 * 2
def baseEnd_2184981 : Nat := 41553536071911888351443

theorem tailTrace_2184981 : CollatzResearch.WordTrace tailWord_2184981 prefixEnd_2184981 41553536071911888351443 := by
  unfold tailWord_2184981
  simp only [CollatzResearch.WordTrace]
  refine ⟨79692804097194476890722797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53128536064796317927148531 79692804097194476890722797)
  ·
    refine ⟨29884801536447928834021049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79692804097194476890722797 29884801536447928834021049)
    ·
      refine ⟨22413601152335946625515787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29884801536447928834021049 22413601152335946625515787)
      ·
        refine ⟨33620401728503919938273681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22413601152335946625515787 33620401728503919938273681)
        ·
          refine ⟨25215301296377939953705261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33620401728503919938273681 25215301296377939953705261)
          ·
            refine ⟨9455737986141727482639473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25215301296377939953705261 9455737986141727482639473)
            ·
              refine ⟨7091803489606295611979605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9455737986141727482639473 7091803489606295611979605)
              ·
                refine ⟨41553536071911888351443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7091803489606295611979605 41553536071911888351443)
                ·
                  rfl

theorem cell23_2184981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 9].length) (baseStart_2184981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184981 prefixEnd_2184981 := by exact prefixLift 2184981
  have htrace : WordTrace (prefixWord ++ tailWord_2184981) baseStart_2184981 baseEnd_2184981 := by
    simpa [prefixWord, tailWord_2184981, baseEnd_2184981] using wordTrace_append hprefix tailTrace_2184981
  have hstable : (prefixWord ++ tailWord_2184981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184981).length < 2 ^ (prefixWord ++ tailWord_2184981).sum := by decide
  have hdescent : baseEnd_2184981 < baseStart_2184981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2184988 : List Nat := [2, 2, 3, 1, 1, 2, 3, 2, 1, 2, 4]
def baseStart_2184988 : Nat := 118140960795 + 2184988 * 2 ^ 59
def prefixEnd_2184988 : Nat := 4983230072969 + 3 ^ 40 * 2184988 * 2
def baseEnd_2184988 : Nat := 1121949068306202458101429

theorem tailTrace_2184988 : CollatzResearch.WordTrace tailWord_2184988 prefixEnd_2184988 1121949068306202458101429 := by
  unfold tailWord_2184988
  simp only [CollatzResearch.WordTrace]
  refine ⟨39846529704084558543113809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53128706272112744724151745 39846529704084558543113809)
  ·
    refine ⟨29884897278063418907335357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39846529704084558543113809 29884897278063418907335357)
    ·
      refine ⟨11206836479273782090250759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29884897278063418907335357 11206836479273782090250759)
      ·
        refine ⟨16810254718910673135376139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11206836479273782090250759 16810254718910673135376139)
        ·
          refine ⟨25215382078366009703064209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16810254718910673135376139 25215382078366009703064209)
          ·
            refine ⟨18911536558774507277298157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25215382078366009703064209 18911536558774507277298157)
            ·
              refine ⟨7091826209540440228986809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18911536558774507277298157 7091826209540440228986809)
              ·
                refine ⟨5318869657155330171740107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7091826209540440228986809 5318869657155330171740107)
                ·
                  refine ⟨7978304485732995257610161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5318869657155330171740107 7978304485732995257610161)
                  ·
                    refine ⟨5983728364299746443207621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7978304485732995257610161 5983728364299746443207621)
                    ·
                      refine ⟨1121949068306202458101429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5983728364299746443207621 1121949068306202458101429)
                      ·
                        rfl

theorem cell23_2184988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_2184988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2184988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2184988 prefixEnd_2184988 := by exact prefixLift 2184988
  have htrace : WordTrace (prefixWord ++ tailWord_2184988) baseStart_2184988 baseEnd_2184988 := by
    simpa [prefixWord, tailWord_2184988, baseEnd_2184988] using wordTrace_append hprefix tailTrace_2184988
  have hstable : (prefixWord ++ tailWord_2184988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2184988).length < 2 ^ (prefixWord ++ tailWord_2184988).sum := by decide
  have hdescent : baseEnd_2184988 < baseStart_2184988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2184988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185009 : List Nat := [1, 2, 2, 3, 2, 3, 1, 4, 1, 2, 2]
def baseStart_2185009 : Nat := 118140960795 + 2185009 * 2 ^ 59
def prefixEnd_2185009 : Nat := 4983230072969 + 3 ^ 40 * 2185009 * 2
def baseEnd_2185009 : Nat := 1121959851399946875938833

theorem tailTrace_2185009 : CollatzResearch.WordTrace tailWord_2185009 prefixEnd_2185009 1121959851399946875938833 := by
  unfold tailWord_2185009
  simp only [CollatzResearch.WordTrace]
  refine ⟨79693825341093037672742081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53129216894062025115161387 79693825341093037672742081)
  ·
    refine ⟨59770369005819778254556561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79693825341093037672742081 59770369005819778254556561)
    ·
      refine ⟨44827776754364833690917421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59770369005819778254556561 44827776754364833690917421)
      ·
        refine ⟨16810416282886812634094033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44827776754364833690917421 16810416282886812634094033)
        ·
          refine ⟨12607812212165109475570525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16810416282886812634094033 12607812212165109475570525)
          ·
            refine ⟨4727929579561916053338947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12607812212165109475570525 4727929579561916053338947)
            ·
              refine ⟨7091894369342874080008421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4727929579561916053338947 7091894369342874080008421)
              ·
                refine ⟨1329730194251788890001579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7091894369342874080008421 1329730194251788890001579)
                ·
                  refine ⟨1994595291377683335002369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1329730194251788890001579 1994595291377683335002369)
                  ·
                    refine ⟨1495946468533262501251777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1994595291377683335002369 1495946468533262501251777)
                    ·
                      refine ⟨1121959851399946875938833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1495946468533262501251777 1121959851399946875938833)
                      ·
                        rfl

theorem cell23_2185009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_2185009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185009 prefixEnd_2185009 := by exact prefixLift 2185009
  have htrace : WordTrace (prefixWord ++ tailWord_2185009) baseStart_2185009 baseEnd_2185009 := by
    simpa [prefixWord, tailWord_2185009, baseEnd_2185009] using wordTrace_append hprefix tailTrace_2185009
  have hstable : (prefixWord ++ tailWord_2185009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185009).length < 2 ^ (prefixWord ++ tailWord_2185009).sum := by decide
  have hdescent : baseEnd_2185009 < baseStart_2185009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185059 : List Nat := [1, 1, 1, 5, 4, 2, 1, 2, 2, 1, 3]
def baseStart_2185059 : Nat := 118140960795 + 2185059 * 2 ^ 59
def prefixEnd_2185059 : Nat := 4983230072969 + 3 ^ 40 * 2185059 * 2
def baseEnd_2185059 : Nat := 1121985525432671680313603

theorem tailTrace_2185059 : CollatzResearch.WordTrace tailWord_2185059 prefixEnd_2185059 1121985525432671680313603 := by
  unfold tailWord_2185059
  simp only [CollatzResearch.WordTrace]
  refine ⟨79695648990911896212062231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53130432660607930808041487 79695648990911896212062231)
  ·
    refine ⟨119543473486367844318093347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79695648990911896212062231 119543473486367844318093347)
    ·
      refine ⟨179315210229551766477140021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119543473486367844318093347 179315210229551766477140021)
      ·
        refine ⟨16810800959020478107231877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 179315210229551766477140021 16810800959020478107231877)
        ·
          refine ⟨3152025179816339645105977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16810800959020478107231877 3152025179816339645105977)
          ·
            refine ⟨2364018884862254733829483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3152025179816339645105977 2364018884862254733829483)
            ·
              refine ⟨3546028327293382100744225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2364018884862254733829483 3546028327293382100744225)
              ·
                refine ⟨2659521245470036575558169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3546028327293382100744225 2659521245470036575558169)
                ·
                  refine ⟨1994640934102527431668627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2659521245470036575558169 1994640934102527431668627)
                  ·
                    refine ⟨2991961401153791147502941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1994640934102527431668627 2991961401153791147502941)
                    ·
                      refine ⟨1121985525432671680313603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2991961401153791147502941 1121985525432671680313603)
                      ·
                        rfl

theorem cell23_2185059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_2185059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185059 prefixEnd_2185059 := by exact prefixLift 2185059
  have htrace : WordTrace (prefixWord ++ tailWord_2185059) baseStart_2185059 baseEnd_2185059 := by
    simpa [prefixWord, tailWord_2185059, baseEnd_2185059] using wordTrace_append hprefix tailTrace_2185059
  have hstable : (prefixWord ++ tailWord_2185059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185059).length < 2 ^ (prefixWord ++ tailWord_2185059).sum := by decide
  have hdescent : baseEnd_2185059 < baseStart_2185059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185082 : List Nat := [3, 1, 1, 1, 1, 1, 4, 5, 2, 2, 2]
def baseStart_2185082 : Nat := 118140960795 + 2185082 * 2 ^ 59
def prefixEnd_2185082 : Nat := 4983230072969 + 3 ^ 40 * 2185082 * 2
def baseEnd_2185082 : Nat := 1121997335487725090325997

theorem tailTrace_2185082 : CollatzResearch.WordTrace tailWord_2185082 prefixEnd_2185082 1121997335487725090325997 := by
  unfold tailWord_2185082
  simp only [CollatzResearch.WordTrace]
  refine ⟨19924121967457142785037375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53130991913219047426766333 19924121967457142785037375)
  ·
    refine ⟨29886182951185714177556063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19924121967457142785037375 29886182951185714177556063)
    ·
      refine ⟨44829274426778571266334095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29886182951185714177556063 44829274426778571266334095)
      ·
        refine ⟨67243911640167856899501143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44829274426778571266334095 67243911640167856899501143)
        ·
          refine ⟨100865867460251785349251715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67243911640167856899501143 100865867460251785349251715)
          ·
            refine ⟨151298801190377678023877573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100865867460251785349251715 151298801190377678023877573)
            ·
              refine ⟨28368525223195814629477045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 151298801190377678023877573 28368525223195814629477045)
              ·
                refine ⟨2659549239674607621513473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28368525223195814629477045 2659549239674607621513473)
                ·
                  refine ⟨1994661929755955716135105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2659549239674607621513473 1994661929755955716135105)
                  ·
                    refine ⟨1495996447316966787101329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1994661929755955716135105 1495996447316966787101329)
                    ·
                      refine ⟨1121997335487725090325997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1495996447316966787101329 1121997335487725090325997)
                      ·
                        rfl

theorem cell23_2185082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 2, 2, 2].length) (baseStart_2185082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185082 prefixEnd_2185082 := by exact prefixLift 2185082
  have htrace : WordTrace (prefixWord ++ tailWord_2185082) baseStart_2185082 baseEnd_2185082 := by
    simpa [prefixWord, tailWord_2185082, baseEnd_2185082] using wordTrace_append hprefix tailTrace_2185082
  have hstable : (prefixWord ++ tailWord_2185082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185082).length < 2 ^ (prefixWord ++ tailWord_2185082).sum := by decide
  have hdescent : baseEnd_2185082 < baseStart_2185082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185086 : List Nat := [4, 2, 3, 1, 1, 2, 2, 2, 1, 3, 2]
def baseStart_2185086 : Nat := 118140960795 + 2185086 * 2 ^ 59
def prefixEnd_2185086 : Nat := 4983230072969 + 3 ^ 40 * 2185086 * 2
def baseEnd_2185086 : Nat := 1121999389410343074675979

theorem tailTrace_2185086 : CollatzResearch.WordTrace tailWord_2185086 prefixEnd_2185086 1121999389410343074675979 := by
  unfold tailWord_2185086
  simp only [CollatzResearch.WordTrace]
  refine ⟨9962079220226759977911889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53131089174542719882196741 9962079220226759977911889)
  ·
    refine ⟨7471559415170069983433917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9962079220226759977911889 7471559415170069983433917)
    ·
      refine ⟨2801834780688776243787719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7471559415170069983433917 2801834780688776243787719)
      ·
        refine ⟨4202752171033164365681579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2801834780688776243787719 4202752171033164365681579)
        ·
          refine ⟨6304128256549746548522369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4202752171033164365681579 6304128256549746548522369)
          ·
            refine ⟨4728096192412309911391777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6304128256549746548522369 4728096192412309911391777)
            ·
              refine ⟨3546072144309232433543833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4728096192412309911391777 3546072144309232433543833)
              ·
                refine ⟨2659554108231924325157875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3546072144309232433543833 2659554108231924325157875)
                ·
                  refine ⟨3989331162347886487736813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2659554108231924325157875 3989331162347886487736813)
                  ·
                    refine ⟨1495999185880457432901305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3989331162347886487736813 1495999185880457432901305)
                    ·
                      refine ⟨1121999389410343074675979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1495999185880457432901305 1121999389410343074675979)
                      ·
                        rfl

theorem cell23_2185086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_2185086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185086 prefixEnd_2185086 := by exact prefixLift 2185086
  have htrace : WordTrace (prefixWord ++ tailWord_2185086) baseStart_2185086 baseEnd_2185086 := by
    simpa [prefixWord, tailWord_2185086, baseEnd_2185086] using wordTrace_append hprefix tailTrace_2185086
  have hstable : (prefixWord ++ tailWord_2185086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185086).length < 2 ^ (prefixWord ++ tailWord_2185086).sum := by decide
  have hdescent : baseEnd_2185086 < baseStart_2185086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185102 : List Nat := [4, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5]
def baseStart_2185102 : Nat := 118140960795 + 2185102 * 2 ^ 59
def prefixEnd_2185102 : Nat := 4983230072969 + 3 ^ 40 * 2185102 * 2
def baseEnd_2185102 : Nat := 1122007605100815012075905

theorem tailTrace_2185102 : CollatzResearch.WordTrace tailWord_2185102 prefixEnd_2185102 1122007605100815012075905 := by
  unfold tailWord_2185102
  simp only [CollatzResearch.WordTrace]
  refine ⟨9962152166219514319484695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53131478219837409703918373 9962152166219514319484695)
  ·
    refine ⟨14943228249329271479227043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9962152166219514319484695 14943228249329271479227043)
    ·
      refine ⟨22414842373993907218840565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14943228249329271479227043 22414842373993907218840565)
      ·
        refine ⟨2101391472561928801766303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22414842373993907218840565 2101391472561928801766303)
        ·
          refine ⟨3152087208842893202649455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2101391472561928801766303 3152087208842893202649455)
          ·
            refine ⟨4728130813264339803974183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3152087208842893202649455 4728130813264339803974183)
            ·
              refine ⟨7092196219896509705961275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4728130813264339803974183 7092196219896509705961275)
              ·
                refine ⟨10638294329844764558941913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7092196219896509705961275 10638294329844764558941913)
                ·
                  refine ⟨7978720747383573419206435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10638294329844764558941913 7978720747383573419206435)
                  ·
                    refine ⟨11968081121075360128809653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7978720747383573419206435 11968081121075360128809653)
                    ·
                      refine ⟨1122007605100815012075905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11968081121075360128809653 1122007605100815012075905)
                      ·
                        rfl

theorem cell23_2185102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_2185102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185102 prefixEnd_2185102 := by exact prefixLift 2185102
  have htrace : WordTrace (prefixWord ++ tailWord_2185102) baseStart_2185102 baseEnd_2185102 := by
    simpa [prefixWord, tailWord_2185102, baseEnd_2185102] using wordTrace_append hprefix tailTrace_2185102
  have hstable : (prefixWord ++ tailWord_2185102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185102).length < 2 ^ (prefixWord ++ tailWord_2185102).sum := by decide
  have hdescent : baseEnd_2185102 < baseStart_2185102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185105 : List Nat := [1, 2, 2, 1, 1, 1, 7, 3, 5]
def baseStart_2185105 : Nat := 118140960795 + 2185105 * 2 ^ 59
def prefixEnd_2185105 : Nat := 4983230072969 + 3 ^ 40 * 2185105 * 2
def baseEnd_2185105 : Nat := 124667682838086500037599

theorem tailTrace_2185105 : CollatzResearch.WordTrace tailWord_2185105 prefixEnd_2185105 124667682838086500037599 := by
  unfold tailWord_2185105
  simp only [CollatzResearch.WordTrace]
  refine ⟨79697326748745246068236769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53131551165830164045491179 79697326748745246068236769)
  ·
    refine ⟨59772995061558934551177577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79697326748745246068236769 59772995061558934551177577)
    ·
      refine ⟨44829746296169200913383183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59772995061558934551177577 44829746296169200913383183)
      ·
        refine ⟨67244619444253801370074775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44829746296169200913383183 67244619444253801370074775)
        ·
          refine ⟨100866929166380702055112163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67244619444253801370074775 100866929166380702055112163)
          ·
            refine ⟨151300393749571053082668245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100866929166380702055112163 151300393749571053082668245)
            ·
              refine ⟨3546102978505571556625037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 151300393749571053082668245 3546102978505571556625037)
              ·
                refine ⟨1329788616939589333734389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3546102978505571556625037 1329788616939589333734389)
                ·
                  refine ⟨124667682838086500037599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1329788616939589333734389 124667682838086500037599)
                  ·
                    rfl

theorem cell23_2185105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 3, 5].length) (baseStart_2185105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185105 prefixEnd_2185105 := by exact prefixLift 2185105
  have htrace : WordTrace (prefixWord ++ tailWord_2185105) baseStart_2185105 baseEnd_2185105 := by
    simpa [prefixWord, tailWord_2185105, baseEnd_2185105] using wordTrace_append hprefix tailTrace_2185105
  have hstable : (prefixWord ++ tailWord_2185105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185105).length < 2 ^ (prefixWord ++ tailWord_2185105).sum := by decide
  have hdescent : baseEnd_2185105 < baseStart_2185105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185122 : List Nat := [3, 3, 1, 2, 3, 2, 1, 1, 7]
def baseStart_2185122 : Nat := 118140960795 + 2185122 * 2 ^ 59
def prefixEnd_2185122 : Nat := 4983230072969 + 3 ^ 40 * 2185122 * 2
def baseEnd_2185122 : Nat := 124668652745989437091757

theorem tailTrace_2185122 : CollatzResearch.WordTrace tailWord_2185122 prefixEnd_2185122 124668652745989437091757 := by
  unfold tailWord_2185122
  simp only [CollatzResearch.WordTrace]
  refine ⟨19924486697420914492901405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53131964526455771981070413 19924486697420914492901405)
  ·
    refine ⟨7471682511532842934838027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19924486697420914492901405 7471682511532842934838027)
    ·
      refine ⟨11207523767299264402257041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7471682511532842934838027 11207523767299264402257041)
      ·
        refine ⟨8405642825474448301692781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11207523767299264402257041 8405642825474448301692781)
        ·
          refine ⟨3152116059552918113134793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8405642825474448301692781 3152116059552918113134793)
          ·
            refine ⟨2364087044664688584851095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3152116059552918113134793 2364087044664688584851095)
            ·
              refine ⟨3546130566997032877276643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2364087044664688584851095 3546130566997032877276643)
              ·
                refine ⟨5319195850495549315914965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3546130566997032877276643 5319195850495549315914965)
                ·
                  refine ⟨124668652745989437091757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5319195850495549315914965 124668652745989437091757)
                  ·
                    rfl

theorem cell23_2185122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_2185122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185122 prefixEnd_2185122 := by exact prefixLift 2185122
  have htrace : WordTrace (prefixWord ++ tailWord_2185122) baseStart_2185122 baseEnd_2185122 := by
    simpa [prefixWord, tailWord_2185122, baseEnd_2185122] using wordTrace_append hprefix tailTrace_2185122
  have hstable : (prefixWord ++ tailWord_2185122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185122).length < 2 ^ (prefixWord ++ tailWord_2185122).sum := by decide
  have hdescent : baseEnd_2185122 < baseStart_2185122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185138 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4]
def baseStart_2185138 : Nat := 118140960795 + 2185138 * 2 ^ 59
def prefixEnd_2185138 : Nat := 4983230072969 + 3 ^ 40 * 2185138 * 2
def baseEnd_2185138 : Nat := 1122026090404376871225739

theorem tailTrace_2185138 : CollatzResearch.WordTrace tailWord_2185138 prefixEnd_2185138 1122026090404376871225739 := by
  unfold tailWord_2185138
  simp only [CollatzResearch.WordTrace]
  refine ⟨19924632589406423176047017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53132353571750461802792045 19924632589406423176047017)
  ·
    refine ⟨14943474442054817382035263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19924632589406423176047017 14943474442054817382035263)
    ·
      refine ⟨22415211663082226073052895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14943474442054817382035263 22415211663082226073052895)
      ·
        refine ⟨33622817494623339109579343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22415211663082226073052895 33622817494623339109579343)
        ·
          refine ⟨50434226241935008664369015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33622817494623339109579343 50434226241935008664369015)
          ·
            refine ⟨75651339362902512996553523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50434226241935008664369015 75651339362902512996553523)
            ·
              refine ⟨113477009044353769494830285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75651339362902512996553523 113477009044353769494830285)
              ·
                refine ⟨42553878391632663560561357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113477009044353769494830285 42553878391632663560561357)
                ·
                  refine ⟨15957704396862248835210509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42553878391632663560561357 15957704396862248835210509)
                  ·
                    refine ⟨5984139148823343313203941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15957704396862248835210509 5984139148823343313203941)
                    ·
                      refine ⟨1122026090404376871225739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5984139148823343313203941 1122026090404376871225739)
                      ·
                        rfl

theorem cell23_2185138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_2185138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185138 prefixEnd_2185138 := by exact prefixLift 2185138
  have htrace : WordTrace (prefixWord ++ tailWord_2185138) baseStart_2185138 baseEnd_2185138 := by
    simpa [prefixWord, tailWord_2185138, baseEnd_2185138] using wordTrace_append hprefix tailTrace_2185138
  have hstable : (prefixWord ++ tailWord_2185138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185138).length < 2 ^ (prefixWord ++ tailWord_2185138).sum := by decide
  have hdescent : baseEnd_2185138 < baseStart_2185138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185172 : List Nat := [2, 4, 1, 2, 1, 1, 2, 2, 2, 4, 2]
def baseStart_2185172 : Nat := 118140960795 + 2185172 * 2 ^ 59
def prefixEnd_2185172 : Nat := 4983230072969 + 3 ^ 40 * 2185172 * 2
def baseEnd_2185172 : Nat := 1122043548746629738200583

theorem tailTrace_2185172 : CollatzResearch.WordTrace tailWord_2185172 prefixEnd_2185172 1122043548746629738200583 := by
  unfold tailWord_2185172
  simp only [CollatzResearch.WordTrace]
  refine ⟨39849885219751258255462885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53133180293001677673950513 39849885219751258255462885)
  ·
    refine ⟨7471853478703360922899291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39849885219751258255462885 7471853478703360922899291)
    ·
      refine ⟨11207780218055041384348937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7471853478703360922899291 11207780218055041384348937)
      ·
        refine ⟨8405835163541281038261703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11207780218055041384348937 8405835163541281038261703)
        ·
          refine ⟨12608752745311921557392555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8405835163541281038261703 12608752745311921557392555)
          ·
            refine ⟨18913129117967882336088833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12608752745311921557392555 18913129117967882336088833)
            ·
              refine ⟨14184846838475911752066625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18913129117967882336088833 14184846838475911752066625)
              ·
                refine ⟨10638635128856933814049969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14184846838475911752066625 10638635128856933814049969)
                ·
                  refine ⟨7978976346642700360537477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10638635128856933814049969 7978976346642700360537477)
                  ·
                    refine ⟨1496058064995506317600777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7978976346642700360537477 1496058064995506317600777)
                    ·
                      refine ⟨1122043548746629738200583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1496058064995506317600777 1122043548746629738200583)
                      ·
                        rfl

theorem cell23_2185172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_2185172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185172 prefixEnd_2185172 := by exact prefixLift 2185172
  have htrace : WordTrace (prefixWord ++ tailWord_2185172) baseStart_2185172 baseEnd_2185172 := by
    simpa [prefixWord, tailWord_2185172, baseEnd_2185172] using wordTrace_append hprefix tailTrace_2185172
  have hstable : (prefixWord ++ tailWord_2185172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185172).length < 2 ^ (prefixWord ++ tailWord_2185172).sum := by decide
  have hdescent : baseEnd_2185172 < baseStart_2185172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185175 : List Nat := [1, 1, 3, 2, 1, 1, 3, 4, 2, 2, 3]
def baseStart_2185175 : Nat := 118140960795 + 2185175 * 2 ^ 59
def prefixEnd_2185175 : Nat := 4983230072969 + 3 ^ 40 * 2185175 * 2
def baseEnd_2185175 : Nat := 1122045089188593226463069

theorem tailTrace_2185175 : CollatzResearch.WordTrace tailWord_2185175 prefixEnd_2185175 1122045089188593226463069 := by
  unfold tailWord_2185175
  simp only [CollatzResearch.WordTrace]
  refine ⟨79699879858491648023284979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53133253238994432015523319 79699879858491648023284979)
  ·
    refine ⟨119549819787737472034927469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79699879858491648023284979 119549819787737472034927469)
    ·
      refine ⟨44831182420401552013097801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119549819787737472034927469 44831182420401552013097801)
      ·
        refine ⟨33623386815301164009823351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44831182420401552013097801 33623386815301164009823351)
        ·
          refine ⟨50435080222951746014735027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33623386815301164009823351 50435080222951746014735027)
          ·
            refine ⟨75652620334427619022102541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50435080222951746014735027 75652620334427619022102541)
            ·
              refine ⟨28369732625410357133288453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75652620334427619022102541 28369732625410357133288453)
              ·
                refine ⟨5319324867264441962491585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28369732625410357133288453 5319324867264441962491585)
                ·
                  refine ⟨3989493650448331471868689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5319324867264441962491585 3989493650448331471868689)
                  ·
                    refine ⟨2992120237836248603901517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3989493650448331471868689 2992120237836248603901517)
                    ·
                      refine ⟨1122045089188593226463069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2992120237836248603901517 1122045089188593226463069)
                      ·
                        rfl

theorem cell23_2185175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_2185175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185175 prefixEnd_2185175 := by exact prefixLift 2185175
  have htrace : WordTrace (prefixWord ++ tailWord_2185175) baseStart_2185175 baseEnd_2185175 := by
    simpa [prefixWord, tailWord_2185175, baseEnd_2185175] using wordTrace_append hprefix tailTrace_2185175
  have hstable : (prefixWord ++ tailWord_2185175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185175).length < 2 ^ (prefixWord ++ tailWord_2185175).sum := by decide
  have hdescent : baseEnd_2185175 < baseStart_2185175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185206 : List Nat := [5, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4]
def baseStart_2185206 : Nat := 118140960795 + 2185206 * 2 ^ 59
def prefixEnd_2185206 : Nat := 4983230072969 + 3 ^ 40 * 2185206 * 2
def baseEnd_2185206 : Nat := 1122061007088882605175427

theorem tailTrace_2185206 : CollatzResearch.WordTrace tailWord_2185206 prefixEnd_2185206 1122061007088882605175427 := by
  unfold tailWord_2185206
  simp only [CollatzResearch.WordTrace]
  refine ⟨4981313157586208769853967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53134007014252893545108981 4981313157586208769853967)
  ·
    refine ⟨7471969736379313154780951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4981313157586208769853967 7471969736379313154780951)
    ·
      refine ⟨11207954604568969732171427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7471969736379313154780951 11207954604568969732171427)
      ·
        refine ⟨16811931906853454598257141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11207954604568969732171427 16811931906853454598257141)
        ·
          refine ⟨1576118616267511368586607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16811931906853454598257141 1576118616267511368586607)
          ·
            refine ⟨2364177924401267052879911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1576118616267511368586607 2364177924401267052879911)
            ·
              refine ⟨3546266886601900579319867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2364177924401267052879911 3546266886601900579319867)
              ·
                refine ⟨5319400329902850868979801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3546266886601900579319867 5319400329902850868979801)
                ·
                  refine ⟨3989550247427138151734851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5319400329902850868979801 3989550247427138151734851)
                  ·
                    refine ⟨5984325371140707227602277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3989550247427138151734851 5984325371140707227602277)
                    ·
                      refine ⟨1122061007088882605175427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5984325371140707227602277 1122061007088882605175427)
                      ·
                        rfl

theorem cell23_2185206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_2185206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185206 prefixEnd_2185206 := by exact prefixLift 2185206
  have htrace : WordTrace (prefixWord ++ tailWord_2185206) baseStart_2185206 baseEnd_2185206 := by
    simpa [prefixWord, tailWord_2185206, baseEnd_2185206] using wordTrace_append hprefix tailTrace_2185206
  have hstable : (prefixWord ++ tailWord_2185206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185206).length < 2 ^ (prefixWord ++ tailWord_2185206).sum := by decide
  have hdescent : baseEnd_2185206 < baseStart_2185206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185273 : List Nat := [1, 2, 1, 5, 3, 2, 1, 3, 1, 1, 3]
def baseStart_2185273 : Nat := 118140960795 + 2185273 * 2 ^ 59
def prefixEnd_2185273 : Nat := 4983230072969 + 3 ^ 40 * 2185273 * 2
def baseEnd_2185273 : Nat := 1122095410292733843037619

theorem tailTrace_2185273 : CollatzResearch.WordTrace tailWord_2185273 prefixEnd_2185273 1122095410292733843037619 := by
  unfold tailWord_2185273
  simp only [CollatzResearch.WordTrace]
  refine ⟨79703454212136610760352473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53135636141424407173568315 79703454212136610760352473)
  ·
    refine ⟨59777590659102458070264355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79703454212136610760352473 59777590659102458070264355)
    ·
      refine ⟨89666385988653687105396533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59777590659102458070264355 89666385988653687105396533)
      ·
        refine ⟨8406223686436283166130925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89666385988653687105396533 8406223686436283166130925)
        ·
          refine ⟨3152333882413606187299097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8406223686436283166130925 3152333882413606187299097)
          ·
            refine ⟨2364250411810204640474323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3152333882413606187299097 2364250411810204640474323)
            ·
              refine ⟨3546375617715306960711485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2364250411810204640474323 3546375617715306960711485)
              ·
                refine ⟨1329890856643240110266807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3546375617715306960711485 1329890856643240110266807)
                ·
                  refine ⟨1994836284964860165400211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1329890856643240110266807 1994836284964860165400211)
                  ·
                    refine ⟨2992254427447290248100317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1994836284964860165400211 2992254427447290248100317)
                    ·
                      refine ⟨1122095410292733843037619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2992254427447290248100317 1122095410292733843037619)
                      ·
                        rfl

theorem cell23_2185273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_2185273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185273 prefixEnd_2185273 := by exact prefixLift 2185273
  have htrace : WordTrace (prefixWord ++ tailWord_2185273) baseStart_2185273 baseEnd_2185273 := by
    simpa [prefixWord, tailWord_2185273, baseEnd_2185273] using wordTrace_append hprefix tailTrace_2185273
  have hstable : (prefixWord ++ tailWord_2185273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185273).length < 2 ^ (prefixWord ++ tailWord_2185273).sum := by decide
  have hdescent : baseEnd_2185273 < baseStart_2185273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185295 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 3, 3, 3]
def baseStart_2185295 : Nat := 118140960795 + 2185295 * 2 ^ 59
def prefixEnd_2185295 : Nat := 4983230072969 + 3 ^ 40 * 2185295 * 2
def baseEnd_2185295 : Nat := 1122106706867132756962517

theorem tailTrace_2185295 : CollatzResearch.WordTrace tailWord_2185295 prefixEnd_2185295 1122106706867132756962517 := by
  unfold tailWord_2185295
  simp only [CollatzResearch.WordTrace]
  refine ⟨79704256618056908517653339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53136171078704605678435559 79704256618056908517653339)
  ·
    refine ⟨119556384927085362776480009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79704256618056908517653339 119556384927085362776480009)
    ·
      refine ⟨89667288695314022082360007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119556384927085362776480009 89667288695314022082360007)
      ·
        refine ⟨134500933042971033123540011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89667288695314022082360007 134500933042971033123540011)
        ·
          refine ⟨201751399564456549685310017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134500933042971033123540011 201751399564456549685310017)
          ·
            refine ⟨151313549673342412263982513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201751399564456549685310017 151313549673342412263982513)
            ·
              refine ⟨113485162255006809197986885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151313549673342412263982513 113485162255006809197986885)
              ·
                refine ⟨21278467922813776724622541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113485162255006809197986885 21278467922813776724622541)
                ·
                  refine ⟨7979425471055166271733453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21278467922813776724622541 7979425471055166271733453)
                  ·
                    refine ⟨2992284551645687351900045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7979425471055166271733453 2992284551645687351900045)
                    ·
                      refine ⟨1122106706867132756962517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2992284551645687351900045 1122106706867132756962517)
                      ·
                        rfl

theorem cell23_2185295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 3, 3].length) (baseStart_2185295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185295 prefixEnd_2185295 := by exact prefixLift 2185295
  have htrace : WordTrace (prefixWord ++ tailWord_2185295) baseStart_2185295 baseEnd_2185295 := by
    simpa [prefixWord, tailWord_2185295, baseEnd_2185295] using wordTrace_append hprefix tailTrace_2185295
  have hstable : (prefixWord ++ tailWord_2185295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185295).length < 2 ^ (prefixWord ++ tailWord_2185295).sum := by decide
  have hdescent : baseEnd_2185295 < baseStart_2185295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185310 : List Nat := [4, 4, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_2185310 : Nat := 118140960795 + 2185310 * 2 ^ 59
def prefixEnd_2185310 : Nat := 4983230072969 + 3 ^ 40 * 2185310 * 2
def baseEnd_2185310 : Nat := 374038136358983399424983

theorem tailTrace_2185310 : CollatzResearch.WordTrace tailWord_2185310 prefixEnd_2185310 374038136358983399424983 := by
  unfold tailWord_2185310
  simp only [CollatzResearch.WordTrace]
  refine ⟨9963100464125320759931173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53136535808668377386299589 9963100464125320759931173)
  ·
    refine ⟨1868081337023497642487095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9963100464125320759931173 1868081337023497642487095)
    ·
      refine ⟨2802122005535246463730643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1868081337023497642487095 2802122005535246463730643)
      ·
        refine ⟨4203183008302869695595965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2802122005535246463730643 4203183008302869695595965)
        ·
          refine ⟨1576193628113576135848487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4203183008302869695595965 1576193628113576135848487)
          ·
            refine ⟨2364290442170364203772731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1576193628113576135848487 2364290442170364203772731)
            ·
              refine ⟨3546435663255546305659097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2364290442170364203772731 3546435663255546305659097)
              ·
                refine ⟨2659826747441659729244323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3546435663255546305659097 2659826747441659729244323)
                ·
                  refine ⟨3989740121162489593866485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2659826747441659729244323 3989740121162489593866485)
                  ·
                    refine ⟨374038136358983399424983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3989740121162489593866485 374038136358983399424983)
                    ·
                      rfl

theorem cell23_2185310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_2185310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185310 prefixEnd_2185310 := by exact prefixLift 2185310
  have htrace : WordTrace (prefixWord ++ tailWord_2185310) baseStart_2185310 baseEnd_2185310 := by
    simpa [prefixWord, tailWord_2185310, baseEnd_2185310] using wordTrace_append hprefix tailTrace_2185310
  have hstable : (prefixWord ++ tailWord_2185310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185310).length < 2 ^ (prefixWord ++ tailWord_2185310).sum := by decide
  have hdescent : baseEnd_2185310 < baseStart_2185310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185352 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 2, 3, 4]
def baseStart_2185352 : Nat := 118140960795 + 2185352 * 2 ^ 59
def prefixEnd_2185352 : Nat := 4983230072969 + 3 ^ 40 * 2185352 * 2
def baseEnd_2185352 : Nat := 1122135975264439033949755

theorem tailTrace_2185352 : CollatzResearch.WordTrace tailWord_2185352 prefixEnd_2185352 1122135975264439033949755 := by
  unfold tailWord_2185352
  simp only [CollatzResearch.WordTrace]
  refine ⟨39853167789425203626239155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53137557052566938168318873 39853167789425203626239155)
  ·
    refine ⟨59779751684137805439358733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39853167789425203626239155 59779751684137805439358733)
    ·
      refine ⟨22417406881551677039759525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59779751684137805439358733 22417406881551677039759525)
      ·
        refine ⟨4203263790290939444954911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22417406881551677039759525 4203263790290939444954911)
        ·
          refine ⟨6304895685436409167432367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4203263790290939444954911 6304895685436409167432367)
          ·
            refine ⟨9457343528154613751148551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6304895685436409167432367 9457343528154613751148551)
            ·
              refine ⟨14186015292231920626722827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9457343528154613751148551 14186015292231920626722827)
              ·
                refine ⟨21279022938347880940084241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14186015292231920626722827 21279022938347880940084241)
                ·
                  refine ⟨15959267203760910705063181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21279022938347880940084241 15959267203760910705063181)
                  ·
                    refine ⟨5984725201410341514398693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15959267203760910705063181 5984725201410341514398693)
                    ·
                      refine ⟨1122135975264439033949755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5984725201410341514398693 1122135975264439033949755)
                      ·
                        rfl

theorem cell23_2185352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_2185352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185352 prefixEnd_2185352 := by exact prefixLift 2185352
  have htrace : WordTrace (prefixWord ++ tailWord_2185352) baseStart_2185352 baseEnd_2185352 := by
    simpa [prefixWord, tailWord_2185352, baseEnd_2185352] using wordTrace_append hprefix tailTrace_2185352
  have hstable : (prefixWord ++ tailWord_2185352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185352).length < 2 ^ (prefixWord ++ tailWord_2185352).sum := by decide
  have hdescent : baseEnd_2185352 < baseStart_2185352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185362 : List Nat := [3, 2, 3, 1, 1, 1, 3, 1, 2, 6]
def baseStart_2185362 : Nat := 118140960795 + 2185362 * 2 ^ 59
def prefixEnd_2185362 : Nat := 4983230072969 + 3 ^ 40 * 2185362 * 2
def baseEnd_2185362 : Nat := 374047036690327998274903

theorem tailTrace_2185362 : CollatzResearch.WordTrace tailWord_2185362 prefixEnd_2185362 374047036690327998274903 := by
  unfold tailWord_2185362
  simp only [CollatzResearch.WordTrace]
  refine ⟨19926675077203544740085585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53137800205876119306894893 19926675077203544740085585)
  ·
    refine ⟨14945006307902658555064189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19926675077203544740085585 14945006307902658555064189)
    ·
      refine ⟨5604377365463496958149071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14945006307902658555064189 5604377365463496958149071)
      ·
        refine ⟨8406566048195245437223607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5604377365463496958149071 8406566048195245437223607)
        ·
          refine ⟨12609849072292868155835411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8406566048195245437223607 12609849072292868155835411)
          ·
            refine ⟨18914773608439302233753117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12609849072292868155835411 18914773608439302233753117)
            ·
              refine ⟨7093040103164738337657419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18914773608439302233753117 7093040103164738337657419)
              ·
                refine ⟨10639560154747107506486129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7093040103164738337657419 10639560154747107506486129)
                ·
                  refine ⟨7979670116060330629864597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10639560154747107506486129 7979670116060330629864597)
                  ·
                    refine ⟨374047036690327998274903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7979670116060330629864597 374047036690327998274903)
                    ·
                      rfl

theorem cell23_2185362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_2185362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185362 prefixEnd_2185362 := by exact prefixLift 2185362
  have htrace : WordTrace (prefixWord ++ tailWord_2185362) baseStart_2185362 baseEnd_2185362 := by
    simpa [prefixWord, tailWord_2185362, baseEnd_2185362] using wordTrace_append hprefix tailTrace_2185362
  have hstable : (prefixWord ++ tailWord_2185362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185362).length < 2 ^ (prefixWord ++ tailWord_2185362).sum := by decide
  have hdescent : baseEnd_2185362 < baseStart_2185362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185372 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 2, 4, 3]
def baseStart_2185372 : Nat := 118140960795 + 2185372 * 2 ^ 59
def prefixEnd_2185372 : Nat := 4983230072969 + 3 ^ 40 * 2185372 * 2
def baseEnd_2185372 : Nat := 1122146244877528955699663

theorem tailTrace_2185372 : CollatzResearch.WordTrace tailWord_2185372 prefixEnd_2185372 1122146244877528955699663 := by
  unfold tailWord_2185372
  simp only [CollatzResearch.WordTrace]
  refine ⟨39853532519388975334103185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53138043359185300445470913 39853532519388975334103185)
  ·
    refine ⟨29890149389541731500577389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39853532519388975334103185 29890149389541731500577389)
    ·
      refine ⟨11208806021078149312716521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29890149389541731500577389 11208806021078149312716521)
      ·
        refine ⟨8406604515808611984537391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11208806021078149312716521 8406604515808611984537391)
        ·
          refine ⟨12609906773712917976806087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8406604515808611984537391 12609906773712917976806087)
          ·
            refine ⟨18914860160569376965209131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12609906773712917976806087 18914860160569376965209131)
            ·
              refine ⟨28372290240854065447813697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18914860160569376965209131 28372290240854065447813697)
              ·
                refine ⟨21279217680640549085860273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28372290240854065447813697 21279217680640549085860273)
                ·
                  refine ⟨15959413260480411814395205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21279217680640549085860273 15959413260480411814395205)
                  ·
                    refine ⟨2992389986340077215199101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15959413260480411814395205 2992389986340077215199101)
                    ·
                      refine ⟨1122146244877528955699663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2992389986340077215199101 1122146244877528955699663)
                      ·
                        rfl

theorem cell23_2185372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_2185372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185372 prefixEnd_2185372 := by exact prefixLift 2185372
  have htrace : WordTrace (prefixWord ++ tailWord_2185372) baseStart_2185372 baseEnd_2185372 := by
    simpa [prefixWord, tailWord_2185372, baseEnd_2185372] using wordTrace_append hprefix tailTrace_2185372
  have hstable : (prefixWord ++ tailWord_2185372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185372).length < 2 ^ (prefixWord ++ tailWord_2185372).sum := by decide
  have hdescent : baseEnd_2185372 < baseStart_2185372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185390 : List Nat := [4, 1, 4, 2, 1, 1, 1, 3, 1, 3, 2]
def baseStart_2185390 : Nat := 118140960795 + 2185390 * 2 ^ 59
def prefixEnd_2185390 : Nat := 4983230072969 + 3 ^ 40 * 2185390 * 2
def baseEnd_2185390 : Nat := 1122155487529309885274581

theorem tailTrace_2185390 : CollatzResearch.WordTrace tailWord_2185390 prefixEnd_2185390 1122155487529309885274581 := by
  unfold tailWord_2185390
  simp only [CollatzResearch.WordTrace]
  refine ⟨9963465194089092467795203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53138481035141826494907749 9963465194089092467795203)
  ·
    refine ⟨14945197791133638701692805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9963465194089092467795203 14945197791133638701692805)
    ·
      refine ⟨2802224585837557256567401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14945197791133638701692805 2802224585837557256567401)
      ·
        refine ⟨2101668439378167942425551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2802224585837557256567401 2101668439378167942425551)
        ·
          refine ⟨3152502659067251913638327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2101668439378167942425551 3152502659067251913638327)
          ·
            refine ⟨4728753988600877870457491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3152502659067251913638327 4728753988600877870457491)
            ·
              refine ⟨7093130982901316805686237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4728753988600877870457491 7093130982901316805686237)
              ·
                refine ⟨2659924118587993802132339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7093130982901316805686237 2659924118587993802132339)
                ·
                  refine ⟨3989886177881990703198509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2659924118587993802132339 3989886177881990703198509)
                  ·
                    refine ⟨1496207316705746513699441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3989886177881990703198509 1496207316705746513699441)
                    ·
                      refine ⟨1122155487529309885274581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1496207316705746513699441 1122155487529309885274581)
                      ·
                        rfl

theorem cell23_2185390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_2185390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185390 prefixEnd_2185390 := by exact prefixLift 2185390
  have htrace : WordTrace (prefixWord ++ tailWord_2185390) baseStart_2185390 baseEnd_2185390 := by
    simpa [prefixWord, tailWord_2185390, baseEnd_2185390] using wordTrace_append hprefix tailTrace_2185390
  have hstable : (prefixWord ++ tailWord_2185390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185390).length < 2 ^ (prefixWord ++ tailWord_2185390).sum := by decide
  have hdescent : baseEnd_2185390 < baseStart_2185390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185402 : List Nat := [3, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3]
def baseStart_2185402 : Nat := 118140960795 + 2185402 * 2 ^ 59
def prefixEnd_2185402 : Nat := 4983230072969 + 3 ^ 40 * 2185402 * 2
def baseEnd_2185402 : Nat := 1122161649297163838324525

theorem tailTrace_2185402 : CollatzResearch.WordTrace tailWord_2185402 prefixEnd_2185402 1122161649297163838324525 := by
  unfold tailWord_2185402
  simp only [CollatzResearch.WordTrace]
  refine ⟨19927039807167316447949615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53138772819112843861198973 19927039807167316447949615)
  ·
    refine ⟨29890559710750974671924423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19927039807167316447949615 29890559710750974671924423)
    ·
      refine ⟨44835839566126462007886635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29890559710750974671924423 44835839566126462007886635)
      ·
        refine ⟨67253759349189693011829953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44835839566126462007886635 67253759349189693011829953)
        ·
          refine ⟨50440319511892269758872465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67253759349189693011829953 50440319511892269758872465)
          ·
            refine ⟨37830239633919202319154349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50440319511892269758872465 37830239633919202319154349)
            ·
              refine ⟨14186339862719700869682881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37830239633919202319154349 14186339862719700869682881)
              ·
                refine ⟨10639754897039775652262161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14186339862719700869682881 10639754897039775652262161)
                ·
                  refine ⟨7979816172779831739196621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10639754897039775652262161 7979816172779831739196621)
                  ·
                    refine ⟨2992431064792436902198733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7979816172779831739196621 2992431064792436902198733)
                    ·
                      refine ⟨1122161649297163838324525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2992431064792436902198733 1122161649297163838324525)
                      ·
                        rfl

theorem cell23_2185402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 2, 3, 3].length) (baseStart_2185402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185402 prefixEnd_2185402 := by exact prefixLift 2185402
  have htrace : WordTrace (prefixWord ++ tailWord_2185402) baseStart_2185402 baseEnd_2185402 := by
    simpa [prefixWord, tailWord_2185402, baseEnd_2185402] using wordTrace_append hprefix tailTrace_2185402
  have hstable : (prefixWord ++ tailWord_2185402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185402).length < 2 ^ (prefixWord ++ tailWord_2185402).sum := by decide
  have hdescent : baseEnd_2185402 < baseStart_2185402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185420 : List Nat := [2, 2, 1, 6, 2, 1, 1, 1, 1, 4, 2]
def baseStart_2185420 : Nat := 118140960795 + 2185420 * 2 ^ 59
def prefixEnd_2185420 : Nat := 4983230072969 + 3 ^ 40 * 2185420 * 2
def baseEnd_2185420 : Nat := 1122170891948944767899443

theorem tailTrace_2185420 : CollatzResearch.WordTrace tailWord_2185420 prefixEnd_2185420 1122170891948944767899443 := by
  unfold tailWord_2185420
  simp only [CollatzResearch.WordTrace]
  refine ⟨39854407871302027432976857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53139210495069369910635809 39854407871302027432976857)
  ·
    refine ⟨29890805903476520574732643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39854407871302027432976857 29890805903476520574732643)
    ·
      refine ⟨44836208855214780862098965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29890805903476520574732643 44836208855214780862098965)
      ·
        refine ⟨2101697290088192852910889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 44836208855214780862098965 2101697290088192852910889)
        ·
          refine ⟨1576272967566144639683167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2101697290088192852910889 1576272967566144639683167)
          ·
            refine ⟨2364409451349216959524751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1576272967566144639683167 2364409451349216959524751)
            ·
              refine ⟨3546614177023825439287127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2364409451349216959524751 3546614177023825439287127)
              ·
                refine ⟨5319921265535738158930691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3546614177023825439287127 5319921265535738158930691)
                ·
                  refine ⟨7979881898303607238396037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5319921265535738158930691 7979881898303607238396037)
                  ·
                    refine ⟨1496227855931926357199257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7979881898303607238396037 1496227855931926357199257)
                    ·
                      refine ⟨1122170891948944767899443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1496227855931926357199257 1122170891948944767899443)
                      ·
                        rfl

theorem cell23_2185420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_2185420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185420 prefixEnd_2185420 := by exact prefixLift 2185420
  have htrace : WordTrace (prefixWord ++ tailWord_2185420) baseStart_2185420 baseEnd_2185420 := by
    simpa [prefixWord, tailWord_2185420, baseEnd_2185420] using wordTrace_append hprefix tailTrace_2185420
  have hstable : (prefixWord ++ tailWord_2185420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185420).length < 2 ^ (prefixWord ++ tailWord_2185420).sum := by decide
  have hdescent : baseEnd_2185420 < baseStart_2185420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185422 : List Nat := [4, 1, 1, 1, 4, 1, 1, 2, 1, 7]
def baseStart_2185422 : Nat := 118140960795 + 2185422 * 2 ^ 59
def prefixEnd_2185422 : Nat := 4983230072969 + 3 ^ 40 * 2185422 * 2
def baseEnd_2185422 : Nat := 374057306303417920024811

theorem tailTrace_2185422 : CollatzResearch.WordTrace tailWord_2185422 prefixEnd_2185422 374057306303417920024811 := by
  unfold tailWord_2185422
  simp only [CollatzResearch.WordTrace]
  refine ⟨9963611086074601150940815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53139259125731206138351013 9963611086074601150940815)
  ·
    refine ⟨14945416629111901726411223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9963611086074601150940815 14945416629111901726411223)
    ·
      refine ⟨22418124943667852589616835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14945416629111901726411223 22418124943667852589616835)
      ·
        refine ⟨33627187415501778884425253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22418124943667852589616835 33627187415501778884425253)
        ·
          refine ⟨6305097640406583540829735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33627187415501778884425253 6305097640406583540829735)
          ·
            refine ⟨9457646460609875311244603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6305097640406583540829735 9457646460609875311244603)
            ·
              refine ⟨14186469690914812966866905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9457646460609875311244603 14186469690914812966866905)
              ·
                refine ⟨10639852268186109725150179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14186469690914812966866905 10639852268186109725150179)
                ·
                  refine ⟨15959778402279164587725269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10639852268186109725150179 15959778402279164587725269)
                  ·
                    refine ⟨374057306303417920024811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15959778402279164587725269 374057306303417920024811)
                    ·
                      rfl

theorem cell23_2185422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_2185422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185422 prefixEnd_2185422 := by exact prefixLift 2185422
  have htrace : WordTrace (prefixWord ++ tailWord_2185422) baseStart_2185422 baseEnd_2185422 := by
    simpa [prefixWord, tailWord_2185422, baseEnd_2185422] using wordTrace_append hprefix tailTrace_2185422
  have hstable : (prefixWord ++ tailWord_2185422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185422).length < 2 ^ (prefixWord ++ tailWord_2185422).sum := by decide
  have hdescent : baseEnd_2185422 < baseStart_2185422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185443 : List Nat := [1, 1, 1, 8, 1, 2, 1, 3, 5]
def baseStart_2185443 : Nat := 118140960795 + 2185443 * 2 ^ 59
def prefixEnd_2185443 : Nat := 4983230072969 + 3 ^ 40 * 2185443 * 2
def baseEnd_2185443 : Nat := 124686966889333130879093

theorem tailTrace_2185443 : CollatzResearch.WordTrace tailWord_2185443 prefixEnd_2185443 124686966889333130879093 := by
  unfold tailWord_2185443
  simp only [CollatzResearch.WordTrace]
  refine ⟨79709654621520729794040983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53139769747680486529360655 79709654621520729794040983)
  ·
    refine ⟨119564481932281094691061475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79709654621520729794040983 119564481932281094691061475)
    ·
      refine ⟨179346722898421642036592213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119564481932281094691061475 179346722898421642036592213)
      ·
        refine ⟨2101719408965878617616315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 179346722898421642036592213 2101719408965878617616315)
        ·
          refine ⟨3152579113448817926424473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2101719408965878617616315 3152579113448817926424473)
          ·
            refine ⟨2364434335086613444818355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3152579113448817926424473 2364434335086613444818355)
            ·
              refine ⟨3546651502629920167227533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2364434335086613444818355 3546651502629920167227533)
              ·
                refine ⟨1329994313486220062710325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3546651502629920167227533 1329994313486220062710325)
                ·
                  refine ⟨124686966889333130879093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1329994313486220062710325 124686966889333130879093)
                  ·
                    rfl

theorem cell23_2185443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 3, 5].length) (baseStart_2185443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185443 prefixEnd_2185443 := by exact prefixLift 2185443
  have htrace : WordTrace (prefixWord ++ tailWord_2185443) baseStart_2185443 baseEnd_2185443 := by
    simpa [prefixWord, tailWord_2185443, baseEnd_2185443] using wordTrace_append hprefix tailTrace_2185443
  have hstable : (prefixWord ++ tailWord_2185443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185443).length < 2 ^ (prefixWord ++ tailWord_2185443).sum := by decide
  have hdescent : baseEnd_2185443 < baseStart_2185443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185529 : List Nat := [1, 2, 1, 6, 1, 1, 1, 2, 3, 5]
def baseStart_2185529 : Nat := 118140960795 + 2185529 * 2 ^ 59
def prefixEnd_2185529 : Nat := 4983230072969 + 3 ^ 40 * 2185529 * 2
def baseEnd_2185529 : Nat := 374075620446761613812147

theorem tailTrace_2185529 : CollatzResearch.WordTrace tailWord_2185529 prefixEnd_2185529 374075620446761613812147 := by
  unfold tailWord_2185529
  simp only [CollatzResearch.WordTrace]
  refine ⟨79712791299209166481671641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53141860866139444321114427 79712791299209166481671641)
  ·
    refine ⟨59784593474406874861253731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79712791299209166481671641 59784593474406874861253731)
    ·
      refine ⟨89676890211610312291880597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59784593474406874861253731 89676890211610312291880597)
      ·
        refine ⟨4203604228669233388681903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 89676890211610312291880597 4203604228669233388681903)
        ·
          refine ⟨6305406343003850083022855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4203604228669233388681903 6305406343003850083022855)
          ·
            refine ⟨9458109514505775124534283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6305406343003850083022855 9458109514505775124534283)
            ·
              refine ⟨14187164271758662686801425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9458109514505775124534283 14187164271758662686801425)
              ·
                refine ⟨10640373203818997015101069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14187164271758662686801425 10640373203818997015101069)
                ·
                  refine ⟨3990139951432123880662901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10640373203818997015101069 3990139951432123880662901)
                  ·
                    refine ⟨374075620446761613812147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3990139951432123880662901 374075620446761613812147)
                    ·
                      rfl

theorem cell23_2185529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 5].length) (baseStart_2185529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185529 prefixEnd_2185529 := by exact prefixLift 2185529
  have htrace : WordTrace (prefixWord ++ tailWord_2185529) baseStart_2185529 baseEnd_2185529 := by
    simpa [prefixWord, tailWord_2185529, baseEnd_2185529] using wordTrace_append hprefix tailTrace_2185529
  have hstable : (prefixWord ++ tailWord_2185529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185529).length < 2 ^ (prefixWord ++ tailWord_2185529).sum := by decide
  have hdescent : baseEnd_2185529 < baseStart_2185529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185553 : List Nat := [1, 2, 2, 1, 4, 4, 1, 1, 2, 3, 2]
def baseStart_2185553 : Nat := 118140960795 + 2185553 * 2 ^ 59
def prefixEnd_2185553 : Nat := 4983230072969 + 3 ^ 40 * 2185553 * 2
def baseEnd_2185553 : Nat := 1122239184875992747536331

theorem tailTrace_2185553 : CollatzResearch.WordTrace tailWord_2185553 prefixEnd_2185553 1122239184875992747536331 := by
  unfold tailWord_2185553
  simp only [CollatzResearch.WordTrace]
  refine ⟨79713666651122218580545313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53142444434081479053696875 79713666651122218580545313)
  ·
    refine ⟨59785249988341663935408985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79713666651122218580545313 59785249988341663935408985)
    ·
      refine ⟨44838937491256247951556739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59785249988341663935408985 44838937491256247951556739)
      ·
        refine ⟨67258406236884371927335109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44838937491256247951556739 67258406236884371927335109)
        ·
          refine ⟨12610951169415819736375333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67258406236884371927335109 12610951169415819736375333)
          ·
            refine ⟨2364553344265466200570375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12610951169415819736375333 2364553344265466200570375)
            ·
              refine ⟨3546830016398199300855563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2364553344265466200570375 3546830016398199300855563)
              ·
                refine ⟨5320245024597298951283345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3546830016398199300855563 5320245024597298951283345)
                ·
                  refine ⟨3990183768447974213462509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5320245024597298951283345 3990183768447974213462509)
                  ·
                    refine ⟨1496318913167990330048441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3990183768447974213462509 1496318913167990330048441)
                    ·
                      refine ⟨1122239184875992747536331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1496318913167990330048441 1122239184875992747536331)
                      ·
                        rfl

theorem cell23_2185553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 3, 2].length) (baseStart_2185553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185553 prefixEnd_2185553 := by exact prefixLift 2185553
  have htrace : WordTrace (prefixWord ++ tailWord_2185553) baseStart_2185553 baseEnd_2185553 := by
    simpa [prefixWord, tailWord_2185553, baseEnd_2185553] using wordTrace_append hprefix tailTrace_2185553
  have hstable : (prefixWord ++ tailWord_2185553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185553).length < 2 ^ (prefixWord ++ tailWord_2185553).sum := by decide
  have hdescent : baseEnd_2185553 < baseStart_2185553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185559 : List Nat := [1, 1, 3, 2, 3, 1, 2, 2, 4, 4]
def baseStart_2185559 : Nat := 118140960795 + 2185559 * 2 ^ 59
def prefixEnd_2185559 : Nat := 4983230072969 + 3 ^ 40 * 2185559 * 2
def baseEnd_2185559 : Nat := 374080755253306574687101

theorem tailTrace_2185559 : CollatzResearch.WordTrace tailWord_2185559 prefixEnd_2185559 374080755253306574687101 := by
  unfold tailWord_2185559
  simp only [CollatzResearch.WordTrace]
  refine ⟨79713885489100481605263731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53142590326066987736842487 79713885489100481605263731)
  ·
    refine ⟨119570828233650722407895597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79713885489100481605263731 119570828233650722407895597)
    ·
      refine ⟨44839060587619020902960849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119570828233650722407895597 44839060587619020902960849)
      ·
        refine ⟨33629295440714265677220637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44839060587619020902960849 33629295440714265677220637)
        ·
          refine ⟨12610985790267849628957739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33629295440714265677220637 12610985790267849628957739)
          ·
            refine ⟨18916478685401774443436609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12610985790267849628957739 18916478685401774443436609)
            ·
              refine ⟨14187359014051330832577457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18916478685401774443436609 14187359014051330832577457)
              ·
                refine ⟨10640519260538498124433093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14187359014051330832577457 10640519260538498124433093)
                ·
                  refine ⟨1995097361350968398331205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10640519260538498124433093 1995097361350968398331205)
                  ·
                    refine ⟨374080755253306574687101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1995097361350968398331205 374080755253306574687101)
                    ·
                      rfl

theorem cell23_2185559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 4, 4].length) (baseStart_2185559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185559 prefixEnd_2185559 := by exact prefixLift 2185559
  have htrace : WordTrace (prefixWord ++ tailWord_2185559) baseStart_2185559 baseEnd_2185559 := by
    simpa [prefixWord, tailWord_2185559, baseEnd_2185559] using wordTrace_append hprefix tailTrace_2185559
  have hstable : (prefixWord ++ tailWord_2185559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185559).length < 2 ^ (prefixWord ++ tailWord_2185559).sum := by decide
  have hdescent : baseEnd_2185559 < baseStart_2185559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185562 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 3, 1, 6]
def baseStart_2185562 : Nat := 118140960795 + 2185562 * 2 ^ 59
def prefixEnd_2185562 : Nat := 4983230072969 + 3 ^ 40 * 2185562 * 2
def baseEnd_2185562 : Nat := 1122243806201883212323789

theorem tailTrace_2185562 : CollatzResearch.WordTrace tailWord_2185562 prefixEnd_2185562 1122243806201883212323789 := by
  unfold tailWord_2185562
  simp only [CollatzResearch.WordTrace]
  refine ⟨19928498727022403279405735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53142663272059742078415293 19928498727022403279405735)
  ·
    refine ⟨29892748090533604919108603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19928498727022403279405735 29892748090533604919108603)
    ·
      refine ⟨44839122135800407378662905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29892748090533604919108603 44839122135800407378662905)
      ·
        refine ⟨33629341601850305533997179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44839122135800407378662905 33629341601850305533997179)
        ·
          refine ⟨50444012402775458300995769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33629341601850305533997179 50444012402775458300995769)
          ·
            refine ⟨37833009302081593725746827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50444012402775458300995769 37833009302081593725746827)
            ·
              refine ⟨56749513953122390588620241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37833009302081593725746827 56749513953122390588620241)
              ·
                refine ⟨42562135464841792941465181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56749513953122390588620241 42562135464841792941465181)
                ·
                  refine ⟨15960800799315672353049443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42562135464841792941465181 15960800799315672353049443)
                  ·
                    refine ⟨23941201198973508529574165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15960800799315672353049443 23941201198973508529574165)
                    ·
                      refine ⟨1122243806201883212323789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23941201198973508529574165 1122243806201883212323789)
                      ·
                        rfl

theorem cell23_2185562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_2185562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185562 prefixEnd_2185562 := by exact prefixLift 2185562
  have htrace : WordTrace (prefixWord ++ tailWord_2185562) baseStart_2185562 baseEnd_2185562 := by
    simpa [prefixWord, tailWord_2185562, baseEnd_2185562] using wordTrace_append hprefix tailTrace_2185562
  have hstable : (prefixWord ++ tailWord_2185562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185562).length < 2 ^ (prefixWord ++ tailWord_2185562).sum := by decide
  have hdescent : baseEnd_2185562 < baseStart_2185562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185572 : List Nat := [2, 3, 1, 1, 3, 1, 12]
def baseStart_2185572 : Nat := 118140960795 + 2185572 * 2 ^ 59
def prefixEnd_2185572 : Nat := 4983230072969 + 3 ^ 40 * 2185572 * 2
def baseEnd_2185572 : Nat := 13854925197634915718503

theorem tailTrace_2185572 : CollatzResearch.WordTrace tailWord_2185572 prefixEnd_2185572 13854925197634915718503 := by
  unfold tailWord_2185572
  simp only [CollatzResearch.WordTrace]
  refine ⟨39857179819026692412743485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53142906425368923216991313 39857179819026692412743485)
  ·
    refine ⟨14946442432135009654778807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39857179819026692412743485 14946442432135009654778807)
    ·
      refine ⟨22419663648202514482168211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14946442432135009654778807 22419663648202514482168211)
      ·
        refine ⟨33629495472303771723252317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22419663648202514482168211 33629495472303771723252317)
        ·
          refine ⟨12611060802113914396219619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33629495472303771723252317 12611060802113914396219619)
          ·
            refine ⟨18916591203170871594329429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12611060802113914396219619 18916591203170871594329429)
            ·
              refine ⟨13854925197634915718503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 18916591203170871594329429 13854925197634915718503)
              ·
                rfl

theorem cell23_2185572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 12].length) (baseStart_2185572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185572 prefixEnd_2185572 := by exact prefixLift 2185572
  have htrace : WordTrace (prefixWord ++ tailWord_2185572) baseStart_2185572 baseEnd_2185572 := by
    simpa [prefixWord, tailWord_2185572, baseEnd_2185572] using wordTrace_append hprefix tailTrace_2185572
  have hstable : (prefixWord ++ tailWord_2185572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185572).length < 2 ^ (prefixWord ++ tailWord_2185572).sum := by decide
  have hdescent : baseEnd_2185572 < baseStart_2185572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185576 : List Nat := [2, 1, 4, 2, 2, 2, 1, 1, 4, 4]
def baseStart_2185576 : Nat := 118140960795 + 2185576 * 2 ^ 59
def prefixEnd_2185576 : Nat := 4983230072969 + 3 ^ 40 * 2185576 * 2
def baseEnd_2185576 : Nat := 374083664977015385849575

theorem tailTrace_2185576 : CollatzResearch.WordTrace tailWord_2185576 prefixEnd_2185576 374083664977015385849575 := by
  unfold tailWord_2185576
  simp only [CollatzResearch.WordTrace]
  refine ⟨39857252765019446754316291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53143003686692595672421721 39857252765019446754316291)
  ·
    refine ⟨59785879147529170131474437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39857252765019446754316291 59785879147529170131474437)
    ·
      refine ⟨11209852340161719399651457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59785879147529170131474437 11209852340161719399651457)
      ·
        refine ⟨8407389255121289549738593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11209852340161719399651457 8407389255121289549738593)
        ·
          refine ⟨6305541941340967162303945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8407389255121289549738593 6305541941340967162303945)
          ·
            refine ⟨4729156456005725371727959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6305541941340967162303945 4729156456005725371727959)
            ·
              refine ⟨7093734684008588057591939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4729156456005725371727959 7093734684008588057591939)
              ·
                refine ⟨10640602026012882086387909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7093734684008588057591939 10640602026012882086387909)
                ·
                  refine ⟨1995112879877415391197733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10640602026012882086387909 1995112879877415391197733)
                  ·
                    refine ⟨374083664977015385849575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1995112879877415391197733 374083664977015385849575)
                    ·
                      rfl

theorem cell23_2185576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_2185576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185576 prefixEnd_2185576 := by exact prefixLift 2185576
  have htrace : WordTrace (prefixWord ++ tailWord_2185576) baseStart_2185576 baseEnd_2185576 := by
    simpa [prefixWord, tailWord_2185576, baseEnd_2185576] using wordTrace_append hprefix tailTrace_2185576
  have hstable : (prefixWord ++ tailWord_2185576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185576).length < 2 ^ (prefixWord ++ tailWord_2185576).sum := by decide
  have hdescent : baseEnd_2185576 < baseStart_2185576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185603 : List Nat := [1, 1, 1, 3, 6, 1, 2, 2, 1, 2, 3]
def baseStart_2185603 : Nat := 118140960795 + 2185603 * 2 ^ 59
def prefixEnd_2185603 : Nat := 4983230072969 + 3 ^ 40 * 2185603 * 2
def baseEnd_2185603 : Nat := 1122264858908717551911101

theorem tailTrace_2185603 : CollatzResearch.WordTrace tailWord_2185603 prefixEnd_2185603 1122264858908717551911101 := by
  unfold tailWord_2185603
  simp only [CollatzResearch.WordTrace]
  refine ⟨79715490300941077119865463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53143660200627384746576975 79715490300941077119865463)
  ·
    refine ⟨119573235451411615679798195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79715490300941077119865463 119573235451411615679798195)
    ·
      refine ⟨179359853177117423519697293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119573235451411615679798195 179359853177117423519697293)
      ·
        refine ⟨67259944941419033819886485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179359853177117423519697293 67259944941419033819886485)
        ·
          refine ⟨3152809919129017210307179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 67259944941419033819886485 3152809919129017210307179)
          ·
            refine ⟨4729214878693525815460769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3152809919129017210307179 4729214878693525815460769)
            ·
              refine ⟨3546911159020144361595577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4729214878693525815460769 3546911159020144361595577)
              ·
                refine ⟨2660183369265108271196683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3546911159020144361595577 2660183369265108271196683)
                ·
                  refine ⟨3990275053897662406795025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2660183369265108271196683 3990275053897662406795025)
                  ·
                    refine ⟨2992706290423246805096269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3990275053897662406795025 2992706290423246805096269)
                    ·
                      refine ⟨1122264858908717551911101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2992706290423246805096269 1122264858908717551911101)
                      ·
                        rfl

theorem cell23_2185603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 2, 3].length) (baseStart_2185603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185603 prefixEnd_2185603 := by exact prefixLift 2185603
  have htrace : WordTrace (prefixWord ++ tailWord_2185603) baseStart_2185603 baseEnd_2185603 := by
    simpa [prefixWord, tailWord_2185603, baseEnd_2185603] using wordTrace_append hprefix tailTrace_2185603
  have hstable : (prefixWord ++ tailWord_2185603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185603).length < 2 ^ (prefixWord ++ tailWord_2185603).sum := by decide
  have hdescent : baseEnd_2185603 < baseStart_2185603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185656 : List Nat := [2, 1, 2, 1, 2, 2, 1, 5, 1, 4, 2]
def baseStart_2185656 : Nat := 118140960795 + 2185656 * 2 ^ 59
def prefixEnd_2185656 : Nat := 4983230072969 + 3 ^ 40 * 2185656 * 2
def baseEnd_2185656 : Nat := 1122292073383405844548357

theorem tailTrace_2185656 : CollatzResearch.WordTrace tailWord_2185656 prefixEnd_2185656 1122292073383405844548357 := by
  unfold tailWord_2185656
  simp only [CollatzResearch.WordTrace]
  refine ⟨39858711684874533585772411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53144948913166044781029881 39858711684874533585772411)
  ·
    refine ⟨59788067527311800378658617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39858711684874533585772411 59788067527311800378658617)
    ·
      refine ⟨44841050645483850283993963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59788067527311800378658617 44841050645483850283993963)
      ·
        refine ⟨67261575968225775425990945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44841050645483850283993963 67261575968225775425990945)
        ·
          refine ⟨50446181976169331569493209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67261575968225775425990945 50446181976169331569493209)
          ·
            refine ⟨37834636482126998677119907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50446181976169331569493209 37834636482126998677119907)
            ·
              refine ⟨56751954723190498015679861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37834636482126998677119907 56751954723190498015679861)
              ·
                refine ⟨5320495755299109188969987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56751954723190498015679861 5320495755299109188969987)
                ·
                  refine ⟨7980743632948663783454981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5320495755299109188969987 7980743632948663783454981)
                  ·
                    refine ⟨1496389431177874459397809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7980743632948663783454981 1496389431177874459397809)
                    ·
                      refine ⟨1122292073383405844548357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1496389431177874459397809 1122292073383405844548357)
                      ·
                        rfl

theorem cell23_2185656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 1, 4, 2].length) (baseStart_2185656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185656 prefixEnd_2185656 := by exact prefixLift 2185656
  have htrace : WordTrace (prefixWord ++ tailWord_2185656) baseStart_2185656 baseEnd_2185656 := by
    simpa [prefixWord, tailWord_2185656, baseEnd_2185656] using wordTrace_append hprefix tailTrace_2185656
  have hstable : (prefixWord ++ tailWord_2185656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185656).length < 2 ^ (prefixWord ++ tailWord_2185656).sum := by decide
  have hdescent : baseEnd_2185656 < baseStart_2185656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185660 : List Nat := [2, 2, 2, 4, 1, 1, 3, 2, 1, 3, 2]
def baseStart_2185660 : Nat := 118140960795 + 2185660 * 2 ^ 59
def prefixEnd_2185660 : Nat := 4983230072969 + 3 ^ 40 * 2185660 * 2
def baseEnd_2185660 : Nat := 1122294127306023828898339

theorem tailTrace_2185660 : CollatzResearch.WordTrace tailWord_2185660 prefixEnd_2185660 1122294127306023828898339 := by
  unfold tailWord_2185660
  simp only [CollatzResearch.WordTrace]
  refine ⟨39858784630867287927345217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53145046174489717236460289 39858784630867287927345217)
  ·
    refine ⟨29894088473150465945508913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39858784630867287927345217 29894088473150465945508913)
    ·
      refine ⟨22420566354862849459131685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29894088473150465945508913 22420566354862849459131685)
      ·
        refine ⟨4203856191536784273587191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22420566354862849459131685 4203856191536784273587191)
        ·
          refine ⟨6305784287305176410380787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4203856191536784273587191 6305784287305176410380787)
          ·
            refine ⟨9458676430957764615571181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6305784287305176410380787 9458676430957764615571181)
            ·
              refine ⟨3547003661609161730839193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9458676430957764615571181 3547003661609161730839193)
              ·
                refine ⟨2660252746206871298129395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3547003661609161730839193 2660252746206871298129395)
                ·
                  refine ⟨3990379119310306947194093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2660252746206871298129395 3990379119310306947194093)
                  ·
                    refine ⟨1496392169741365105197785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3990379119310306947194093 1496392169741365105197785)
                    ·
                      refine ⟨1122294127306023828898339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1496392169741365105197785 1122294127306023828898339)
                      ·
                        rfl

theorem cell23_2185660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_2185660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185660 prefixEnd_2185660 := by exact prefixLift 2185660
  have htrace : WordTrace (prefixWord ++ tailWord_2185660) baseStart_2185660 baseEnd_2185660 := by
    simpa [prefixWord, tailWord_2185660, baseEnd_2185660] using wordTrace_append hprefix tailTrace_2185660
  have hstable : (prefixWord ++ tailWord_2185660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185660).length < 2 ^ (prefixWord ++ tailWord_2185660).sum := by decide
  have hdescent : baseEnd_2185660 < baseStart_2185660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185690 : List Nat := [3, 1, 1, 2, 3, 1, 4, 2, 2, 2, 2]
def baseStart_2185690 : Nat := 118140960795 + 2185690 * 2 ^ 59
def prefixEnd_2185690 : Nat := 4983230072969 + 3 ^ 40 * 2185690 * 2
def baseEnd_2185690 : Nat := 1122309531725658711523201

theorem tailTrace_2185690 : CollatzResearch.WordTrace tailWord_2185690 prefixEnd_2185690 1122309531725658711523201 := by
  unfold tailWord_2185690
  simp only [CollatzResearch.WordTrace]
  refine ⟨19929665862906472744570631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53145775634417260652188349 19929665862906472744570631)
  ·
    refine ⟨29894498794359709116855947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19929665862906472744570631 29894498794359709116855947)
    ·
      refine ⟨44841748191539563675283921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29894498794359709116855947 44841748191539563675283921)
      ·
        refine ⟨33631311143654672756462941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44841748191539563675283921 33631311143654672756462941)
        ·
          refine ⟨12611741678870502283673603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33631311143654672756462941 12611741678870502283673603)
          ·
            refine ⟨18917612518305753425510405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12611741678870502283673603 18917612518305753425510405)
            ·
              refine ⟨3547052347182328767283201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18917612518305753425510405 3547052347182328767283201)
              ·
                refine ⟨2660289260386746575462401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3547052347182328767283201 2660289260386746575462401)
                ·
                  refine ⟨1995216945290059931596801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2660289260386746575462401 1995216945290059931596801)
                  ·
                    refine ⟨1496412708967544948697601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1995216945290059931596801 1496412708967544948697601)
                    ·
                      refine ⟨1122309531725658711523201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1496412708967544948697601 1122309531725658711523201)
                      ·
                        rfl

theorem cell23_2185690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 2, 2, 2].length) (baseStart_2185690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185690 prefixEnd_2185690 := by exact prefixLift 2185690
  have htrace : WordTrace (prefixWord ++ tailWord_2185690) baseStart_2185690 baseEnd_2185690 := by
    simpa [prefixWord, tailWord_2185690, baseEnd_2185690] using wordTrace_append hprefix tailTrace_2185690
  have hstable : (prefixWord ++ tailWord_2185690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185690).length < 2 ^ (prefixWord ++ tailWord_2185690).sum := by decide
  have hdescent : baseEnd_2185690 < baseStart_2185690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185696 : List Nat := [2, 1, 1, 3, 1, 1, 5, 4, 5]
def baseStart_2185696 : Nat := 118140960795 + 2185696 * 2 ^ 59
def prefixEnd_2185696 : Nat := 4983230072969 + 3 ^ 40 * 2185696 * 2
def baseEnd_2185696 : Nat := 124701401401065076449797

theorem tailTrace_2185696 : CollatzResearch.WordTrace tailWord_2185696 prefixEnd_2185696 124701401401065076449797 := by
  unfold tailWord_2185696
  simp only [CollatzResearch.WordTrace]
  refine ⟨39859441144802077001500471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53145921526402769335333961 39859441144802077001500471)
  ·
    refine ⟨59789161717203115502250707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39859441144802077001500471 59789161717203115502250707)
    ·
      refine ⟨89683742575804673253376061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59789161717203115502250707 89683742575804673253376061)
      ·
        refine ⟨33631403465926752470016023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89683742575804673253376061 33631403465926752470016023)
        ·
          refine ⟨50447105198890128705024035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33631403465926752470016023 50447105198890128705024035)
          ·
            refine ⟨75670657798335193057536053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50447105198890128705024035 75670657798335193057536053)
            ·
              refine ⟨7094124168593924349144005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75670657798335193057536053 7094124168593924349144005)
              ·
                refine ⟨1330148281611360815464501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7094124168593924349144005 1330148281611360815464501)
                ·
                  refine ⟨124701401401065076449797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1330148281611360815464501 124701401401065076449797)
                  ·
                    rfl

theorem cell23_2185696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 4, 5].length) (baseStart_2185696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185696 prefixEnd_2185696 := by exact prefixLift 2185696
  have htrace : WordTrace (prefixWord ++ tailWord_2185696) baseStart_2185696 baseEnd_2185696 := by
    simpa [prefixWord, tailWord_2185696, baseEnd_2185696] using wordTrace_append hprefix tailTrace_2185696
  have hstable : (prefixWord ++ tailWord_2185696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185696).length < 2 ^ (prefixWord ++ tailWord_2185696).sum := by decide
  have hdescent : baseEnd_2185696 < baseStart_2185696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185706 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 1, 5, 3]
def baseStart_2185706 : Nat := 118140960795 + 2185706 * 2 ^ 59
def prefixEnd_2185706 : Nat := 4983230072969 + 3 ^ 40 * 2185706 * 2
def baseEnd_2185706 : Nat := 1122317747416130648923127

theorem tailTrace_2185706 : CollatzResearch.WordTrace tailWord_2185706 prefixEnd_2185706 1122317747416130648923127 := by
  unfold tailWord_2185706
  simp only [CollatzResearch.WordTrace]
  refine ⟨19929811754891981427716243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53146164679711950473909981 19929811754891981427716243)
  ·
    refine ⟨29894717632337972141574365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19929811754891981427716243 29894717632337972141574365)
    ·
      refine ⟨11210519112126739553090387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29894717632337972141574365 11210519112126739553090387)
      ·
        refine ⟨16815778668190109329635581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11210519112126739553090387 16815778668190109329635581)
        ·
          refine ⟨6305917000571290998613343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16815778668190109329635581 6305917000571290998613343)
          ·
            refine ⟨9458875500856936497920015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6305917000571290998613343 9458875500856936497920015)
            ·
              refine ⟨14188313251285404746880023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9458875500856936497920015 14188313251285404746880023)
              ·
                refine ⟨21282469876928107120320035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14188313251285404746880023 21282469876928107120320035)
                ·
                  refine ⟨31923704815392160680480053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21282469876928107120320035 31923704815392160680480053)
                  ·
                    refine ⟨2992847326443015063795005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31923704815392160680480053 2992847326443015063795005)
                    ·
                      refine ⟨1122317747416130648923127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2992847326443015063795005 1122317747416130648923127)
                      ·
                        rfl

theorem cell23_2185706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_2185706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185706 prefixEnd_2185706 := by exact prefixLift 2185706
  have htrace : WordTrace (prefixWord ++ tailWord_2185706) baseStart_2185706 baseEnd_2185706 := by
    simpa [prefixWord, tailWord_2185706, baseEnd_2185706] using wordTrace_append hprefix tailTrace_2185706
  have hstable : (prefixWord ++ tailWord_2185706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185706).length < 2 ^ (prefixWord ++ tailWord_2185706).sum := by decide
  have hdescent : baseEnd_2185706 < baseStart_2185706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185741 : List Nat := [1, 7, 1, 1, 1, 3, 1, 2, 2, 2, 2]
def baseStart_2185741 : Nat := 118140960795 + 2185741 * 2 ^ 59
def prefixEnd_2185741 : Nat := 4983230072969 + 3 ^ 40 * 2185741 * 2
def baseEnd_2185741 : Nat := 1122335719239038011985467

theorem tailTrace_2185741 : CollatzResearch.WordTrace tailWord_2185741 prefixEnd_2185741 1122335719239038011985467 := by
  unfold tailWord_2185741
  simp only [CollatzResearch.WordTrace]
  refine ⟨79720523574441126688389077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53147015716294084458926051 79720523574441126688389077)
  ·
    refine ⟨1868449771275963906759119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 79720523574441126688389077 1868449771275963906759119)
    ·
      refine ⟨2802674656913945860138679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1868449771275963906759119 2802674656913945860138679)
      ·
        refine ⟨4204011985370918790208019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2802674656913945860138679 4204011985370918790208019)
        ·
          refine ⟨6306017978056378185312029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4204011985370918790208019 6306017978056378185312029)
          ·
            refine ⟨2364756741771141819492011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6306017978056378185312029 2364756741771141819492011)
            ·
              refine ⟨3547135112656712729238017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2364756741771141819492011 3547135112656712729238017)
              ·
                refine ⟨2660351334492534546928513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3547135112656712729238017 2660351334492534546928513)
                ·
                  refine ⟨1995263500869400910196385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2660351334492534546928513 1995263500869400910196385)
                  ·
                    refine ⟨1496447625652050682647289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1995263500869400910196385 1496447625652050682647289)
                    ·
                      refine ⟨1122335719239038011985467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1496447625652050682647289 1122335719239038011985467)
                      ·
                        rfl

theorem cell23_2185741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_2185741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185741 prefixEnd_2185741 := by exact prefixLift 2185741
  have htrace : WordTrace (prefixWord ++ tailWord_2185741) baseStart_2185741 baseEnd_2185741 := by
    simpa [prefixWord, tailWord_2185741, baseEnd_2185741] using wordTrace_append hprefix tailTrace_2185741
  have hstable : (prefixWord ++ tailWord_2185741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185741).length < 2 ^ (prefixWord ++ tailWord_2185741).sum := by decide
  have hdescent : baseEnd_2185741 < baseStart_2185741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185759 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 6]
def baseStart_2185759 : Nat := 118140960795 + 2185759 * 2 ^ 59
def prefixEnd_2185759 : Nat := 4983230072969 + 3 ^ 40 * 2185759 * 2
def baseEnd_2185759 : Nat := 1122344961890818941560383

theorem tailTrace_2185759 : CollatzResearch.WordTrace tailWord_2185759 prefixEnd_2185759 1122344961890818941560383 := by
  unfold tailWord_2185759
  simp only [CollatzResearch.WordTrace]
  refine ⟨79721180088375915762544331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53147453392250610508362887 79721180088375915762544331)
  ·
    refine ⟨119581770132563873643816497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79721180088375915762544331 119581770132563873643816497)
    ·
      refine ⟨89686327599422905232862373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119581770132563873643816497 89686327599422905232862373)
      ·
        refine ⟨16816186424891794731161695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89686327599422905232862373 16816186424891794731161695)
        ·
          refine ⟨25224279637337692096742543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16816186424891794731161695 25224279637337692096742543)
          ·
            refine ⟨37836419456006538145113815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25224279637337692096742543 37836419456006538145113815)
            ·
              refine ⟨56754629184009807217670723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37836419456006538145113815 56754629184009807217670723)
              ·
                refine ⟨85131943776014710826506085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56754629184009807217670723 85131943776014710826506085)
                ·
                  refine ⟨15962239458002758279969891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85131943776014710826506085 15962239458002758279969891)
                  ·
                    refine ⟨23943359187004137419954837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15962239458002758279969891 23943359187004137419954837)
                    ·
                      refine ⟨1122344961890818941560383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23943359187004137419954837 1122344961890818941560383)
                      ·
                        rfl

theorem cell23_2185759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_2185759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185759 prefixEnd_2185759 := by exact prefixLift 2185759
  have htrace : WordTrace (prefixWord ++ tailWord_2185759) baseStart_2185759 baseEnd_2185759 := by
    simpa [prefixWord, tailWord_2185759, baseEnd_2185759] using wordTrace_append hprefix tailTrace_2185759
  have hstable : (prefixWord ++ tailWord_2185759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185759).length < 2 ^ (prefixWord ++ tailWord_2185759).sum := by decide
  have hdescent : baseEnd_2185759 < baseStart_2185759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185763 : List Nat := [1, 1, 1, 4, 4, 1, 2, 1, 2, 4, 2]
def baseStart_2185763 : Nat := 118140960795 + 2185763 * 2 ^ 59
def prefixEnd_2185763 : Nat := 4983230072969 + 3 ^ 40 * 2185763 * 2
def baseEnd_2185763 : Nat := 1122347015813436925910365

theorem tailTrace_2185763 : CollatzResearch.WordTrace tailWord_2185763 prefixEnd_2185763 1122347015813436925910365 := by
  unfold tailWord_2185763
  simp only [CollatzResearch.WordTrace]
  refine ⟨79721325980361424445689943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53147550653574282963793295 79721325980361424445689943)
  ·
    refine ⟨119581988970542136668534915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79721325980361424445689943 119581988970542136668534915)
    ·
      refine ⟨179372983455813205002802373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119581988970542136668534915 179372983455813205002802373)
      ·
        refine ⟨33632434397964975938025445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 179372983455813205002802373 33632434397964975938025445)
        ·
          refine ⟨6306081449618432988379771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33632434397964975938025445 6306081449618432988379771)
          ·
            refine ⟨9459122174427649482569657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6306081449618432988379771 9459122174427649482569657)
            ·
              refine ⟨7094341630820737111927243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9459122174427649482569657 7094341630820737111927243)
              ·
                refine ⟨10641512446231105667890865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7094341630820737111927243 10641512446231105667890865)
                ·
                  refine ⟨7981134334673329250918149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10641512446231105667890865 7981134334673329250918149)
                  ·
                    refine ⟨1496462687751249234547153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7981134334673329250918149 1496462687751249234547153)
                    ·
                      refine ⟨1122347015813436925910365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1496462687751249234547153 1122347015813436925910365)
                      ·
                        rfl

theorem cell23_2185763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 4, 2].length) (baseStart_2185763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185763 prefixEnd_2185763 := by exact prefixLift 2185763
  have htrace : WordTrace (prefixWord ++ tailWord_2185763) baseStart_2185763 baseEnd_2185763 := by
    simpa [prefixWord, tailWord_2185763, baseEnd_2185763] using wordTrace_append hprefix tailTrace_2185763
  have hstable : (prefixWord ++ tailWord_2185763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185763).length < 2 ^ (prefixWord ++ tailWord_2185763).sum := by decide
  have hdescent : baseEnd_2185763 < baseStart_2185763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185903 : List Nat := [1, 1, 2, 1, 2, 5, 2, 2, 1, 3, 3]
def baseStart_2185903 : Nat := 118140960795 + 2185903 * 2 ^ 59
def prefixEnd_2185903 : Nat := 4983230072969 + 3 ^ 40 * 2185903 * 2
def baseEnd_2185903 : Nat := 1122418903105066378159721

theorem tailTrace_2185903 : CollatzResearch.WordTrace tailWord_2185903 prefixEnd_2185903 1122418903105066378159721 := by
  unfold tailWord_2185903
  simp only [CollatzResearch.WordTrace]
  refine ⟨79726432199854228355786363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53150954799902818903857575 79726432199854228355786363)
  ·
    refine ⟨119589648299781342533679545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79726432199854228355786363 119589648299781342533679545)
    ·
      refine ⟨89692236224836006900259659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119589648299781342533679545 89692236224836006900259659)
      ·
        refine ⟨134538354337254010350389489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89692236224836006900259659 134538354337254010350389489)
        ·
          refine ⟨100903765752940507762792117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134538354337254010350389489 100903765752940507762792117)
          ·
            refine ⟨9459728039338172602761761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100903765752940507762792117 9459728039338172602761761)
            ·
              refine ⟨7094796029503629452071321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9459728039338172602761761 7094796029503629452071321)
              ·
                refine ⟨5321097022127722089053491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7094796029503629452071321 5321097022127722089053491)
                ·
                  refine ⟨7981645533191583133580237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5321097022127722089053491 7981645533191583133580237)
                  ·
                    refine ⟨2993117074946843675092589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7981645533191583133580237 2993117074946843675092589)
                    ·
                      refine ⟨1122418903105066378159721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2993117074946843675092589 1122418903105066378159721)
                      ·
                        rfl

theorem cell23_2185903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 3, 3].length) (baseStart_2185903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185903 prefixEnd_2185903 := by exact prefixLift 2185903
  have htrace : WordTrace (prefixWord ++ tailWord_2185903) baseStart_2185903 baseEnd_2185903 := by
    simpa [prefixWord, tailWord_2185903, baseEnd_2185903] using wordTrace_append hprefix tailTrace_2185903
  have hstable : (prefixWord ++ tailWord_2185903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185903).length < 2 ^ (prefixWord ++ tailWord_2185903).sum := by decide
  have hdescent : baseEnd_2185903 < baseStart_2185903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185907 : List Nat := [1, 1, 1, 2, 3, 6, 2, 1, 1, 2, 3]
def baseStart_2185907 : Nat := 118140960795 + 2185907 * 2 ^ 59
def prefixEnd_2185907 : Nat := 4983230072969 + 3 ^ 40 * 2185907 * 2
def baseEnd_2185907 : Nat := 1122420957027684362509703

theorem tailTrace_2185907 : CollatzResearch.WordTrace tailWord_2185907 prefixEnd_2185907 1122420957027684362509703 := by
  unfold tailWord_2185907
  simp only [CollatzResearch.WordTrace]
  refine ⟨79726578091839737038931975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53151052061226491359287983 79726578091839737038931975)
  ·
    refine ⟨119589867137759605558397963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79726578091839737038931975 119589867137759605558397963)
    ·
      refine ⟨179384800706639408337596945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119589867137759605558397963 179384800706639408337596945)
      ·
        refine ⟨134538600529979556253197709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179384800706639408337596945 134538600529979556253197709)
        ·
          refine ⟨50451975198742333594949141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134538600529979556253197709 50451975198742333594949141)
          ·
            refine ⟨2364936337441046887263241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 50451975198742333594949141 2364936337441046887263241)
            ·
              refine ⟨1773702253080785165447431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2364936337441046887263241 1773702253080785165447431)
              ·
                refine ⟨2660553379621177748171147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1773702253080785165447431 2660553379621177748171147)
                ·
                  refine ⟨3990830069431766622256721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2660553379621177748171147 3990830069431766622256721)
                  ·
                    refine ⟨2993122552073824966692541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3990830069431766622256721 2993122552073824966692541)
                    ·
                      refine ⟨1122420957027684362509703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2993122552073824966692541 1122420957027684362509703)
                      ·
                        rfl

theorem cell23_2185907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 1, 2, 3].length) (baseStart_2185907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185907 prefixEnd_2185907 := by exact prefixLift 2185907
  have htrace : WordTrace (prefixWord ++ tailWord_2185907) baseStart_2185907 baseEnd_2185907 := by
    simpa [prefixWord, tailWord_2185907, baseEnd_2185907] using wordTrace_append hprefix tailTrace_2185907
  have hstable : (prefixWord ++ tailWord_2185907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185907).length < 2 ^ (prefixWord ++ tailWord_2185907).sum := by decide
  have hdescent : baseEnd_2185907 < baseStart_2185907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185910 : List Nat := [5, 1, 3, 1, 2, 1, 10]
def baseStart_2185910 : Nat := 118140960795 + 2185910 * 2 ^ 59
def prefixEnd_2185910 : Nat := 4983230072969 + 3 ^ 40 * 2185910 * 2
def baseEnd_2185910 : Nat := 13857067869995652478669

theorem tailTrace_2185910 : CollatzResearch.WordTrace tailWord_2185910 prefixEnd_2185910 13857067869995652478669 := by
  unfold tailWord_2185910
  simp only [CollatzResearch.WordTrace]
  refine ⟨4982917969426804284455699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53151125007219245700860789 4982917969426804284455699)
  ·
    refine ⟨7474376954140206426683549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4982917969426804284455699 7474376954140206426683549)
    ·
      refine ⟨2802891357802577410006331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7474376954140206426683549 2802891357802577410006331)
      ·
        refine ⟨4204337036703866115009497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2802891357802577410006331 4204337036703866115009497)
        ·
          refine ⟨3153252777527899586257123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4204337036703866115009497 3153252777527899586257123)
          ·
            refine ⟨4729879166291849379385685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3153252777527899586257123 4729879166291849379385685)
            ·
              refine ⟨13857067869995652478669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4729879166291849379385685 13857067869995652478669)
              ·
                rfl

theorem cell23_2185910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 10].length) (baseStart_2185910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185910 prefixEnd_2185910 := by exact prefixLift 2185910
  have htrace : WordTrace (prefixWord ++ tailWord_2185910) baseStart_2185910 baseEnd_2185910 := by
    simpa [prefixWord, tailWord_2185910, baseEnd_2185910] using wordTrace_append hprefix tailTrace_2185910
  have hstable : (prefixWord ++ tailWord_2185910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185910).length < 2 ^ (prefixWord ++ tailWord_2185910).sum := by decide
  have hdescent : baseEnd_2185910 < baseStart_2185910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185920 : List Nat := [2, 1, 1, 2, 4, 3, 1, 1, 4, 1, 3]
def baseStart_2185920 : Nat := 118140960795 + 2185920 * 2 ^ 59
def prefixEnd_2185920 : Nat := 4983230072969 + 3 ^ 40 * 2185920 * 2
def baseEnd_2185920 : Nat := 1122427632276192811647143

theorem tailTrace_2185920 : CollatzResearch.WordTrace tailWord_2185920 prefixEnd_2185920 1122427632276192811647143 := by
  unfold tailWord_2185920
  simp only [CollatzResearch.WordTrace]
  refine ⟨39863526120396320129577607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53151368160528426839436809 39863526120396320129577607)
  ·
    refine ⟨59795289180594480194366411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39863526120396320129577607 59795289180594480194366411)
    ·
      refine ⟨89692933770891720291549617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59795289180594480194366411 89692933770891720291549617)
      ·
        refine ⟨67269700328168790218662213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89692933770891720291549617 67269700328168790218662213)
        ·
          refine ⟨12613068811531648165999165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67269700328168790218662213 12613068811531648165999165)
          ·
            refine ⟨4729900804324368062249687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12613068811531648165999165 4729900804324368062249687)
            ·
              refine ⟨7094851206486552093374531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4729900804324368062249687 7094851206486552093374531)
              ·
                refine ⟨10642276809729828140061797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7094851206486552093374531 10642276809729828140061797)
                ·
                  refine ⟨1995426901824342776261587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10642276809729828140061797 1995426901824342776261587)
                  ·
                    refine ⟨2993140352736514164392381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1995426901824342776261587 2993140352736514164392381)
                    ·
                      refine ⟨1122427632276192811647143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2993140352736514164392381 1122427632276192811647143)
                      ·
                        rfl

theorem cell23_2185920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 4, 1, 3].length) (baseStart_2185920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185920 prefixEnd_2185920 := by exact prefixLift 2185920
  have htrace : WordTrace (prefixWord ++ tailWord_2185920) baseStart_2185920 baseEnd_2185920 := by
    simpa [prefixWord, tailWord_2185920, baseEnd_2185920] using wordTrace_append hprefix tailTrace_2185920
  have hstable : (prefixWord ++ tailWord_2185920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185920).length < 2 ^ (prefixWord ++ tailWord_2185920).sum := by decide
  have hdescent : baseEnd_2185920 < baseStart_2185920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185921 : List Nat := [1, 2, 6, 2, 1, 1, 2, 1, 3, 2, 2]
def baseStart_2185921 : Nat := 118140960795 + 2185921 * 2 ^ 59
def prefixEnd_2185921 : Nat := 4983230072969 + 3 ^ 40 * 2185921 * 2
def baseEnd_2185921 : Nat := 1122428145756847307734639

theorem tailTrace_2185921 : CollatzResearch.WordTrace tailWord_2185921 prefixEnd_2185921 1122428145756847307734639 := by
  unfold tailWord_2185921
  simp only [CollatzResearch.WordTrace]
  refine ⟨79727088713789017429941617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53151392475859344953294411 79727088713789017429941617)
  ·
    refine ⟨59795316535341763072456213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79727088713789017429941617 59795316535341763072456213)
    ·
      refine ⟨2802905462594145144021385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 59795316535341763072456213 2802905462594145144021385)
      ·
        refine ⟨2102179096945608858016039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2802905462594145144021385 2102179096945608858016039)
        ·
          refine ⟨3153268645418413287024059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2102179096945608858016039 3153268645418413287024059)
          ·
            refine ⟨4729902968127619930536089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3153268645418413287024059 4729902968127619930536089)
            ·
              refine ⟨3547427226095714947902067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4729902968127619930536089 3547427226095714947902067)
              ·
                refine ⟨5321140839143572421853101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3547427226095714947902067 5321140839143572421853101)
                ·
                  refine ⟨1995427814678839658194913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5321140839143572421853101 1995427814678839658194913)
                  ·
                    refine ⟨1496570861009129743646185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1995427814678839658194913 1496570861009129743646185)
                    ·
                      refine ⟨1122428145756847307734639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1496570861009129743646185 1122428145756847307734639)
                      ·
                        rfl

theorem cell23_2185921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_2185921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185921 prefixEnd_2185921 := by exact prefixLift 2185921
  have htrace : WordTrace (prefixWord ++ tailWord_2185921) baseStart_2185921 baseEnd_2185921 := by
    simpa [prefixWord, tailWord_2185921, baseEnd_2185921] using wordTrace_append hprefix tailTrace_2185921
  have hstable : (prefixWord ++ tailWord_2185921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185921).length < 2 ^ (prefixWord ++ tailWord_2185921).sum := by decide
  have hdescent : baseEnd_2185921 < baseStart_2185921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185937 : List Nat := [1, 2, 2, 1, 2, 3, 5, 1, 2, 1, 3]
def baseStart_2185937 : Nat := 118140960795 + 2185937 * 2 ^ 59
def prefixEnd_2185937 : Nat := 4983230072969 + 3 ^ 40 * 2185937 * 2
def baseEnd_2185937 : Nat := 1122436361447319245134565

theorem tailTrace_2185937 : CollatzResearch.WordTrace tailWord_2185937 prefixEnd_2185937 1122436361447319245134565 := by
  unfold tailWord_2185937
  simp only [CollatzResearch.WordTrace]
  refine ⟨79727672281731052162524065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53151781521154034775016043 79727672281731052162524065)
  ·
    refine ⟨59795754211298289121893049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79727672281731052162524065 59795754211298289121893049)
    ·
      refine ⟨44846815658473716841419787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59795754211298289121893049 44846815658473716841419787)
      ·
        refine ⟨67270223487710575262129681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44846815658473716841419787 67270223487710575262129681)
        ·
          refine ⟨50452667615782931446597261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67270223487710575262129681 50452667615782931446597261)
          ·
            refine ⟨18919750355918599292473973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50452667615782931446597261 18919750355918599292473973)
            ·
              refine ⟨1773726595867368683669435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18919750355918599292473973 1773726595867368683669435)
              ·
                refine ⟨2660589893801053025504153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1773726595867368683669435 2660589893801053025504153)
                ·
                  refine ⟨1995442420350789769128115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2660589893801053025504153 1995442420350789769128115)
                  ·
                    refine ⟨2993163630526184653692173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1995442420350789769128115 2993163630526184653692173)
                    ·
                      refine ⟨1122436361447319245134565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2993163630526184653692173 1122436361447319245134565)
                      ·
                        rfl

theorem cell23_2185937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 2, 1, 3].length) (baseStart_2185937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185937 prefixEnd_2185937 := by exact prefixLift 2185937
  have htrace : WordTrace (prefixWord ++ tailWord_2185937) baseStart_2185937 baseEnd_2185937 := by
    simpa [prefixWord, tailWord_2185937, baseEnd_2185937] using wordTrace_append hprefix tailTrace_2185937
  have hstable : (prefixWord ++ tailWord_2185937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185937).length < 2 ^ (prefixWord ++ tailWord_2185937).sum := by decide
  have hdescent : baseEnd_2185937 < baseStart_2185937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185976 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 1, 2, 7]
def baseStart_2185976 : Nat := 118140960795 + 2185976 * 2 ^ 59
def prefixEnd_2185976 : Nat := 4983230072969 + 3 ^ 40 * 2185976 * 2
def baseEnd_2185976 : Nat := 1122456387192844592546885

theorem tailTrace_2185976 : CollatzResearch.WordTrace tailWord_2185976 prefixEnd_2185976 1122456387192844592546885 := by
  unfold tailWord_2185976
  simp only [CollatzResearch.WordTrace]
  refine ⟨39864547364294880911596891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53152729819059841215462521 39864547364294880911596891)
  ·
    refine ⟨59796821046442321367395337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39864547364294880911596891 59796821046442321367395337)
    ·
      refine ⟨44847615784831741025546503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59796821046442321367395337 44847615784831741025546503)
      ·
        refine ⟨67271423677247611538319755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44847615784831741025546503 67271423677247611538319755)
        ·
          refine ⟨100907135515871417307479633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67271423677247611538319755 100907135515871417307479633)
          ·
            refine ⟨75680351636903562980609725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100907135515871417307479633 75680351636903562980609725)
            ·
              refine ⟨28380131863838836117728647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75680351636903562980609725 28380131863838836117728647)
              ·
                refine ⟨42570197795758254176592971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28380131863838836117728647 42570197795758254176592971)
                ·
                  refine ⟨63855296693637381264889457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42570197795758254176592971 63855296693637381264889457)
                  ·
                    refine ⟨47891472520228035948667093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 63855296693637381264889457 47891472520228035948667093)
                    ·
                      refine ⟨1122456387192844592546885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 47891472520228035948667093 1122456387192844592546885)
                      ·
                        rfl

theorem cell23_2185976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_2185976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185976 prefixEnd_2185976 := by exact prefixLift 2185976
  have htrace : WordTrace (prefixWord ++ tailWord_2185976) baseStart_2185976 baseEnd_2185976 := by
    simpa [prefixWord, tailWord_2185976, baseEnd_2185976] using wordTrace_append hprefix tailTrace_2185976
  have hstable : (prefixWord ++ tailWord_2185976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185976).length < 2 ^ (prefixWord ++ tailWord_2185976).sum := by decide
  have hdescent : baseEnd_2185976 < baseStart_2185976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2185993 : List Nat := [1, 2, 1, 1, 3, 2, 2, 3, 2, 3, 3]
def baseStart_2185993 : Nat := 118140960795 + 2185993 * 2 ^ 59
def prefixEnd_2185993 : Nat := 4983230072969 + 3 ^ 40 * 2185993 * 2
def baseEnd_2185993 : Nat := 1122465116363971026034307

theorem tailTrace_2185993 : CollatzResearch.WordTrace tailWord_2185993 prefixEnd_2185993 1122465116363971026034307 := by
  unfold tailWord_2185993
  simp only [CollatzResearch.WordTrace]
  refine ⟨79729714769528173726562633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53153143179685449151041755 79729714769528173726562633)
  ·
    refine ⟨59797286077146130294921975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79729714769528173726562633 59797286077146130294921975)
    ·
      refine ⟨89695929115719195442382963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59797286077146130294921975 89695929115719195442382963)
      ·
        refine ⟨134543893673578793163574445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89695929115719195442382963 134543893673578793163574445)
        ·
          refine ⟨50453960127592047436340417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134543893673578793163574445 50453960127592047436340417)
          ·
            refine ⟨37840470095694035577255313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50453960127592047436340417 37840470095694035577255313)
            ·
              refine ⟨28380352571770526682941485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37840470095694035577255313 28380352571770526682941485)
              ·
                refine ⟨10642632214413947506103057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28380352571770526682941485 10642632214413947506103057)
                ·
                  refine ⟨7981974160810460629577293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10642632214413947506103057 7981974160810460629577293)
                  ·
                    refine ⟨2993240310303922736091485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7981974160810460629577293 2993240310303922736091485)
                    ·
                      refine ⟨1122465116363971026034307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2993240310303922736091485 1122465116363971026034307)
                      ·
                        rfl

theorem cell23_2185993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 3, 3].length) (baseStart_2185993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2185993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2185993 prefixEnd_2185993 := by exact prefixLift 2185993
  have htrace : WordTrace (prefixWord ++ tailWord_2185993) baseStart_2185993 baseEnd_2185993 := by
    simpa [prefixWord, tailWord_2185993, baseEnd_2185993] using wordTrace_append hprefix tailTrace_2185993
  have hstable : (prefixWord ++ tailWord_2185993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2185993).length < 2 ^ (prefixWord ++ tailWord_2185993).sum := by decide
  have hdescent : baseEnd_2185993 < baseStart_2185993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2185993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186060 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 5, 4]
def baseStart_2186060 : Nat := 118140960795 + 2186060 * 2 ^ 59
def prefixEnd_2186060 : Nat := 4983230072969 + 3 ^ 40 * 2186060 * 2
def baseEnd_2186060 : Nat := 374166506522607421298833

theorem tailTrace_2186060 : CollatzResearch.WordTrace tailWord_2186060 prefixEnd_2186060 374166506522607421298833 := by
  unfold tailWord_2186060
  simp only [CollatzResearch.WordTrace]
  refine ⟨39866079230142722084625817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53154772306856962779501089 39866079230142722084625817)
  ·
    refine ⟨29899559422607041563469363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39866079230142722084625817 29899559422607041563469363)
    ·
      refine ⟨44849339133910562345204045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29899559422607041563469363 44849339133910562345204045)
      ·
        refine ⟨16818502175216460879451517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44849339133910562345204045 16818502175216460879451517)
        ·
          refine ⟨6306938315706172829794319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16818502175216460879451517 6306938315706172829794319)
          ·
            refine ⟨9460407473559259244691479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6306938315706172829794319 9460407473559259244691479)
            ·
              refine ⟨14190611210338888867037219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9460407473559259244691479 14190611210338888867037219)
              ·
                refine ⟨21285916815508333300555829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14190611210338888867037219 21285916815508333300555829)
                ·
                  refine ⟨1995554701453906246927109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21285916815508333300555829 1995554701453906246927109)
                  ·
                    refine ⟨374166506522607421298833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1995554701453906246927109 374166506522607421298833)
                    ·
                      rfl

theorem cell23_2186060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 5, 4].length) (baseStart_2186060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186060 prefixEnd_2186060 := by exact prefixLift 2186060
  have htrace : WordTrace (prefixWord ++ tailWord_2186060) baseStart_2186060 baseEnd_2186060 := by
    simpa [prefixWord, tailWord_2186060, baseEnd_2186060] using wordTrace_append hprefix tailTrace_2186060
  have hstable : (prefixWord ++ tailWord_2186060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186060).length < 2 ^ (prefixWord ++ tailWord_2186060).sum := by decide
  have hdescent : baseEnd_2186060 < baseStart_2186060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186094 : List Nat := [4, 1, 2, 3, 2, 1, 2, 1, 3, 4]
def baseStart_2186094 : Nat := 118140960795 + 2186094 * 2 ^ 59
def prefixEnd_2186094 : Nat := 4983230072969 + 3 ^ 40 * 2186094 * 2
def baseEnd_2186094 : Nat := 374172325970025043623781

theorem tailTrace_2186094 : CollatzResearch.WordTrace tailWord_2186094 prefixEnd_2186094 374172325970025043623781 := by
  unfold tailWord_2186094
  simp only [CollatzResearch.WordTrace]
  refine ⟨9966674817770283496998667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53155599028108178650659557 9966674817770283496998667)
  ·
    refine ⟨14950012226655425245498001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9966674817770283496998667 14950012226655425245498001)
    ·
      refine ⟨11212509169991568934123501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14950012226655425245498001 11212509169991568934123501)
      ·
        refine ⟨4204690938746838350296313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11212509169991568934123501 4204690938746838350296313)
        ·
          refine ⟨3153518204060128762722235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4204690938746838350296313 3153518204060128762722235)
          ·
            refine ⟨4730277306090193144083353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3153518204060128762722235 4730277306090193144083353)
            ·
              refine ⟨3547707979567644858062515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4730277306090193144083353 3547707979567644858062515)
              ·
                refine ⟨5321561969351467287093773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3547707979567644858062515 5321561969351467287093773)
                ·
                  refine ⟨1995585738506800232660165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5321561969351467287093773 1995585738506800232660165)
                  ·
                    refine ⟨374172325970025043623781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1995585738506800232660165 374172325970025043623781)
                    ·
                      rfl

theorem cell23_2186094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_2186094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186094 prefixEnd_2186094 := by exact prefixLift 2186094
  have htrace : WordTrace (prefixWord ++ tailWord_2186094) baseStart_2186094 baseEnd_2186094 := by
    simpa [prefixWord, tailWord_2186094, baseEnd_2186094] using wordTrace_append hprefix tailTrace_2186094
  have hstable : (prefixWord ++ tailWord_2186094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186094).length < 2 ^ (prefixWord ++ tailWord_2186094).sum := by decide
  have hdescent : baseEnd_2186094 < baseStart_2186094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186103 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 5, 5]
def baseStart_2186103 : Nat := 118140960795 + 2186103 * 2 ^ 59
def prefixEnd_2186103 : Nat := 4983230072969 + 3 ^ 40 * 2186103 * 2
def baseEnd_2186103 : Nat := 374173866411988531886267

theorem tailTrace_2186103 : CollatzResearch.WordTrace tailWord_2186103 prefixEnd_2186103 374173866411988531886267 := by
  unfold tailWord_2186103
  simp only [CollatzResearch.WordTrace]
  refine ⟨79733726799129662513066963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53155817866086441675377975 79733726799129662513066963)
  ·
    refine ⟨119600590198694493769600445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79733726799129662513066963 119600590198694493769600445)
    ·
      refine ⟨44850221324510435163600167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119600590198694493769600445 44850221324510435163600167)
      ·
        refine ⟨67275331986765652745400251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44850221324510435163600167 67275331986765652745400251)
        ·
          refine ⟨100912997980148479118100377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67275331986765652745400251 100912997980148479118100377)
          ·
            refine ⟨75684748485111359338575283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100912997980148479118100377 75684748485111359338575283)
            ·
              refine ⟨113527122727667039007862925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75684748485111359338575283 113527122727667039007862925)
              ·
                refine ⟨42572671022875139627948597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113527122727667039007862925 42572671022875139627948597)
                ·
                  refine ⟨3991187908394544340120181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42572671022875139627948597 3991187908394544340120181)
                  ·
                    refine ⟨374173866411988531886267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3991187908394544340120181 374173866411988531886267)
                    ·
                      rfl

theorem cell23_2186103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 5].length) (baseStart_2186103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186103 prefixEnd_2186103 := by exact prefixLift 2186103
  have htrace : WordTrace (prefixWord ++ tailWord_2186103) baseStart_2186103 baseEnd_2186103 := by
    simpa [prefixWord, tailWord_2186103, baseEnd_2186103] using wordTrace_append hprefix tailTrace_2186103
  have hstable : (prefixWord ++ tailWord_2186103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186103).length < 2 ^ (prefixWord ++ tailWord_2186103).sum := by decide
  have hdescent : baseEnd_2186103 < baseStart_2186103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186117 : List Nat := [1, 3, 1, 1, 3, 3, 2, 2, 3, 1, 3]
def baseStart_2186117 : Nat := 118140960795 + 2186117 * 2 ^ 59
def prefixEnd_2186117 : Nat := 4983230072969 + 3 ^ 40 * 2186117 * 2
def baseEnd_2186117 : Nat := 1122528787965128540883737

theorem tailTrace_2186117 : CollatzResearch.WordTrace tailWord_2186117 prefixEnd_2186117 1122528787965128540883737 := by
  unfold tailWord_2186117
  simp only [CollatzResearch.WordTrace]
  refine ⟨79734237421078942904076605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53156158280719295269384403 79734237421078942904076605)
  ·
    refine ⟨29900339032904603589028727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79734237421078942904076605 29900339032904603589028727)
    ·
      refine ⟨44850508549356905383543091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29900339032904603589028727 44850508549356905383543091)
      ·
        refine ⟨67275762824035358075314637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44850508549356905383543091 67275762824035358075314637)
        ·
          refine ⟨25228411059013259278242989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67275762824035358075314637 25228411059013259278242989)
          ·
            refine ⟨9460654147129972229341121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25228411059013259278242989 9460654147129972229341121)
            ·
              refine ⟨7095490610347479172005841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9460654147129972229341121 7095490610347479172005841)
              ·
                refine ⟨5321617957760609379004381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7095490610347479172005841 5321617957760609379004381)
                ·
                  refine ⟨1995606734160228517126643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5321617957760609379004381 1995606734160228517126643)
                  ·
                    refine ⟨2993410101240342775689965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1995606734160228517126643 2993410101240342775689965)
                    ·
                      refine ⟨1122528787965128540883737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2993410101240342775689965 1122528787965128540883737)
                      ·
                        rfl

theorem cell23_2186117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 3, 1, 3].length) (baseStart_2186117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186117 prefixEnd_2186117 := by exact prefixLift 2186117
  have htrace : WordTrace (prefixWord ++ tailWord_2186117) baseStart_2186117 baseEnd_2186117 := by
    simpa [prefixWord, tailWord_2186117, baseEnd_2186117] using wordTrace_append hprefix tailTrace_2186117
  have hstable : (prefixWord ++ tailWord_2186117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186117).length < 2 ^ (prefixWord ++ tailWord_2186117).sum := by decide
  have hdescent : baseEnd_2186117 < baseStart_2186117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186151 : List Nat := [1, 1, 6, 1, 3, 2, 1, 1, 3, 1, 3]
def baseStart_2186151 : Nat := 118140960795 + 2186151 * 2 ^ 59
def prefixEnd_2186151 : Nat := 4983230072969 + 3 ^ 40 * 2186151 * 2
def baseEnd_2186151 : Nat := 1122546246307381407858581

theorem tailTrace_2186151 : CollatzResearch.WordTrace tailWord_2186151 prefixEnd_2186151 1122546246307381407858581 := by
  unfold tailWord_2186151
  simp only [CollatzResearch.WordTrace]
  refine ⟨79735477502955766710814307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53156985001970511140542871 79735477502955766710814307)
  ·
    refine ⟨119603216254433650066221461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79735477502955766710814307 119603216254433650066221461)
    ·
      refine ⟨5606400761926577346854131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 119603216254433650066221461 5606400761926577346854131)
      ·
        refine ⟨8409601142889866020281197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5606400761926577346854131 8409601142889866020281197)
        ·
          refine ⟨3153600428583699757605449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8409601142889866020281197 3153600428583699757605449)
          ·
            refine ⟨2365200321437774818204087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3153600428583699757605449 2365200321437774818204087)
            ·
              refine ⟨3547800482156662227306131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2365200321437774818204087 3547800482156662227306131)
              ·
                refine ⟨5321700723234993340959197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3547800482156662227306131 5321700723234993340959197)
                ·
                  refine ⟨1995637771213122502859699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5321700723234993340959197 1995637771213122502859699)
                  ·
                    refine ⟨2993456656819683754289549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1995637771213122502859699 2993456656819683754289549)
                    ·
                      refine ⟨1122546246307381407858581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2993456656819683754289549 1122546246307381407858581)
                      ·
                        rfl

theorem cell23_2186151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_2186151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186151 prefixEnd_2186151 := by exact prefixLift 2186151
  have htrace : WordTrace (prefixWord ++ tailWord_2186151) baseStart_2186151 baseEnd_2186151 := by
    simpa [prefixWord, tailWord_2186151, baseEnd_2186151] using wordTrace_append hprefix tailTrace_2186151
  have hstable : (prefixWord ++ tailWord_2186151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186151).length < 2 ^ (prefixWord ++ tailWord_2186151).sum := by decide
  have hdescent : baseEnd_2186151 < baseStart_2186151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186153 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 3, 1, 6]
def baseStart_2186153 : Nat := 118140960795 + 2186153 * 2 ^ 59
def prefixEnd_2186153 : Nat := 4983230072969 + 3 ^ 40 * 2186153 * 2
def baseEnd_2186153 : Nat := 1122547273268690400033571

theorem tailTrace_2186153 : CollatzResearch.WordTrace tailWord_2186153 prefixEnd_2186153 1122547273268690400033571 := by
  unfold tailWord_2186153
  simp only [CollatzResearch.WordTrace]
  refine ⟨79735550448948521052387113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53157033632632347368258075 79735550448948521052387113)
  ·
    refine ⟨59801662836711390789290335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79735550448948521052387113 59801662836711390789290335)
    ·
      refine ⟨89702494255067086183935503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59801662836711390789290335 89702494255067086183935503)
      ·
        refine ⟨134553741382600629275903255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89702494255067086183935503 134553741382600629275903255)
        ·
          refine ⟨201830612073900943913854883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134553741382600629275903255 201830612073900943913854883)
          ·
            refine ⟨302745918110851415870782325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201830612073900943913854883 302745918110851415870782325)
            ·
              refine ⟨28382429822892320237885843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 302745918110851415870782325 28382429822892320237885843)
              ·
                refine ⟨42573644734338480356828765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28382429822892320237885843 42573644734338480356828765)
                ·
                  refine ⟨15965116775376930133810787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42573644734338480356828765 15965116775376930133810787)
                  ·
                    refine ⟨23947675163065395200716181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15965116775376930133810787 23947675163065395200716181)
                    ·
                      refine ⟨1122547273268690400033571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23947675163065395200716181 1122547273268690400033571)
                      ·
                        rfl

theorem cell23_2186153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 1, 6].length) (baseStart_2186153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186153 prefixEnd_2186153 := by exact prefixLift 2186153
  have htrace : WordTrace (prefixWord ++ tailWord_2186153) baseStart_2186153 baseEnd_2186153 := by
    simpa [prefixWord, tailWord_2186153, baseEnd_2186153] using wordTrace_append hprefix tailTrace_2186153
  have hstable : (prefixWord ++ tailWord_2186153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186153).length < 2 ^ (prefixWord ++ tailWord_2186153).sum := by decide
  have hdescent : baseEnd_2186153 < baseStart_2186153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186170 : List Nat := [3, 1, 1, 1, 2, 1, 4, 3, 1, 2, 4]
def baseStart_2186170 : Nat := 118140960795 + 2186170 * 2 ^ 59
def prefixEnd_2186170 : Nat := 4983230072969 + 3 ^ 40 * 2186170 * 2
def baseEnd_2186170 : Nat := 1122556002439816833520993

theorem tailTrace_2186170 : CollatzResearch.WordTrace tailWord_2186170 prefixEnd_2186170 1122556002439816833520993 := by
  unfold tailWord_2186170
  simp only [CollatzResearch.WordTrace]
  refine ⟨19934042622471733238938991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53157446993257955303837309 19934042622471733238938991)
  ·
    refine ⟨29901063933707599858408487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19934042622471733238938991 29901063933707599858408487)
    ·
      refine ⟨44851595900561399787612731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29901063933707599858408487 44851595900561399787612731)
      ·
        refine ⟨67277393850842099681419097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44851595900561399787612731 67277393850842099681419097)
        ·
          refine ⟨50458045388131574761064323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67277393850842099681419097 50458045388131574761064323)
          ·
            refine ⟨75687068082197362141596485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50458045388131574761064323 75687068082197362141596485)
            ·
              refine ⟨14191325265412005401549341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75687068082197362141596485 14191325265412005401549341)
              ·
                refine ⟨5321746974529502025581003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14191325265412005401549341 5321746974529502025581003)
                ·
                  refine ⟨7982620461794253038371505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5321746974529502025581003 7982620461794253038371505)
                  ·
                    refine ⟨5986965346345689778778629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7982620461794253038371505 5986965346345689778778629)
                    ·
                      refine ⟨1122556002439816833520993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5986965346345689778778629 1122556002439816833520993)
                      ·
                        rfl

theorem cell23_2186170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_2186170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186170 prefixEnd_2186170 := by exact prefixLift 2186170
  have htrace : WordTrace (prefixWord ++ tailWord_2186170) baseStart_2186170 baseEnd_2186170 := by
    simpa [prefixWord, tailWord_2186170, baseEnd_2186170] using wordTrace_append hprefix tailTrace_2186170
  have hstable : (prefixWord ++ tailWord_2186170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186170).length < 2 ^ (prefixWord ++ tailWord_2186170).sum := by decide
  have hdescent : baseEnd_2186170 < baseStart_2186170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186174 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2]
def baseStart_2186174 : Nat := 118140960795 + 2186174 * 2 ^ 59
def prefixEnd_2186174 : Nat := 4983230072969 + 3 ^ 40 * 2186174 * 2
def baseEnd_2186174 : Nat := 1122558056362434817870975

theorem tailTrace_2186174 : CollatzResearch.WordTrace tailWord_2186174 prefixEnd_2186174 1122558056362434817870975 := by
  unfold tailWord_2186174
  simp only [CollatzResearch.WordTrace]
  refine ⟨9967039547734055204862697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53157544254581627759267717 9967039547734055204862697)
  ·
    refine ⟨7475279660800541403647023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9967039547734055204862697 7475279660800541403647023)
    ·
      refine ⟨11212919491200812105470535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7475279660800541403647023 11212919491200812105470535)
      ·
        refine ⟨16819379236801218158205803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11212919491200812105470535 16819379236801218158205803)
        ·
          refine ⟨25229068855201827237308705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16819379236801218158205803 25229068855201827237308705)
          ·
            refine ⟨18921801641401370427981529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25229068855201827237308705 18921801641401370427981529)
            ·
              refine ⟨14191351231051027820986147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18921801641401370427981529 14191351231051027820986147)
              ·
                refine ⟨21287026846576541731479221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14191351231051027820986147 21287026846576541731479221)
                ·
                  refine ⟨1995658766866550787326177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21287026846576541731479221 1995658766866550787326177)
                  ·
                    refine ⟨1496744075149913090494633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1995658766866550787326177 1496744075149913090494633)
                    ·
                      refine ⟨1122558056362434817870975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1496744075149913090494633 1122558056362434817870975)
                      ·
                        rfl

theorem cell23_2186174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_2186174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186174 prefixEnd_2186174 := by exact prefixLift 2186174
  have htrace : WordTrace (prefixWord ++ tailWord_2186174) baseStart_2186174 baseEnd_2186174 := by
    simpa [prefixWord, tailWord_2186174, baseEnd_2186174] using wordTrace_append hprefix tailTrace_2186174
  have hstable : (prefixWord ++ tailWord_2186174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186174).length < 2 ^ (prefixWord ++ tailWord_2186174).sum := by decide
  have hdescent : baseEnd_2186174 < baseStart_2186174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186194 : List Nat := [3, 2, 2, 3, 1, 3, 1, 1, 1, 1, 5]
def baseStart_2186194 : Nat := 118140960795 + 2186194 * 2 ^ 59
def prefixEnd_2186194 : Nat := 4983230072969 + 3 ^ 40 * 2186194 * 2
def baseEnd_2186194 : Nat := 1122568325975524739620883

theorem tailTrace_2186194 : CollatzResearch.WordTrace tailWord_2186194 prefixEnd_2186194 1122568325975524739620883 := by
  unfold tailWord_2186194
  simp only [CollatzResearch.WordTrace]
  refine ⟨19934261460449996263657409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53158030561199990036419757 19934261460449996263657409)
  ·
    refine ⟨14950696095337497197743057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19934261460449996263657409 14950696095337497197743057)
    ·
      refine ⟨11213022071503122898307293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14950696095337497197743057 11213022071503122898307293)
      ·
        refine ⟨4204883276813671086865235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11213022071503122898307293 4204883276813671086865235)
        ·
          refine ⟨6307324915220506630297853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4204883276813671086865235 6307324915220506630297853)
          ·
            refine ⟨2365246843207689986361695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6307324915220506630297853 2365246843207689986361695)
            ·
              refine ⟨3547870264811534979542543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2365246843207689986361695 3547870264811534979542543)
              ·
                refine ⟨5321805397217302469313815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3547870264811534979542543 5321805397217302469313815)
                ·
                  refine ⟨7982708095825953703970723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5321805397217302469313815 7982708095825953703970723)
                  ·
                    refine ⟨11974062143738930555956085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7982708095825953703970723 11974062143738930555956085)
                    ·
                      refine ⟨1122568325975524739620883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11974062143738930555956085 1122568325975524739620883)
                      ·
                        rfl

theorem cell23_2186194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_2186194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186194 prefixEnd_2186194 := by exact prefixLift 2186194
  have htrace : WordTrace (prefixWord ++ tailWord_2186194) baseStart_2186194 baseEnd_2186194 := by
    simpa [prefixWord, tailWord_2186194, baseEnd_2186194] using wordTrace_append hprefix tailTrace_2186194
  have hstable : (prefixWord ++ tailWord_2186194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186194).length < 2 ^ (prefixWord ++ tailWord_2186194).sum := by decide
  have hdescent : baseEnd_2186194 < baseStart_2186194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186242 : List Nat := [3, 4, 1, 3, 1, 1, 2, 3, 1, 2, 2]
def baseStart_2186242 : Nat := 118140960795 + 2186242 * 2 ^ 59
def prefixEnd_2186242 : Nat := 4983230072969 + 3 ^ 40 * 2186242 * 2
def baseEnd_2186242 : Nat := 1122592973046940551820663

theorem tailTrace_2186242 : CollatzResearch.WordTrace tailWord_2186242 prefixEnd_2186242 1122592973046940551820663 := by
  unfold tailWord_2186242
  simp only [CollatzResearch.WordTrace]
  refine ⟨19934699136406522313094245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53159197697084059501584653 19934699136406522313094245)
  ·
    refine ⟨3737756088076222933705171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19934699136406522313094245 3737756088076222933705171)
    ·
      refine ⟨5606634132114334400557757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3737756088076222933705171 5606634132114334400557757)
      ·
        refine ⟨2102487799542875400209159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5606634132114334400557757 2102487799542875400209159)
        ·
          refine ⟨3153731699314313100313739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2102487799542875400209159 3153731699314313100313739)
          ·
            refine ⟨4730597548971469650470609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3153731699314313100313739 4730597548971469650470609)
            ·
              refine ⟨3547948161728602237852957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4730597548971469650470609 3547948161728602237852957)
              ·
                refine ⟨1330480560648225839194859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3547948161728602237852957 1330480560648225839194859)
                ·
                  refine ⟨1995720840972338758792289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1330480560648225839194859 1995720840972338758792289)
                  ·
                    refine ⟨1496790630729254069094217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1995720840972338758792289 1496790630729254069094217)
                    ·
                      refine ⟨1122592973046940551820663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1496790630729254069094217 1122592973046940551820663)
                      ·
                        rfl

theorem cell23_2186242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_2186242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186242 prefixEnd_2186242 := by exact prefixLift 2186242
  have htrace : WordTrace (prefixWord ++ tailWord_2186242) baseStart_2186242 baseEnd_2186242 := by
    simpa [prefixWord, tailWord_2186242, baseEnd_2186242] using wordTrace_append hprefix tailTrace_2186242
  have hstable : (prefixWord ++ tailWord_2186242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186242).length < 2 ^ (prefixWord ++ tailWord_2186242).sum := by decide
  have hdescent : baseEnd_2186242 < baseStart_2186242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186251 : List Nat := [1, 1, 1, 1, 6, 2, 4, 1, 1, 3, 2]
def baseStart_2186251 : Nat := 118140960795 + 2186251 * 2 ^ 59
def prefixEnd_2186251 : Nat := 4983230072969 + 3 ^ 40 * 2186251 * 2
def baseEnd_2186251 : Nat := 1122597594372831016608121

theorem tailTrace_2186251 : CollatzResearch.WordTrace tailWord_2186251 prefixEnd_2186251 1122597594372831016608121 := by
  unfold tailWord_2186251
  simp only [CollatzResearch.WordTrace]
  refine ⟨79739124802593483789454607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53159416535062322526303071 79739124802593483789454607)
  ·
    refine ⟨119608687203890225684181911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79739124802593483789454607 119608687203890225684181911)
    ·
      refine ⟨179413030805835338526272867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119608687203890225684181911 179413030805835338526272867)
      ·
        refine ⟨269119546208753007789409301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179413030805835338526272867 269119546208753007789409301)
        ·
          refine ⟨12614978728535297240128561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 269119546208753007789409301 12614978728535297240128561)
          ·
            refine ⟨9461234046401472930096421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12614978728535297240128561 9461234046401472930096421)
            ·
              refine ⟨1773981383700276174393079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9461234046401472930096421 1773981383700276174393079)
              ·
                refine ⟨2660972075550414261589619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1773981383700276174393079 2660972075550414261589619)
                ·
                  refine ⟨3991458113325621392384429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2660972075550414261589619 3991458113325621392384429)
                  ·
                    refine ⟨1496796792497108022144161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3991458113325621392384429 1496796792497108022144161)
                    ·
                      refine ⟨1122597594372831016608121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1496796792497108022144161 1122597594372831016608121)
                      ·
                        rfl

theorem cell23_2186251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 1, 3, 2].length) (baseStart_2186251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186251 prefixEnd_2186251 := by exact prefixLift 2186251
  have htrace : WordTrace (prefixWord ++ tailWord_2186251) baseStart_2186251 baseEnd_2186251 := by
    simpa [prefixWord, tailWord_2186251, baseEnd_2186251] using wordTrace_append hprefix tailTrace_2186251
  have hstable : (prefixWord ++ tailWord_2186251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186251).length < 2 ^ (prefixWord ++ tailWord_2186251).sum := by decide
  have hdescent : baseEnd_2186251 < baseStart_2186251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186330 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 2, 8]
def baseStart_2186330 : Nat := 118140960795 + 2186330 * 2 ^ 59
def prefixEnd_2186330 : Nat := 4983230072969 + 3 ^ 40 * 2186330 * 2
def baseEnd_2186330 : Nat := 374212719781512069173419

theorem tailTrace_2186330 : CollatzResearch.WordTrace tailWord_2186330 prefixEnd_2186330 374212719781512069173419 := by
  unfold tailWord_2186330
  simp only [CollatzResearch.WordTrace]
  refine ⟨19935501542326820070395111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53161337446204853521053629 19935501542326820070395111)
  ·
    refine ⟨29903252313490230105592667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19935501542326820070395111 29903252313490230105592667)
    ·
      refine ⟨44854878470235345158389001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29903252313490230105592667 44854878470235345158389001)
      ·
        refine ⟨33641158852676508868791751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44854878470235345158389001 33641158852676508868791751)
        ·
          refine ⟨50461738279014763303187627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33641158852676508868791751 50461738279014763303187627)
          ·
            refine ⟨75692607418522144954781441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50461738279014763303187627 75692607418522144954781441)
            ·
              refine ⟨56769455563891608716086081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75692607418522144954781441 56769455563891608716086081)
              ·
                refine ⟨42577091672918706537064561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56769455563891608716086081 42577091672918706537064561)
                ·
                  refine ⟨31932818754689029902798421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42577091672918706537064561 31932818754689029902798421)
                  ·
                    refine ⟨374212719781512069173419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31932818754689029902798421 374212719781512069173419)
                    ·
                      rfl

theorem cell23_2186330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 2, 8].length) (baseStart_2186330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186330 prefixEnd_2186330 := by exact prefixLift 2186330
  have htrace : WordTrace (prefixWord ++ tailWord_2186330) baseStart_2186330 baseEnd_2186330 := by
    simpa [prefixWord, tailWord_2186330, baseEnd_2186330] using wordTrace_append hprefix tailTrace_2186330
  have hstable : (prefixWord ++ tailWord_2186330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186330).length < 2 ^ (prefixWord ++ tailWord_2186330).sum := by decide
  have hdescent : baseEnd_2186330 < baseStart_2186330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186354 : List Nat := [3, 2, 1, 2, 2, 1, 4, 1, 2, 1, 4]
def baseStart_2186354 : Nat := 118140960795 + 2186354 * 2 ^ 59
def prefixEnd_2186354 : Nat := 4983230072969 + 3 ^ 40 * 2186354 * 2
def baseEnd_2186354 : Nat := 1122650482880244113620147

theorem tailTrace_2186354 : CollatzResearch.WordTrace tailWord_2186354 prefixEnd_2186354 1122650482880244113620147 := by
  unfold tailWord_2186354
  simp only [CollatzResearch.WordTrace]
  refine ⟨19935720380305083095113529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53161921014146888253636077 19935720380305083095113529)
  ·
    refine ⟨14951790285228812321335147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19935720380305083095113529 14951790285228812321335147)
    ·
      refine ⟨22427685427843218482002721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14951790285228812321335147 22427685427843218482002721)
      ·
        refine ⟨16820764070882413861502041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22427685427843218482002721 16820764070882413861502041)
        ·
          refine ⟨12615573053161810396126531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16820764070882413861502041 12615573053161810396126531)
          ·
            refine ⟨18923359579742715594189797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12615573053161810396126531 18923359579742715594189797)
            ·
              refine ⟨3548129921201759173910587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18923359579742715594189797 3548129921201759173910587)
              ·
                refine ⟨5322194881802638760865881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3548129921201759173910587 5322194881802638760865881)
                ·
                  refine ⟨3991646161351979070649411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5322194881802638760865881 3991646161351979070649411)
                  ·
                    refine ⟨5987469242027968605974117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3991646161351979070649411 5987469242027968605974117)
                    ·
                      refine ⟨1122650482880244113620147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5987469242027968605974117 1122650482880244113620147)
                      ·
                        rfl

theorem cell23_2186354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_2186354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186354 prefixEnd_2186354 := by exact prefixLift 2186354
  have htrace : WordTrace (prefixWord ++ tailWord_2186354) baseStart_2186354 baseEnd_2186354 := by
    simpa [prefixWord, tailWord_2186354, baseEnd_2186354] using wordTrace_append hprefix tailTrace_2186354
  have hstable : (prefixWord ++ tailWord_2186354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186354).length < 2 ^ (prefixWord ++ tailWord_2186354).sum := by decide
  have hdescent : baseEnd_2186354 < baseStart_2186354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186360 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 10]
def baseStart_2186360 : Nat := 118140960795 + 2186360 * 2 ^ 59
def prefixEnd_2186360 : Nat := 4983230072969 + 3 ^ 40 * 2186360 * 2
def baseEnd_2186360 : Nat := 124739284862685676682791

theorem tailTrace_2186360 : CollatzResearch.WordTrace tailWord_2186360 prefixEnd_2186360 124739284862685676682791 := by
  unfold tailWord_2186360
  simp only [CollatzResearch.WordTrace]
  refine ⟨39871550179599297702586267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53162066906132396936781689 39871550179599297702586267)
  ·
    refine ⟨59807325269398946553879401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39871550179599297702586267 59807325269398946553879401)
    ·
      refine ⟨44855493952049209915409551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59807325269398946553879401 44855493952049209915409551)
      ·
        refine ⟨67283240928073814873114327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44855493952049209915409551 67283240928073814873114327)
        ·
          refine ⟨100924861392110722309671491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67283240928073814873114327 100924861392110722309671491)
          ·
            refine ⟨151387292088166083464507237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100924861392110722309671491 151387292088166083464507237)
            ·
              refine ⟨28385117266531140649595107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 151387292088166083464507237 28385117266531140649595107)
              ·
                refine ⟨42577675899796710974392661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28385117266531140649595107 42577675899796710974392661)
                ·
                  refine ⟨124739284862685676682791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 42577675899796710974392661 124739284862685676682791)
                  ·
                    rfl

theorem cell23_2186360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 10].length) (baseStart_2186360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186360 prefixEnd_2186360 := by exact prefixLift 2186360
  have htrace : WordTrace (prefixWord ++ tailWord_2186360) baseStart_2186360 baseEnd_2186360 := by
    simpa [prefixWord, tailWord_2186360, baseEnd_2186360] using wordTrace_append hprefix tailTrace_2186360
  have hstable : (prefixWord ++ tailWord_2186360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186360).length < 2 ^ (prefixWord ++ tailWord_2186360).sum := by decide
  have hdescent : baseEnd_2186360 < baseStart_2186360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186377 : List Nat := [1, 2, 1, 1, 4, 3, 1, 4, 6]
def baseStart_2186377 : Nat := 118140960795 + 2186377 * 2 ^ 59
def prefixEnd_2186377 : Nat := 4983230072969 + 3 ^ 40 * 2186377 * 2
def baseEnd_2186377 : Nat := 124740254770588613736949

theorem tailTrace_2186377 : CollatzResearch.WordTrace tailWord_2186377 prefixEnd_2186377 124740254770588613736949 := by
  unfold tailWord_2186377
  simp only [CollatzResearch.WordTrace]
  refine ⟨79743720400137007308541385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53162480266758004872360923 79743720400137007308541385)
  ·
    refine ⟨59807790300102755481406039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79743720400137007308541385 59807790300102755481406039)
    ·
      refine ⟨89711685450154133222109059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59807790300102755481406039 89711685450154133222109059)
      ·
        refine ⟨134567528175231199833163589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89711685450154133222109059 134567528175231199833163589)
        ·
          refine ⟨25231411532855849968718173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 134567528175231199833163589 25231411532855849968718173)
          ·
            refine ⟨9461779324820943738269315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25231411532855849968718173 9461779324820943738269315)
            ·
              refine ⟨14192668987231415607403973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9461779324820943738269315 14192668987231415607403973)
              ·
                refine ⟨2661125435105890426388245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14192668987231415607403973 2661125435105890426388245)
                ·
                  refine ⟨124740254770588613736949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2661125435105890426388245 124740254770588613736949)
                  ·
                    rfl

theorem cell23_2186377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 6].length) (baseStart_2186377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186377 prefixEnd_2186377 := by exact prefixLift 2186377
  have htrace : WordTrace (prefixWord ++ tailWord_2186377) baseStart_2186377 baseEnd_2186377 := by
    simpa [prefixWord, tailWord_2186377, baseEnd_2186377] using wordTrace_append hprefix tailTrace_2186377
  have hstable : (prefixWord ++ tailWord_2186377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186377).length < 2 ^ (prefixWord ++ tailWord_2186377).sum := by decide
  have hdescent : baseEnd_2186377 < baseStart_2186377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186394 : List Nat := [3, 1, 1, 5, 1, 1, 2, 3, 6]
def baseStart_2186394 : Nat := 118140960795 + 2186394 * 2 ^ 59
def prefixEnd_2186394 : Nat := 4983230072969 + 3 ^ 40 * 2186394 * 2
def baseEnd_2186394 : Nat := 124741224678491550791107

theorem tailTrace_2186394 : CollatzResearch.WordTrace tailWord_2186394 prefixEnd_2186394 124741224678491550791107 := by
  unfold tailWord_2186394
  simp only [CollatzResearch.WordTrace]
  refine ⟨19936085110268854802977559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53162893627383612807940157 19936085110268854802977559)
  ·
    refine ⟨29904127665403282204466339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19936085110268854802977559 29904127665403282204466339)
    ·
      refine ⟨44856191498104923306699509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29904127665403282204466339 44856191498104923306699509)
      ·
        refine ⟨4205267952947336560003079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44856191498104923306699509 4205267952947336560003079)
        ·
          refine ⟨6307901929421004840004619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4205267952947336560003079 6307901929421004840004619)
          ·
            refine ⟨9461852894131507260006929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6307901929421004840004619 9461852894131507260006929)
            ·
              refine ⟨7096389670598630445005197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9461852894131507260006929 7096389670598630445005197)
              ·
                refine ⟨2661146126474486416876949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7096389670598630445005197 2661146126474486416876949)
                ·
                  refine ⟨124741224678491550791107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2661146126474486416876949 124741224678491550791107)
                  ·
                    rfl

theorem cell23_2186394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 6].length) (baseStart_2186394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186394 prefixEnd_2186394 := by exact prefixLift 2186394
  have htrace : WordTrace (prefixWord ++ tailWord_2186394) baseStart_2186394 baseEnd_2186394 := by
    simpa [prefixWord, tailWord_2186394, baseEnd_2186394] using wordTrace_append hprefix tailTrace_2186394
  have hstable : (prefixWord ++ tailWord_2186394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186394).length < 2 ^ (prefixWord ++ tailWord_2186394).sum := by decide
  have hdescent : baseEnd_2186394 < baseStart_2186394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186427 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 4]
def baseStart_2186427 : Nat := 118140960795 + 2186427 * 2 ^ 59
def prefixEnd_2186427 : Nat := 4983230072969 + 3 ^ 40 * 2186427 * 2
def baseEnd_2186427 : Nat := 1122687966968022328007311

theorem tailTrace_2186427 : CollatzResearch.WordTrace tailWord_2186427 prefixEnd_2186427 1122687966968022328007311 := by
  unfold tailWord_2186427
  simp only [CollatzResearch.WordTrace]
  refine ⟨79745544049955865847861535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53163696033303910565241023 79745544049955865847861535)
  ·
    refine ⟨119618316074933798771792303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79745544049955865847861535 119618316074933798771792303)
    ·
      refine ⟨179427474112400698157688455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119618316074933798771792303 179427474112400698157688455)
      ·
        refine ⟨269141211168601047236532683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179427474112400698157688455 269141211168601047236532683)
        ·
          refine ⟨403711816752901570854799025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269141211168601047236532683 403711816752901570854799025)
          ·
            refine ⟨302783862564676178141099269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 403711816752901570854799025 302783862564676178141099269)
            ·
              refine ⟨56771974230876783401456113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 302783862564676178141099269 56771974230876783401456113)
              ·
                refine ⟨42578980673157587551092085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56771974230876783401456113 42578980673157587551092085)
                ·
                  refine ⟨3991779438108523832914883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42578980673157587551092085 3991779438108523832914883)
                  ·
                    refine ⟨5987669157162785749372325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3991779438108523832914883 5987669157162785749372325)
                    ·
                      refine ⟨1122687966968022328007311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5987669157162785749372325 1122687966968022328007311)
                      ·
                        rfl

theorem cell23_2186427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 4].length) (baseStart_2186427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186427 prefixEnd_2186427 := by exact prefixLift 2186427
  have htrace : WordTrace (prefixWord ++ tailWord_2186427) baseStart_2186427 baseEnd_2186427 := by
    simpa [prefixWord, tailWord_2186427, baseEnd_2186427] using wordTrace_append hprefix tailTrace_2186427
  have hstable : (prefixWord ++ tailWord_2186427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186427).length < 2 ^ (prefixWord ++ tailWord_2186427).sum := by decide
  have hdescent : baseEnd_2186427 < baseStart_2186427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186445 : List Nat := [1, 6, 2, 2, 1, 1, 3, 1, 6]
def baseStart_2186445 : Nat := 118140960795 + 2186445 * 2 ^ 59
def prefixEnd_2186445 : Nat := 4983230072969 + 3 ^ 40 * 2186445 * 2
def baseEnd_2186445 : Nat := 124744134402200361953581

theorem tailTrace_2186445 : CollatzResearch.WordTrace tailWord_2186445 prefixEnd_2186445 124744134402200361953581 := by
  unfold tailWord_2186445
  simp only [CollatzResearch.WordTrace]
  refine ⟨79746200563890654922016789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53164133709260436614677859 79746200563890654922016789)
  ·
    refine ⟨3738103151432374449469537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 79746200563890654922016789 3738103151432374449469537)
    ·
      refine ⟨2803577363574280837102153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3738103151432374449469537 2803577363574280837102153)
      ·
        refine ⟨2102683022680710627826615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2803577363574280837102153 2102683022680710627826615)
        ·
          refine ⟨3154024534021065941739923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2102683022680710627826615 3154024534021065941739923)
          ·
            refine ⟨4731036801031598912609885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3154024534021065941739923 4731036801031598912609885)
            ·
              refine ⟨1774138800386849592228707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4731036801031598912609885 1774138800386849592228707)
              ·
                refine ⟨2661208200580274388343061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1774138800386849592228707 2661208200580274388343061)
                ·
                  refine ⟨124744134402200361953581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2661208200580274388343061 124744134402200361953581)
                  ·
                    rfl

theorem cell23_2186445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_2186445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186445 prefixEnd_2186445 := by exact prefixLift 2186445
  have htrace : WordTrace (prefixWord ++ tailWord_2186445) baseStart_2186445 baseEnd_2186445 := by
    simpa [prefixWord, tailWord_2186445, baseEnd_2186445] using wordTrace_append hprefix tailTrace_2186445
  have hstable : (prefixWord ++ tailWord_2186445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186445).length < 2 ^ (prefixWord ++ tailWord_2186445).sum := by decide
  have hdescent : baseEnd_2186445 < baseStart_2186445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186447 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 2, 6, 3]
def baseStart_2186447 : Nat := 118140960795 + 2186447 * 2 ^ 59
def prefixEnd_2186447 : Nat := 4983230072969 + 3 ^ 40 * 2186447 * 2
def baseEnd_2186447 : Nat := 1122698236581112249757219

theorem tailTrace_2186447 : CollatzResearch.WordTrace tailWord_2186447 prefixEnd_2186447 1122698236581112249757219 := by
  unfold tailWord_2186447
  simp only [CollatzResearch.WordTrace]
  refine ⟨79746273509883409263589595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53164182339922272842393063 79746273509883409263589595)
  ·
    refine ⟨119619410264825113895384393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79746273509883409263589595 119619410264825113895384393)
    ·
      refine ⟨89714557698618835421538295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119619410264825113895384393 89714557698618835421538295)
      ·
        refine ⟨134571836547928253132307443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89714557698618835421538295 134571836547928253132307443)
        ·
          refine ⟨201857754821892379698461165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134571836547928253132307443 201857754821892379698461165)
          ·
            refine ⟨75696658058209642386922937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201857754821892379698461165 75696658058209642386922937)
            ·
              refine ⟨56772493543657231790192203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75696658058209642386922937 56772493543657231790192203)
              ·
                refine ⟨85158740315485847685288305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56772493543657231790192203 85158740315485847685288305)
                ·
                  refine ⟨63869055236614385763966229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85158740315485847685288305 63869055236614385763966229)
                  ·
                    refine ⟨2993861964216299332685917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63869055236614385763966229 2993861964216299332685917)
                    ·
                      refine ⟨1122698236581112249757219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2993861964216299332685917 1122698236581112249757219)
                      ·
                        rfl

theorem cell23_2186447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 6, 3].length) (baseStart_2186447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186447 prefixEnd_2186447 := by exact prefixLift 2186447
  have htrace : WordTrace (prefixWord ++ tailWord_2186447) baseStart_2186447 baseEnd_2186447 := by
    simpa [prefixWord, tailWord_2186447, baseEnd_2186447] using wordTrace_append hprefix tailTrace_2186447
  have hstable : (prefixWord ++ tailWord_2186447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186447).length < 2 ^ (prefixWord ++ tailWord_2186447).sum := by decide
  have hdescent : baseEnd_2186447 < baseStart_2186447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186517 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 1, 2, 8]
def baseStart_2186517 : Nat := 118140960795 + 2186517 * 2 ^ 59
def prefixEnd_2186517 : Nat := 4983230072969 + 3 ^ 40 * 2186517 * 2
def baseEnd_2186517 : Nat := 1122734180226926975881897

theorem tailTrace_2186517 : CollatzResearch.WordTrace tailWord_2186517 prefixEnd_2186517 1122734180226926975881897 := by
  unfold tailWord_2186517
  simp only [CollatzResearch.WordTrace]
  refine ⟨79748826619629811218637805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53165884413086540812425203 79748826619629811218637805)
  ·
    refine ⟨29905809982361179206989177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79748826619629811218637805 29905809982361179206989177)
    ·
      refine ⟨22429357486770884405241883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29905809982361179206989177 22429357486770884405241883)
      ·
        refine ⟨33644036230156326607862825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22429357486770884405241883 33644036230156326607862825)
        ·
          refine ⟨25233027172617244955897119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33644036230156326607862825 25233027172617244955897119)
          ·
            refine ⟨37849540758925867433845679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25233027172617244955897119 37849540758925867433845679)
            ·
              refine ⟨56774311138388801150768519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37849540758925867433845679 56774311138388801150768519)
              ·
                refine ⟨85161466707583201726152779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56774311138388801150768519 85161466707583201726152779)
                ·
                  refine ⟨127742200061374802589229169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85161466707583201726152779 127742200061374802589229169)
                  ·
                    refine ⟨95806650046031101941921877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 127742200061374802589229169 95806650046031101941921877)
                    ·
                      refine ⟨1122734180226926975881897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 95806650046031101941921877 1122734180226926975881897)
                      ·
                        rfl

theorem cell23_2186517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_2186517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186517 prefixEnd_2186517 := by exact prefixLift 2186517
  have htrace : WordTrace (prefixWord ++ tailWord_2186517) baseStart_2186517 baseEnd_2186517 := by
    simpa [prefixWord, tailWord_2186517, baseEnd_2186517] using wordTrace_append hprefix tailTrace_2186517
  have hstable : (prefixWord ++ tailWord_2186517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186517).length < 2 ^ (prefixWord ++ tailWord_2186517).sum := by decide
  have hdescent : baseEnd_2186517 < baseStart_2186517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186537 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 5, 3, 5]
def baseStart_2186537 : Nat := 118140960795 + 2186537 * 2 ^ 59
def prefixEnd_2186537 : Nat := 4983230072969 + 3 ^ 40 * 2186537 * 2
def baseEnd_2186537 : Nat := 1122744449840016897631805

theorem tailTrace_2186537 : CollatzResearch.WordTrace tailWord_2186537 prefixEnd_2186537 1122744449840016897631805 := by
  unfold tailWord_2186537
  simp only [CollatzResearch.WordTrace]
  refine ⟨79749556079557354634365865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53166370719704903089577243 79749556079557354634365865)
  ·
    refine ⟨59812167059668015975774399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79749556079557354634365865 59812167059668015975774399)
    ·
      refine ⟨89718250589502023963661599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59812167059668015975774399 89718250589502023963661599)
      ·
        refine ⟨134577375884253035945492399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89718250589502023963661599 134577375884253035945492399)
        ·
          refine ⟨201866063826379553918238599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134577375884253035945492399 201866063826379553918238599)
          ·
            refine ⟨302799095739569330877357899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201866063826379553918238599 302799095739569330877357899)
            ·
              refine ⟨454198643609353996316036849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302799095739569330877357899 454198643609353996316036849)
              ·
                refine ⟨340648982707015497237027637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 454198643609353996316036849 340648982707015497237027637)
                ·
                  refine ⟨31935842128782702865971341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 340648982707015497237027637 31935842128782702865971341)
                  ·
                    refine ⟨11975940798293513574739253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31935842128782702865971341 11975940798293513574739253)
                    ·
                      refine ⟨1122744449840016897631805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11975940798293513574739253 1122744449840016897631805)
                      ·
                        rfl

theorem cell23_2186537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 3, 5].length) (baseStart_2186537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186537 prefixEnd_2186537 := by exact prefixLift 2186537
  have htrace : WordTrace (prefixWord ++ tailWord_2186537) baseStart_2186537 baseEnd_2186537 := by
    simpa [prefixWord, tailWord_2186537, baseEnd_2186537] using wordTrace_append hprefix tailTrace_2186537
  have hstable : (prefixWord ++ tailWord_2186537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186537).length < 2 ^ (prefixWord ++ tailWord_2186537).sum := by decide
  have hdescent : baseEnd_2186537 < baseStart_2186537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186554 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 1, 6, 3]
def baseStart_2186554 : Nat := 118140960795 + 2186554 * 2 ^ 59
def prefixEnd_2186554 : Nat := 4983230072969 + 3 ^ 40 * 2186554 * 2
def baseEnd_2186554 : Nat := 1122753179011143331119227

theorem tailTrace_2186554 : CollatzResearch.WordTrace tailWord_2186554 prefixEnd_2186554 1122753179011143331119227 := by
  unfold tailWord_2186554
  simp only [CollatzResearch.WordTrace]
  refine ⟨19937544030123941634433679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53166784080330511025156477 19937544030123941634433679)
  ·
    refine ⟨29906316045185912451650519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19937544030123941634433679 29906316045185912451650519)
    ·
      refine ⟨44859474067778868677475779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29906316045185912451650519 44859474067778868677475779)
      ·
        refine ⟨67289211101668303016213669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44859474067778868677475779 67289211101668303016213669)
        ·
          refine ⟨12616727081562806815540063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67289211101668303016213669 12616727081562806815540063)
          ·
            refine ⟨18925090622344210223310095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12616727081562806815540063 18925090622344210223310095)
            ·
              refine ⟨28387635933516315334965143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18925090622344210223310095 28387635933516315334965143)
              ·
                refine ⟨42581453900274473002447715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28387635933516315334965143 42581453900274473002447715)
                ·
                  refine ⟨63872180850411709503671573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42581453900274473002447715 63872180850411709503671573)
                  ·
                    refine ⟨2994008477363048882984605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63872180850411709503671573 2994008477363048882984605)
                    ·
                      refine ⟨1122753179011143331119227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2994008477363048882984605 1122753179011143331119227)
                      ·
                        rfl

theorem cell23_2186554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 1, 6, 3].length) (baseStart_2186554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186554 prefixEnd_2186554 := by exact prefixLift 2186554
  have htrace : WordTrace (prefixWord ++ tailWord_2186554) baseStart_2186554 baseEnd_2186554 := by
    simpa [prefixWord, tailWord_2186554, baseEnd_2186554] using wordTrace_append hprefix tailTrace_2186554
  have hstable : (prefixWord ++ tailWord_2186554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186554).length < 2 ^ (prefixWord ++ tailWord_2186554).sum := by decide
  have hdescent : baseEnd_2186554 < baseStart_2186554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186561 : List Nat := [1, 2, 5, 2, 1, 2, 1, 1, 2, 6]
def baseStart_2186561 : Nat := 118140960795 + 2186561 * 2 ^ 59
def prefixEnd_2186561 : Nat := 4983230072969 + 3 ^ 40 * 2186561 * 2
def baseEnd_2186561 : Nat := 374252257791908267910565

theorem tailTrace_2186561 : CollatzResearch.WordTrace tailWord_2186561 prefixEnd_2186561 374252257791908267910565 := by
  unfold tailWord_2186561
  simp only [CollatzResearch.WordTrace]
  refine ⟨79750431431470406733239537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53166954287646937822159691 79750431431470406733239537)
  ·
    refine ⟨59812823573602805049929653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79750431431470406733239537 59812823573602805049929653)
    ·
      refine ⟨5607452210025262973430905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59812823573602805049929653 5607452210025262973430905)
      ·
        refine ⟨4205589157518947230073179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5607452210025262973430905 4205589157518947230073179)
        ·
          refine ⟨6308383736278420845109769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4205589157518947230073179 6308383736278420845109769)
          ·
            refine ⟨4731287802208815633832327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6308383736278420845109769 4731287802208815633832327)
            ·
              refine ⟨7096931703313223450748491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4731287802208815633832327 7096931703313223450748491)
              ·
                refine ⟨10645397554969835176122737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7096931703313223450748491 10645397554969835176122737)
                ·
                  refine ⟨7984048166227376382092053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10645397554969835176122737 7984048166227376382092053)
                  ·
                    refine ⟨374252257791908267910565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7984048166227376382092053 374252257791908267910565)
                    ·
                      rfl

theorem cell23_2186561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_2186561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186561 prefixEnd_2186561 := by exact prefixLift 2186561
  have htrace : WordTrace (prefixWord ++ tailWord_2186561) baseStart_2186561 baseEnd_2186561 := by
    simpa [prefixWord, tailWord_2186561, baseEnd_2186561] using wordTrace_append hprefix tailTrace_2186561
  have hstable : (prefixWord ++ tailWord_2186561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186561).length < 2 ^ (prefixWord ++ tailWord_2186561).sum := by decide
  have hdescent : baseEnd_2186561 < baseStart_2186561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186574 : List Nat := [4, 1, 1, 1, 1, 1, 5, 2, 7]
def baseStart_2186574 : Nat := 118140960795 + 2186574 * 2 ^ 59
def prefixEnd_2186574 : Nat := 4983230072969 + 3 ^ 40 * 2186574 * 2
def baseEnd_2186574 : Nat := 124751494291581472541015

theorem tailTrace_2186574 : CollatzResearch.WordTrace tailWord_2186574 prefixEnd_2186574 124751494291581472541015 := by
  unfold tailWord_2186574
  simp only [CollatzResearch.WordTrace]
  refine ⟨9968863197552913744182847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53167270386948873302308517 9968863197552913744182847)
  ·
    refine ⟨14953294796329370616274271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9968863197552913744182847 14953294796329370616274271)
    ·
      refine ⟨22429942194494055924411407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14953294796329370616274271 22429942194494055924411407)
      ·
        refine ⟨33644913291741083886617111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22429942194494055924411407 33644913291741083886617111)
        ·
          refine ⟨50467369937611625829925667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33644913291741083886617111 50467369937611625829925667)
          ·
            refine ⟨75701054906417438744888501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50467369937611625829925667 75701054906417438744888501)
            ·
              refine ⟨7096973897476634882333297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75701054906417438744888501 7096973897476634882333297)
              ·
                refine ⟨5322730423107476161749973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7096973897476634882333297 5322730423107476161749973)
                ·
                  refine ⟨124751494291581472541015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5322730423107476161749973 124751494291581472541015)
                  ·
                    rfl

theorem cell23_2186574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 7].length) (baseStart_2186574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186574 prefixEnd_2186574 := by exact prefixLift 2186574
  have htrace : WordTrace (prefixWord ++ tailWord_2186574) baseStart_2186574 baseEnd_2186574 := by
    simpa [prefixWord, tailWord_2186574, baseEnd_2186574] using wordTrace_append hprefix tailTrace_2186574
  have hstable : (prefixWord ++ tailWord_2186574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186574).length < 2 ^ (prefixWord ++ tailWord_2186574).sum := by decide
  have hdescent : baseEnd_2186574 < baseStart_2186574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186584 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 1, 5, 3]
def baseStart_2186584 : Nat := 118140960795 + 2186584 * 2 ^ 59
def prefixEnd_2186584 : Nat := 4983230072969 + 3 ^ 40 * 2186584 * 2
def baseEnd_2186584 : Nat := 1122768583430778213744089

theorem tailTrace_2186584 : CollatzResearch.WordTrace tailWord_2186584 prefixEnd_2186584 1122768583430778213744089 := by
  unfold tailWord_2186584
  simp only [CollatzResearch.WordTrace]
  refine ⟨39875635155193540830663403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53167513540258054440884537 39875635155193540830663403)
  ·
    refine ⟨59813452732790311245995105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39875635155193540830663403 59813452732790311245995105)
    ·
      refine ⟨44860089549592733434496329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59813452732790311245995105 44860089549592733434496329)
      ·
        refine ⟨33645067162194550075872247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44860089549592733434496329 33645067162194550075872247)
        ·
          refine ⟨50467600743291825113808371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33645067162194550075872247 50467600743291825113808371)
          ·
            refine ⟨75701401114937737670712557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50467600743291825113808371 75701401114937737670712557)
            ·
              refine ⟨28388025418101651626517209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75701401114937737670712557 28388025418101651626517209)
              ·
                refine ⟨21291019063576238719887907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28388025418101651626517209 21291019063576238719887907)
                ·
                  refine ⟨31936528595364358079831861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21291019063576238719887907 31936528595364358079831861)
                  ·
                    refine ⟨2994049555815408569984237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31936528595364358079831861 2994049555815408569984237)
                    ·
                      refine ⟨1122768583430778213744089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2994049555815408569984237 1122768583430778213744089)
                      ·
                        rfl

theorem cell23_2186584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_2186584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186584 prefixEnd_2186584 := by exact prefixLift 2186584
  have htrace : WordTrace (prefixWord ++ tailWord_2186584) baseStart_2186584 baseEnd_2186584 := by
    simpa [prefixWord, tailWord_2186584, baseEnd_2186584] using wordTrace_append hprefix tailTrace_2186584
  have hstable : (prefixWord ++ tailWord_2186584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186584).length < 2 ^ (prefixWord ++ tailWord_2186584).sum := by decide
  have hdescent : baseEnd_2186584 < baseStart_2186584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186589 : List Nat := [1, 4, 5, 1, 1, 1, 1, 3, 1, 3, 2]
def baseStart_2186589 : Nat := 118140960795 + 2186589 * 2 ^ 59
def prefixEnd_2186589 : Nat := 4983230072969 + 3 ^ 40 * 2186589 * 2
def baseEnd_2186589 : Nat := 1122771150834050694181567

theorem tailTrace_2186589 : CollatzResearch.WordTrace tailWord_2186589 prefixEnd_2186589 1122771150834050694181567 := by
  unfold tailWord_2186589
  simp only [CollatzResearch.WordTrace]
  refine ⟨79751452675368967515258821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53167635116912645010172547 79751452675368967515258821)
  ·
    refine ⟨14953397376631681409111029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79751452675368967515258821 14953397376631681409111029)
    ·
      refine ⟨1401881004059220132104159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14953397376631681409111029 1401881004059220132104159)
      ·
        refine ⟨2102821506088830198156239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1401881004059220132104159 2102821506088830198156239)
        ·
          refine ⟨3154232259133245297234359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2102821506088830198156239 3154232259133245297234359)
          ·
            refine ⟨4731348388699867945851539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3154232259133245297234359 4731348388699867945851539)
            ·
              refine ⟨7097022583049801918777309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4731348388699867945851539 7097022583049801918777309)
              ·
                refine ⟨2661383468643675719541491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7097022583049801918777309 2661383468643675719541491)
                ·
                  refine ⟨3992075202965513579312237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2661383468643675719541491 3992075202965513579312237)
                  ·
                    refine ⟨1497028201112067592242089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3992075202965513579312237 1497028201112067592242089)
                    ·
                      refine ⟨1122771150834050694181567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1497028201112067592242089 1122771150834050694181567)
                      ·
                        rfl

theorem cell23_2186589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_2186589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186589 prefixEnd_2186589 := by exact prefixLift 2186589
  have htrace : WordTrace (prefixWord ++ tailWord_2186589) baseStart_2186589 baseEnd_2186589 := by
    simpa [prefixWord, tailWord_2186589, baseEnd_2186589] using wordTrace_append hprefix tailTrace_2186589
  have hstable : (prefixWord ++ tailWord_2186589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186589).length < 2 ^ (prefixWord ++ tailWord_2186589).sum := by decide
  have hdescent : baseEnd_2186589 < baseStart_2186589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186642 : List Nat := [3, 2, 3, 3, 1, 2, 1, 3, 5]
def baseStart_2186642 : Nat := 118140960795 + 2186642 * 2 ^ 59
def prefixEnd_2186642 : Nat := 4983230072969 + 3 ^ 40 * 2186642 * 2
def baseEnd_2186642 : Nat := 124755373923193220757647

theorem tailTrace_2186642 : CollatzResearch.WordTrace tailWord_2186642 prefixEnd_2186642 124755373923193220757647 := by
  unfold tailWord_2186642
  simp only [CollatzResearch.WordTrace]
  refine ⟨19938346436044239391734545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53168923829451305044625453 19938346436044239391734545)
  ·
    refine ⟨14953759827033179543800909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19938346436044239391734545 14953759827033179543800909)
    ·
      refine ⟨5607659935137442328925341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14953759827033179543800909 5607659935137442328925341)
      ·
        refine ⟨2102872475676540873347003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5607659935137442328925341 2102872475676540873347003)
        ·
          refine ⟨3154308713514811310020505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2102872475676540873347003 3154308713514811310020505)
          ·
            refine ⟨2365731535136108482515379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3154308713514811310020505 2365731535136108482515379)
            ·
              refine ⟨3548597302704162723773069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2365731535136108482515379 3548597302704162723773069)
              ·
                refine ⟨1330723988514061021414901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3548597302704162723773069 1330723988514061021414901)
                ·
                  refine ⟨124755373923193220757647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1330723988514061021414901 124755373923193220757647)
                  ·
                    rfl

theorem cell23_2186642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 3, 5].length) (baseStart_2186642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186642 prefixEnd_2186642 := by exact prefixLift 2186642
  have htrace : WordTrace (prefixWord ++ tailWord_2186642) baseStart_2186642 baseEnd_2186642 := by
    simpa [prefixWord, tailWord_2186642, baseEnd_2186642] using wordTrace_append hprefix tailTrace_2186642
  have hstable : (prefixWord ++ tailWord_2186642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186642).length < 2 ^ (prefixWord ++ tailWord_2186642).sum := by decide
  have hdescent : baseEnd_2186642 < baseStart_2186642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186658 : List Nat := [3, 3, 1, 2, 1, 3, 1, 2, 2, 1, 4]
def baseStart_2186658 : Nat := 118140960795 + 2186658 * 2 ^ 59
def prefixEnd_2186658 : Nat := 4983230072969 + 3 ^ 40 * 2186658 * 2
def baseEnd_2186658 : Nat := 1122806580999210924218749

theorem tailTrace_2186658 : CollatzResearch.WordTrace tailWord_2186658 prefixEnd_2186658 1122806580999210924218749 := by
  unfold tailWord_2186658
  simp only [CollatzResearch.WordTrace]
  refine ⟨19938492328029748074880157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53169312874745994866347085 19938492328029748074880157)
  ·
    refine ⟨7476934623011155528080059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19938492328029748074880157 7476934623011155528080059)
    ·
      refine ⟨11215401934516733292120089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7476934623011155528080059 11215401934516733292120089)
      ·
        refine ⟨8411551450887549969090067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11215401934516733292120089 8411551450887549969090067)
        ·
          refine ⟨12617327176331324953635101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8411551450887549969090067 12617327176331324953635101)
          ·
            refine ⟨4731497691124246857613163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12617327176331324953635101 4731497691124246857613163)
            ·
              refine ⟨7097246536686370286419745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4731497691124246857613163 7097246536686370286419745)
              ·
                refine ⟨5322934902514777714814809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7097246536686370286419745 5322934902514777714814809)
                ·
                  refine ⟨3992201176886083286111107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5322934902514777714814809 3992201176886083286111107)
                  ·
                    refine ⟨5988301765329124929166661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3992201176886083286111107 5988301765329124929166661)
                    ·
                      refine ⟨1122806580999210924218749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5988301765329124929166661 1122806580999210924218749)
                      ·
                        rfl

theorem cell23_2186658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_2186658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186658 prefixEnd_2186658 := by exact prefixLift 2186658
  have htrace : WordTrace (prefixWord ++ tailWord_2186658) baseStart_2186658 baseEnd_2186658 := by
    simpa [prefixWord, tailWord_2186658, baseEnd_2186658] using wordTrace_append hprefix tailTrace_2186658
  have hstable : (prefixWord ++ tailWord_2186658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186658).length < 2 ^ (prefixWord ++ tailWord_2186658).sum := by decide
  have hdescent : baseEnd_2186658 < baseStart_2186658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186668 : List Nat := [2, 2, 1, 1, 1, 1, 4, 6, 1, 4]
def baseStart_2186668 : Nat := 118140960795 + 2186668 * 2 ^ 59
def prefixEnd_2186668 : Nat := 4983230072969 + 3 ^ 40 * 2186668 * 2
def baseEnd_2186668 : Nat := 374270571935251961697901

theorem tailTrace_2186668 : CollatzResearch.WordTrace tailWord_2186668 prefixEnd_2186668 374270571935251961697901 := by
  unfold tailWord_2186668
  simp only [CollatzResearch.WordTrace]
  refine ⟨39877167021041382003692329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53169556028055176004923105 39877167021041382003692329)
  ·
    refine ⟨29907875265781036502769247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39877167021041382003692329 29907875265781036502769247)
    ·
      refine ⟨44861812898671554754153871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29907875265781036502769247 44861812898671554754153871)
      ·
        refine ⟨67292719348007332131230807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44861812898671554754153871 67292719348007332131230807)
        ·
          refine ⟨100939079022010998196846211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67292719348007332131230807 100939079022010998196846211)
          ·
            refine ⟨151408618533016497295269317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100939079022010998196846211 151408618533016497295269317)
            ·
              refine ⟨28389115974940593242862997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 151408618533016497295269317 28389115974940593242862997)
              ·
                refine ⟨1330739811325340308259203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28389115974940593242862997 1330739811325340308259203)
                ·
                  refine ⟨1996109716988010462388805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1330739811325340308259203 1996109716988010462388805)
                  ·
                    refine ⟨374270571935251961697901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1996109716988010462388805 374270571935251961697901)
                    ·
                      rfl

theorem cell23_2186668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6, 1, 4].length) (baseStart_2186668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186668 prefixEnd_2186668 := by exact prefixLift 2186668
  have htrace : WordTrace (prefixWord ++ tailWord_2186668) baseStart_2186668 baseEnd_2186668 := by
    simpa [prefixWord, tailWord_2186668, baseEnd_2186668] using wordTrace_append hprefix tailTrace_2186668
  have hstable : (prefixWord ++ tailWord_2186668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186668).length < 2 ^ (prefixWord ++ tailWord_2186668).sum := by decide
  have hdescent : baseEnd_2186668 < baseStart_2186668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186711 : List Nat := [1, 1, 3, 2, 1, 1, 1, 7, 1, 5]
def baseStart_2186711 : Nat := 118140960795 + 2186711 * 2 ^ 59
def prefixEnd_2186711 : Nat := 4983230072969 + 3 ^ 40 * 2186711 * 2
def baseEnd_2186711 : Nat := 374277931824633072285335

theorem tailTrace_2186711 : CollatzResearch.WordTrace tailWord_2186711 prefixEnd_2186711 374277931824633072285335 := by
  unfold tailWord_2186711
  simp only [CollatzResearch.WordTrace]
  refine ⟨79755902380926982351199987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53170601587284654900799991 79755902380926982351199987)
  ·
    refine ⟨119633853571390473526799981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79755902380926982351199987 119633853571390473526799981)
    ·
      refine ⟨44862695089271427572549993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119633853571390473526799981 44862695089271427572549993)
      ·
        refine ⟨33647021316953570679412495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44862695089271427572549993 33647021316953570679412495)
        ·
          refine ⟨50470531975430356019118743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33647021316953570679412495 50470531975430356019118743)
          ·
            refine ⟨75705797963145534028678115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50470531975430356019118743 75705797963145534028678115)
            ·
              refine ⟨113558696944718301043017173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75705797963145534028678115 113558696944718301043017173)
              ·
                refine ⟨2661531959641835180695715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 113558696944718301043017173 2661531959641835180695715)
                ·
                  refine ⟨3992297939462752771043573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2661531959641835180695715 3992297939462752771043573)
                  ·
                    refine ⟨374277931824633072285335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3992297939462752771043573 374277931824633072285335)
                    ·
                      rfl

theorem cell23_2186711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 5].length) (baseStart_2186711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186711 prefixEnd_2186711 := by exact prefixLift 2186711
  have htrace : WordTrace (prefixWord ++ tailWord_2186711) baseStart_2186711 baseEnd_2186711 := by
    simpa [prefixWord, tailWord_2186711, baseEnd_2186711] using wordTrace_append hprefix tailTrace_2186711
  have hstable : (prefixWord ++ tailWord_2186711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186711).length < 2 ^ (prefixWord ++ tailWord_2186711).sum := by decide
  have hdescent : baseEnd_2186711 < baseStart_2186711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186761 : List Nat := [1, 2, 1, 1, 3, 1, 3, 4, 1, 2, 4]
def baseStart_2186761 : Nat := 118140960795 + 2186761 * 2 ^ 59
def prefixEnd_2186761 : Nat := 4983230072969 + 3 ^ 40 * 2186761 * 2
def baseEnd_2186761 : Nat := 1122859469506624021230775

theorem tailTrace_2186761 : CollatzResearch.WordTrace tailWord_2186761 prefixEnd_2186761 1122859469506624021230775 := by
  unfold tailWord_2186761
  simp only [CollatzResearch.WordTrace]
  refine ⟨79757726030745840890520137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53171817353830560593680091 79757726030745840890520137)
  ·
    refine ⟨59818294523059380667890103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79757726030745840890520137 59818294523059380667890103)
    ·
      refine ⟨89727441784589071001835155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59818294523059380667890103 89727441784589071001835155)
      ·
        refine ⟨134591162676883606502752733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89727441784589071001835155 134591162676883606502752733)
        ·
          refine ⟨50471686003831352438532275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134591162676883606502752733 50471686003831352438532275)
          ·
            refine ⟨75707529005747028657798413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50471686003831352438532275 75707529005747028657798413)
            ·
              refine ⟨28390323377155135746674405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75707529005747028657798413 28390323377155135746674405)
              ·
                refine ⟨5323185633216587952501451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28390323377155135746674405 5323185633216587952501451)
                ·
                  refine ⟨7984778449824881928752177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5323185633216587952501451 7984778449824881928752177)
                  ·
                    refine ⟨5988583837368661446564133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7984778449824881928752177 5988583837368661446564133)
                    ·
                      refine ⟨1122859469506624021230775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5988583837368661446564133 1122859469506624021230775)
                      ·
                        rfl

theorem cell23_2186761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 2, 4].length) (baseStart_2186761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186761 prefixEnd_2186761 := by exact prefixLift 2186761
  have htrace : WordTrace (prefixWord ++ tailWord_2186761) baseStart_2186761 baseEnd_2186761 := by
    simpa [prefixWord, tailWord_2186761, baseEnd_2186761] using wordTrace_append hprefix tailTrace_2186761
  have hstable : (prefixWord ++ tailWord_2186761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186761).length < 2 ^ (prefixWord ++ tailWord_2186761).sum := by decide
  have hdescent : baseEnd_2186761 < baseStart_2186761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186792 : List Nat := [2, 1, 5, 2, 3, 1, 1, 1, 1, 6]
def baseStart_2186792 : Nat := 118140960795 + 2186792 * 2 ^ 59
def prefixEnd_2186792 : Nat := 4983230072969 + 3 ^ 40 * 2186792 * 2
def baseEnd_2186792 : Nat := 374291795802304466647711

theorem tailTrace_2186792 : CollatzResearch.WordTrace tailWord_2186792 prefixEnd_2186792 374291795802304466647711 := by
  unfold tailWord_2186792
  simp only [CollatzResearch.WordTrace]
  refine ⟨39879428346816766592449315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53172571129089022123265753 39879428346816766592449315)
  ·
    refine ⟨59819142520225149888673973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39879428346816766592449315 59819142520225149888673973)
    ·
      refine ⟨5608044611271107802063185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59819142520225149888673973 5608044611271107802063185)
      ·
        refine ⟨4206033458453330851547389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5608044611271107802063185 4206033458453330851547389)
        ·
          refine ⟨1577262546919999069330271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4206033458453330851547389 1577262546919999069330271)
          ·
            refine ⟨2365893820379998603995407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1577262546919999069330271 2365893820379998603995407)
            ·
              refine ⟨3548840730569997905993111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2365893820379998603995407 3548840730569997905993111)
              ·
                refine ⟨5323261095854996858989667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3548840730569997905993111 5323261095854996858989667)
                ·
                  refine ⟨7984891643782495288484501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5323261095854996858989667 7984891643782495288484501)
                  ·
                    refine ⟨374291795802304466647711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7984891643782495288484501 374291795802304466647711)
                    ·
                      rfl

theorem cell23_2186792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_2186792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186792 prefixEnd_2186792 := by exact prefixLift 2186792
  have htrace : WordTrace (prefixWord ++ tailWord_2186792) baseStart_2186792 baseEnd_2186792 := by
    simpa [prefixWord, tailWord_2186792, baseEnd_2186792] using wordTrace_append hprefix tailTrace_2186792
  have hstable : (prefixWord ++ tailWord_2186792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186792).length < 2 ^ (prefixWord ++ tailWord_2186792).sum := by decide
  have hdescent : baseEnd_2186792 < baseStart_2186792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186822 : List Nat := [6, 1, 1, 1, 4, 1, 9]
def baseStart_2186822 : Nat := 118140960795 + 2186822 * 2 ^ 59
def prefixEnd_2186822 : Nat := 4983230072969 + 3 ^ 40 * 2186822 * 2
def baseEnd_2186822 : Nat := 13862849281809238056395

theorem tailTrace_2186822 : CollatzResearch.WordTrace tailWord_2186822 prefixEnd_2186822 13862849281809238056395 := by
  unfold tailWord_2186822
  simp only [CollatzResearch.WordTrace]
  refine ⟨2492498465110151509640335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53173300589016565538993813 2492498465110151509640335)
  ·
    refine ⟨3738747697665227264460503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2492498465110151509640335 3738747697665227264460503)
    ·
      refine ⟨5608121546497840896690755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3738747697665227264460503 5608121546497840896690755)
      ·
        refine ⟨8412182319746761345036133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5608121546497840896690755 8412182319746761345036133)
        ·
          refine ⟨1577284184952517752194275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8412182319746761345036133 1577284184952517752194275)
          ·
            refine ⟨2365926277428776628291413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1577284184952517752194275 2365926277428776628291413)
            ·
              refine ⟨13862849281809238056395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2365926277428776628291413 13862849281809238056395)
              ·
                rfl

theorem cell23_2186822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 9].length) (baseStart_2186822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186822 prefixEnd_2186822 := by exact prefixLift 2186822
  have htrace : WordTrace (prefixWord ++ tailWord_2186822) baseStart_2186822 baseEnd_2186822 := by
    simpa [prefixWord, tailWord_2186822, baseEnd_2186822] using wordTrace_append hprefix tailTrace_2186822
  have hstable : (prefixWord ++ tailWord_2186822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186822).length < 2 ^ (prefixWord ++ tailWord_2186822).sum := by decide
  have hdescent : baseEnd_2186822 < baseStart_2186822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186858 : List Nat := [3, 1, 3, 2, 1, 2, 1, 2, 2, 1, 5]
def baseStart_2186858 : Nat := 118140960795 + 2186858 * 2 ^ 59
def prefixEnd_2186858 : Nat := 4983230072969 + 3 ^ 40 * 2186858 * 2
def baseEnd_2186858 : Nat := 1122909277130110141717829

theorem tailTrace_2186858 : CollatzResearch.WordTrace tailWord_2186858 prefixEnd_2186858 1122909277130110141717829 := by
  unfold tailWord_2186858
  simp only [CollatzResearch.WordTrace]
  refine ⟨19940315977848606614200307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53174175940929617637867485 19940315977848606614200307)
  ·
    refine ⟨29910473966772909921300461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19940315977848606614200307 29910473966772909921300461)
    ·
      refine ⟨11216427737539841220487673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29910473966772909921300461 11216427737539841220487673)
      ·
        refine ⟨8412320803154880915365755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11216427737539841220487673 8412320803154880915365755)
        ·
          refine ⟨12618481204732321373048633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8412320803154880915365755 12618481204732321373048633)
          ·
            refine ⟨9463860903549241029786475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12618481204732321373048633 9463860903549241029786475)
            ·
              refine ⟨14195791355323861544679713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9463860903549241029786475 14195791355323861544679713)
              ·
                refine ⟨10646843516492896158509785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14195791355323861544679713 10646843516492896158509785)
                ·
                  refine ⟨7985132637369672118882339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10646843516492896158509785 7985132637369672118882339)
                  ·
                    refine ⟨11977698956054508178323509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7985132637369672118882339 11977698956054508178323509)
                    ·
                      refine ⟨1122909277130110141717829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11977698956054508178323509 1122909277130110141717829)
                      ·
                        rfl

theorem cell23_2186858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_2186858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186858 prefixEnd_2186858 := by exact prefixLift 2186858
  have htrace : WordTrace (prefixWord ++ tailWord_2186858) baseStart_2186858 baseEnd_2186858 := by
    simpa [prefixWord, tailWord_2186858, baseEnd_2186858] using wordTrace_append hprefix tailTrace_2186858
  have hstable : (prefixWord ++ tailWord_2186858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186858).length < 2 ^ (prefixWord ++ tailWord_2186858).sum := by decide
  have hdescent : baseEnd_2186858 < baseStart_2186858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186958 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6]
def baseStart_2186958 : Nat := 118140960795 + 2186958 * 2 ^ 59
def prefixEnd_2186958 : Nat := 4983230072969 + 3 ^ 40 * 2186958 * 2
def baseEnd_2186958 : Nat := 1122960625195559750467369

theorem tailTrace_2186958 : CollatzResearch.WordTrace tailWord_2186958 prefixEnd_2186958 1122960625195559750467369 := by
  unfold tailWord_2186958
  simp only [CollatzResearch.WordTrace]
  refine ⟨9970613901379017941930191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53176607474021429023627685 9970613901379017941930191)
  ·
    refine ⟨14955920852068526912895287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9970613901379017941930191 14955920852068526912895287)
    ·
      refine ⟨22433881278102790369342931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14955920852068526912895287 22433881278102790369342931)
      ·
        refine ⟨33650821917154185554014397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22433881278102790369342931 33650821917154185554014397)
        ·
          refine ⟨12619058218932819582755399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33650821917154185554014397 12619058218932819582755399)
          ·
            refine ⟨18928587328399229374133099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12619058218932819582755399 18928587328399229374133099)
            ·
              refine ⟨28392880992598844061199649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18928587328399229374133099 28392880992598844061199649)
              ·
                refine ⟨21294660744449133045899737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28392880992598844061199649 21294660744449133045899737)
                ·
                  refine ⟨15970995558336849784424803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21294660744449133045899737 15970995558336849784424803)
                  ·
                    refine ⟨23956493337505274676637205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15970995558336849784424803 23956493337505274676637205)
                    ·
                      refine ⟨1122960625195559750467369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23956493337505274676637205 1122960625195559750467369)
                      ·
                        rfl

theorem cell23_2186958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_2186958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186958 prefixEnd_2186958 := by exact prefixLift 2186958
  have htrace : WordTrace (prefixWord ++ tailWord_2186958) baseStart_2186958 baseEnd_2186958 := by
    simpa [prefixWord, tailWord_2186958, baseEnd_2186958] using wordTrace_append hprefix tailTrace_2186958
  have hstable : (prefixWord ++ tailWord_2186958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186958).length < 2 ^ (prefixWord ++ tailWord_2186958).sum := by decide
  have hdescent : baseEnd_2186958 < baseStart_2186958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186962 : List Nat := [3, 2, 2, 2, 2, 1, 2, 1, 2, 4, 2]
def baseStart_2186962 : Nat := 118140960795 + 2186962 * 2 ^ 59
def prefixEnd_2186962 : Nat := 4983230072969 + 3 ^ 40 * 2186962 * 2
def baseEnd_2186962 : Nat := 1122962679118177734817351

theorem tailTrace_2186962 : CollatzResearch.WordTrace tailWord_2186962 prefixEnd_2186962 1122962679118177734817351 := by
  unfold tailWord_2186962
  simp only [CollatzResearch.WordTrace]
  refine ⟨19941264275754413054646785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53176704735345101479058093 19941264275754413054646785)
  ·
    refine ⟨14955948206815809790985089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19941264275754413054646785 14955948206815809790985089)
    ·
      refine ⟨11216961155111857343238817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14955948206815809790985089 11216961155111857343238817)
      ·
        refine ⟨8412720866333893007429113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11216961155111857343238817 8412720866333893007429113)
        ·
          refine ⟨6309540649750419755571835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8412720866333893007429113 6309540649750419755571835)
          ·
            refine ⟨9464310974625629633357753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6309540649750419755571835 9464310974625629633357753)
            ·
              refine ⟨7098233230969222225018315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9464310974625629633357753 7098233230969222225018315)
              ·
                refine ⟨10647349846453833337527473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7098233230969222225018315 10647349846453833337527473)
                ·
                  refine ⟨7985512384840375003145605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10647349846453833337527473 7985512384840375003145605)
                  ·
                    refine ⟨1497283572157570313089801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7985512384840375003145605 1497283572157570313089801)
                    ·
                      refine ⟨1122962679118177734817351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1497283572157570313089801 1122962679118177734817351)
                      ·
                        rfl

theorem cell23_2186962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_2186962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186962 prefixEnd_2186962 := by exact prefixLift 2186962
  have htrace : WordTrace (prefixWord ++ tailWord_2186962) baseStart_2186962 baseEnd_2186962 := by
    simpa [prefixWord, tailWord_2186962, baseEnd_2186962] using wordTrace_append hprefix tailTrace_2186962
  have hstable : (prefixWord ++ tailWord_2186962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186962).length < 2 ^ (prefixWord ++ tailWord_2186962).sum := by decide
  have hdescent : baseEnd_2186962 < baseStart_2186962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186989 : List Nat := [1, 5, 1, 2, 1, 2, 3, 3, 1, 4]
def baseStart_2186989 : Nat := 118140960795 + 2186989 * 2 ^ 59
def prefixEnd_2186989 : Nat := 4983230072969 + 3 ^ 40 * 2186989 * 2
def baseEnd_2186989 : Nat := 374325514365283043059909

theorem tailTrace_2186989 : CollatzResearch.WordTrace tailWord_2186989 prefixEnd_2186989 374325514365283043059909 := by
  unfold tailWord_2186989
  simp only [CollatzResearch.WordTrace]
  refine ⟨79766041873919835829820021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53177361249279890553213347 79766041873919835829820021)
  ·
    refine ⟨7478066425679984609045627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79766041873919835829820021 7478066425679984609045627)
    ·
      refine ⟨11217099638519976913568441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7478066425679984609045627 11217099638519976913568441)
      ·
        refine ⟨8412824728889982685176331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11217099638519976913568441 8412824728889982685176331)
        ·
          refine ⟨12619237093334974027764497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8412824728889982685176331 12619237093334974027764497)
          ·
            refine ⟨9464427820001230520823373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12619237093334974027764497 9464427820001230520823373)
            ·
              refine ⟨3549160432500461445308765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9464427820001230520823373 3549160432500461445308765)
              ·
                refine ⟨1330935162187673041990787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3549160432500461445308765 1330935162187673041990787)
                ·
                  refine ⟨1996402743281509562986181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1330935162187673041990787 1996402743281509562986181)
                  ·
                    refine ⟨374325514365283043059909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1996402743281509562986181 374325514365283043059909)
                    ·
                      rfl

theorem cell23_2186989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_2186989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186989 prefixEnd_2186989 := by exact prefixLift 2186989
  have htrace : WordTrace (prefixWord ++ tailWord_2186989) baseStart_2186989 baseEnd_2186989 := by
    simpa [prefixWord, tailWord_2186989, baseEnd_2186989] using wordTrace_append hprefix tailTrace_2186989
  have hstable : (prefixWord ++ tailWord_2186989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186989).length < 2 ^ (prefixWord ++ tailWord_2186989).sum := by decide
  have hdescent : baseEnd_2186989 < baseStart_2186989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2186995 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 5, 1, 3]
def baseStart_2186995 : Nat := 118140960795 + 2186995 * 2 ^ 59
def prefixEnd_2186995 : Nat := 4983230072969 + 3 ^ 40 * 2186995 * 2
def baseEnd_2186995 : Nat := 1122979623979776105704699

theorem tailTrace_2186995 : CollatzResearch.WordTrace tailWord_2186995 prefixEnd_2186995 1122979623979776105704699 := by
  unfold tailWord_2186995
  simp only [CollatzResearch.WordTrace]
  refine ⟨79766260711898098854538439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53177507141265399236358959 79766260711898098854538439)
  ·
    refine ⟨119649391067847148281807659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79766260711898098854538439 119649391067847148281807659)
    ·
      refine ⟨179474086601770722422711489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119649391067847148281807659 179474086601770722422711489)
      ·
        refine ⟨134605564951328041817033617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179474086601770722422711489 134605564951328041817033617)
        ·
          refine ⟨100954173713496031362775213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134605564951328041817033617 100954173713496031362775213)
          ·
            refine ⟨37857815142561011761040705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100954173713496031362775213 37857815142561011761040705)
            ·
              refine ⟨28393361356920758820780529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37857815142561011761040705 28393361356920758820780529)
              ·
                refine ⟨21295021017690569115585397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28393361356920758820780529 21295021017690569115585397)
                ·
                  refine ⟨1996408220408490854586131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21295021017690569115585397 1996408220408490854586131)
                  ·
                    refine ⟨2994612330612736281879197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1996408220408490854586131 2994612330612736281879197)
                    ·
                      refine ⟨1122979623979776105704699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2994612330612736281879197 1122979623979776105704699)
                      ·
                        rfl

theorem cell23_2186995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 5, 1, 3].length) (baseStart_2186995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2186995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2186995 prefixEnd_2186995 := by exact prefixLift 2186995
  have htrace : WordTrace (prefixWord ++ tailWord_2186995) baseStart_2186995 baseEnd_2186995 := by
    simpa [prefixWord, tailWord_2186995, baseEnd_2186995] using wordTrace_append hprefix tailTrace_2186995
  have hstable : (prefixWord ++ tailWord_2186995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2186995).length < 2 ^ (prefixWord ++ tailWord_2186995).sum := by decide
  have hdescent : baseEnd_2186995 < baseStart_2186995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2186995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187005 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 3, 5, 2]
def baseStart_2187005 : Nat := 118140960795 + 2187005 * 2 ^ 59
def prefixEnd_2187005 : Nat := 4983230072969 + 3 ^ 40 * 2187005 * 2
def baseEnd_2187005 : Nat := 1122984758786321066579653

theorem tailTrace_2187005 : CollatzResearch.WordTrace tailWord_2187005 prefixEnd_2187005 1122984758786321066579653 := by
  unfold tailWord_2187005
  simp only [CollatzResearch.WordTrace]
  refine ⟨79766625441861870562402469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53177750294574580374934979 79766625441861870562402469)
  ·
    refine ⟨14956242270349100730450463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79766625441861870562402469 14956242270349100730450463)
    ·
      refine ⟨22434363405523651095675695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14956242270349100730450463 22434363405523651095675695)
      ·
        refine ⟨33651545108285476643513543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22434363405523651095675695 33651545108285476643513543)
        ·
          refine ⟨50477317662428214965270315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33651545108285476643513543 50477317662428214965270315)
          ·
            refine ⟨75715976493642322447905473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50477317662428214965270315 75715976493642322447905473)
            ·
              refine ⟨56786982370231741835929105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75715976493642322447905473 56786982370231741835929105)
              ·
                refine ⟨42590236777673806376946829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56786982370231741835929105 42590236777673806376946829)
                ·
                  refine ⟨15971338791627677391355061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42590236777673806376946829 15971338791627677391355061)
                  ·
                    refine ⟨1497313011715094755439537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15971338791627677391355061 1497313011715094755439537)
                    ·
                      refine ⟨1122984758786321066579653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1497313011715094755439537 1122984758786321066579653)
                      ·
                        rfl

theorem cell23_2187005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 5, 2].length) (baseStart_2187005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187005 prefixEnd_2187005 := by exact prefixLift 2187005
  have htrace : WordTrace (prefixWord ++ tailWord_2187005) baseStart_2187005 baseEnd_2187005 := by
    simpa [prefixWord, tailWord_2187005, baseEnd_2187005] using wordTrace_append hprefix tailTrace_2187005
  have hstable : (prefixWord ++ tailWord_2187005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187005).length < 2 ^ (prefixWord ++ tailWord_2187005).sum := by decide
  have hdescent : baseEnd_2187005 < baseStart_2187005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187006 : List Nat := [4, 2, 2, 1, 4, 1, 1, 1, 3, 4]
def baseStart_2187006 : Nat := 118140960795 + 2187006 * 2 ^ 59
def prefixEnd_2187006 : Nat := 4983230072969 + 3 ^ 40 * 2187006 * 2
def baseEnd_2187006 : Nat := 374328424088991854222383

theorem tailTrace_2187006 : CollatzResearch.WordTrace tailWord_2187006 prefixEnd_2187006 374328424088991854222383 := by
  unfold tailWord_2187006
  simp only [CollatzResearch.WordTrace]
  refine ⟨9970832739357280966648609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53177774609905498488792581 9970832739357280966648609)
  ·
    refine ⟨7478124554517960724986457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9970832739357280966648609 7478124554517960724986457)
    ·
      refine ⟨5608593415888470543739843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7478124554517960724986457 5608593415888470543739843)
      ·
        refine ⟨8412890123832705815609765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5608593415888470543739843 8412890123832705815609765)
        ·
          refine ⟨1577416898218632340426831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8412890123832705815609765 1577416898218632340426831)
          ·
            refine ⟨2366125347327948510640247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1577416898218632340426831 2366125347327948510640247)
            ·
              refine ⟨3549188020991922765960371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2366125347327948510640247 3549188020991922765960371)
              ·
                refine ⟨5323782031487884148940557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3549188020991922765960371 5323782031487884148940557)
                ·
                  refine ⟨1996418261807956555852709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5323782031487884148940557 1996418261807956555852709)
                  ·
                    refine ⟨374328424088991854222383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1996418261807956555852709 374328424088991854222383)
                    ·
                      rfl

theorem cell23_2187006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_2187006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187006 prefixEnd_2187006 := by exact prefixLift 2187006
  have htrace : WordTrace (prefixWord ++ tailWord_2187006) baseStart_2187006 baseEnd_2187006 := by
    simpa [prefixWord, tailWord_2187006, baseEnd_2187006] using wordTrace_append hprefix tailTrace_2187006
  have hstable : (prefixWord ++ tailWord_2187006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187006).length < 2 ^ (prefixWord ++ tailWord_2187006).sum := by decide
  have hdescent : baseEnd_2187006 < baseStart_2187006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187045 : List Nat := [1, 3, 1, 2, 3, 3, 1, 2, 1, 6]
def baseStart_2187045 : Nat := 118140960795 + 2187045 * 2 ^ 59
def prefixEnd_2187045 : Nat := 4983230072969 + 3 ^ 40 * 2187045 * 2
def baseEnd_2187045 : Nat := 374335099337500303359823

theorem tailTrace_2187045 : CollatzResearch.WordTrace tailWord_2187045 prefixEnd_2187045 374335099337500303359823 := by
  unfold tailWord_2187045
  simp only [CollatzResearch.WordTrace]
  refine ⟨79768084361716957393858589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53178722907811304929239059 79768084361716957393858589)
  ·
    refine ⟨29913031635643859022696971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79768084361716957393858589 29913031635643859022696971)
    ·
      refine ⟨44869547453465788534045457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29913031635643859022696971 44869547453465788534045457)
      ·
        refine ⟨33652160590099341400534093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44869547453465788534045457 33652160590099341400534093)
        ·
          refine ⟨12619560221287253025200285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33652160590099341400534093 12619560221287253025200285)
          ·
            refine ⟨4732335082982719884450107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12619560221287253025200285 4732335082982719884450107)
            ·
              refine ⟨7098502624474079826675161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4732335082982719884450107 7098502624474079826675161)
              ·
                refine ⟨5323876968355559870006371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7098502624474079826675161 5323876968355559870006371)
                ·
                  refine ⟨7985815452533339805009557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5323876968355559870006371 7985815452533339805009557)
                  ·
                    refine ⟨374335099337500303359823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7985815452533339805009557 374335099337500303359823)
                    ·
                      rfl

theorem cell23_2187045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 6].length) (baseStart_2187045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187045 prefixEnd_2187045 := by exact prefixLift 2187045
  have htrace : WordTrace (prefixWord ++ tailWord_2187045) baseStart_2187045 baseEnd_2187045 := by
    simpa [prefixWord, tailWord_2187045, baseEnd_2187045] using wordTrace_append hprefix tailTrace_2187045
  have hstable : (prefixWord ++ tailWord_2187045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187045).length < 2 ^ (prefixWord ++ tailWord_2187045).sum := by decide
  have hdescent : baseEnd_2187045 < baseStart_2187045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187058 : List Nat := [3, 2, 1, 1, 3, 13]
def baseStart_2187058 : Nat := 118140960795 + 2187058 * 2 ^ 59
def prefixEnd_2187058 : Nat := 4983230072969 + 3 ^ 40 * 2187058 * 2
def baseEnd_2187058 : Nat := 4621448449633783371263

theorem tailTrace_2187058 : CollatzResearch.WordTrace tailWord_2187058 prefixEnd_2187058 4621448449633783371263 := by
  unfold tailWord_2187058
  simp only [CollatzResearch.WordTrace]
  refine ⟨19942139627667465153520457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53179039007113240409387885 19942139627667465153520457)
  ·
    refine ⟨14956604720750598865140343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19942139627667465153520457 14956604720750598865140343)
    ·
      refine ⟨22434907081125898297710515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14956604720750598865140343 22434907081125898297710515)
      ·
        refine ⟨33652360621688847446565773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22434907081125898297710515 33652360621688847446565773)
        ·
          refine ⟨12619635233133317792462165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33652360621688847446565773 12619635233133317792462165)
          ·
            refine ⟨4621448449633783371263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 12619635233133317792462165 4621448449633783371263)
            ·
              rfl

theorem cell23_2187058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 13].length) (baseStart_2187058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187058 prefixEnd_2187058 := by exact prefixLift 2187058
  have htrace : WordTrace (prefixWord ++ tailWord_2187058) baseStart_2187058 baseEnd_2187058 := by
    simpa [prefixWord, tailWord_2187058, baseEnd_2187058] using wordTrace_append hprefix tailTrace_2187058
  have hstable : (prefixWord ++ tailWord_2187058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187058).length < 2 ^ (prefixWord ++ tailWord_2187058).sum := by decide
  have hdescent : baseEnd_2187058 < baseStart_2187058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187075 : List Nat := [1, 1, 1, 3, 1, 7, 1, 8]
def baseStart_2187075 : Nat := 118140960795 + 2187075 * 2 ^ 59
def prefixEnd_2187075 : Nat := 4983230072969 + 3 ^ 40 * 2187075 * 2
def baseEnd_2187075 : Nat := 41593359349338362692753

theorem tailTrace_2187075 : CollatzResearch.WordTrace tailWord_2187075 prefixEnd_2187075 41593359349338362692753 := by
  unfold tailWord_2187075
  simp only [CollatzResearch.WordTrace]
  refine ⟨79769178551608272517450679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53179452367738848344967119 79769178551608272517450679)
  ·
    refine ⟨119653767827412408776176019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79769178551608272517450679 119653767827412408776176019)
    ·
      refine ⟨179480651741118613164264029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119653767827412408776176019 179480651741118613164264029)
      ·
        refine ⟨67305244402919479936599011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179480651741118613164264029 67305244402919479936599011)
        ·
          refine ⟨100957866604379219904898517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67305244402919479936599011 100957866604379219904898517)
          ·
            refine ⟨2366199998540137966521059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 100957866604379219904898517 2366199998540137966521059)
            ·
              refine ⟨3549299997810206949781589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2366199998540137966521059 3549299997810206949781589)
              ·
                refine ⟨41593359349338362692753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3549299997810206949781589 41593359349338362692753)
                ·
                  rfl

theorem cell23_2187075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 8].length) (baseStart_2187075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187075 prefixEnd_2187075 := by exact prefixLift 2187075
  have htrace : WordTrace (prefixWord ++ tailWord_2187075) baseStart_2187075 baseEnd_2187075 := by
    simpa [prefixWord, tailWord_2187075, baseEnd_2187075] using wordTrace_append hprefix tailTrace_2187075
  have hstable : (prefixWord ++ tailWord_2187075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187075).length < 2 ^ (prefixWord ++ tailWord_2187075).sum := by decide
  have hdescent : baseEnd_2187075 < baseStart_2187075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187088 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 4, 7]
def baseStart_2187088 : Nat := 118140960795 + 2187088 * 2 ^ 59
def prefixEnd_2187088 : Nat := 4983230072969 + 3 ^ 40 * 2187088 * 2
def baseEnd_2187088 : Nat := 374342459226881413947257

theorem tailTrace_2187088 : CollatzResearch.WordTrace tailWord_2187088 prefixEnd_2187088 374342459226881413947257 := by
  unfold tailWord_2187088
  simp only [CollatzResearch.WordTrace]
  refine ⟨39884826350280587868836959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53179768467040783825115945 39884826350280587868836959)
  ·
    refine ⟨59827239525420881803255439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39884826350280587868836959 59827239525420881803255439)
    ·
      refine ⟨89740859288131322704883159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59827239525420881803255439 89740859288131322704883159)
      ·
        refine ⟨134611288932196984057324739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89740859288131322704883159 134611288932196984057324739)
        ·
          refine ⟨201916933398295476085987109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134611288932196984057324739 201916933398295476085987109)
          ·
            refine ⟨37859425012180401766122583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 201916933398295476085987109 37859425012180401766122583)
            ·
              refine ⟨56789137518270602649183875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37859425012180401766122583 56789137518270602649183875)
              ·
                refine ⟨85183706277405903973775813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56789137518270602649183875 85183706277405903973775813)
                ·
                  refine ⟨15971944927013606995082965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85183706277405903973775813 15971944927013606995082965)
                  ·
                    refine ⟨374342459226881413947257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15971944927013606995082965 374342459226881413947257)
                    ·
                      rfl

theorem cell23_2187088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 4, 7].length) (baseStart_2187088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187088 prefixEnd_2187088 := by exact prefixLift 2187088
  have htrace : WordTrace (prefixWord ++ tailWord_2187088) baseStart_2187088 baseEnd_2187088 := by
    simpa [prefixWord, tailWord_2187088, baseEnd_2187088] using wordTrace_append hprefix tailTrace_2187088
  have hstable : (prefixWord ++ tailWord_2187088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187088).length < 2 ^ (prefixWord ++ tailWord_2187088).sum := by decide
  have hdescent : baseEnd_2187088 < baseStart_2187088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187092 : List Nat := [2, 4, 1, 1, 3, 2, 3, 7]
def baseStart_2187092 : Nat := 118140960795 + 2187092 * 2 ^ 59
def prefixEnd_2187092 : Nat := 4983230072969 + 3 ^ 40 * 2187092 * 2
def baseEnd_2187092 : Nat := 41593682651972675044139

theorem tailTrace_2187092 : CollatzResearch.WordTrace tailWord_2187092 prefixEnd_2187092 41593682651972675044139 := by
  unfold tailWord_2187092
  simp only [CollatzResearch.WordTrace]
  refine ⟨39884899296273342210409765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53179865728364456280546353 39884899296273342210409765)
  ·
    refine ⟨7478418618051251664451831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39884899296273342210409765 7478418618051251664451831)
    ·
      refine ⟨11217627927076877496677747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7478418618051251664451831 11217627927076877496677747)
      ·
        refine ⟨16826441890615316245016621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11217627927076877496677747 16826441890615316245016621)
        ·
          refine ⟨6309915708980743591881233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16826441890615316245016621 6309915708980743591881233)
          ·
            refine ⟨4732436781735557693910925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6309915708980743591881233 4732436781735557693910925)
            ·
              refine ⟨1774663793150834135216597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4732436781735557693910925 1774663793150834135216597)
              ·
                refine ⟨41593682651972675044139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1774663793150834135216597 41593682651972675044139)
                ·
                  rfl

theorem cell23_2187092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 7].length) (baseStart_2187092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187092 prefixEnd_2187092 := by exact prefixLift 2187092
  have htrace : WordTrace (prefixWord ++ tailWord_2187092) baseStart_2187092 baseEnd_2187092 := by
    simpa [prefixWord, tailWord_2187092, baseEnd_2187092] using wordTrace_append hprefix tailTrace_2187092
  have hstable : (prefixWord ++ tailWord_2187092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187092).length < 2 ^ (prefixWord ++ tailWord_2187092).sum := by decide
  have hdescent : baseEnd_2187092 < baseStart_2187092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187106 : List Nat := [3, 3, 2, 1, 2, 1, 4, 1, 1, 2, 3]
def baseStart_2187106 : Nat := 118140960795 + 2187106 * 2 ^ 59
def prefixEnd_2187106 : Nat := 4983230072969 + 3 ^ 40 * 2187106 * 2
def baseEnd_2187106 : Nat := 1123036620332425171416689

theorem tailTrace_2187106 : CollatzResearch.WordTrace tailWord_2187106 prefixEnd_2187106 1123036620332425171416689 := by
  unfold tailWord_2187106
  simp only [CollatzResearch.WordTrace]
  refine ⟨19942577303623991202957293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53180206142997309874552781 19942577303623991202957293)
  ·
    refine ⟨7478466488858996701108985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19942577303623991202957293 7478466488858996701108985)
    ·
      refine ⟨5608849866644247525831739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7478466488858996701108985 5608849866644247525831739)
      ·
        refine ⟨8413274799966371288747609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5608849866644247525831739 8413274799966371288747609)
        ·
          refine ⟨6309956099974778466560707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8413274799966371288747609 6309956099974778466560707)
          ·
            refine ⟨9464934149962167699841061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6309956099974778466560707 9464934149962167699841061)
            ·
              refine ⟨1774675153117906443720199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9464934149962167699841061 1774675153117906443720199)
              ·
                refine ⟨2662012729676859665580299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1774675153117906443720199 2662012729676859665580299)
                ·
                  refine ⟨3993019094515289498370449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2662012729676859665580299 3993019094515289498370449)
                  ·
                    refine ⟨2994764320886467123777837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3993019094515289498370449 2994764320886467123777837)
                    ·
                      refine ⟨1123036620332425171416689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2994764320886467123777837 1123036620332425171416689)
                      ·
                        rfl

theorem cell23_2187106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_2187106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187106 prefixEnd_2187106 := by exact prefixLift 2187106
  have htrace : WordTrace (prefixWord ++ tailWord_2187106) baseStart_2187106 baseEnd_2187106 := by
    simpa [prefixWord, tailWord_2187106, baseEnd_2187106] using wordTrace_append hprefix tailTrace_2187106
  have hstable : (prefixWord ++ tailWord_2187106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187106).length < 2 ^ (prefixWord ++ tailWord_2187106).sum := by decide
  have hdescent : baseEnd_2187106 < baseStart_2187106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187145 : List Nat := [1, 2, 1, 1, 5, 1, 2, 2, 2, 1, 5]
def baseStart_2187145 : Nat := 118140960795 + 2187145 * 2 ^ 59
def prefixEnd_2187145 : Nat := 4983230072969 + 3 ^ 40 * 2187145 * 2
def baseEnd_2187145 : Nat := 1123056646077950518829009

theorem tailTrace_2187145 : CollatzResearch.WordTrace tailWord_2187145 prefixEnd_2187145 1123056646077950518829009 := by
  unfold tailWord_2187145
  simp only [CollatzResearch.WordTrace]
  refine ⟨79771731661354674472498889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53181154440903116314999259 79771731661354674472498889)
  ·
    refine ⟨59828798746016005854374167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79771731661354674472498889 59828798746016005854374167)
    ·
      refine ⟨89743198119024008781561251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59828798746016005854374167 89743198119024008781561251)
      ·
        refine ⟨134614797178536013172341877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89743198119024008781561251 134614797178536013172341877)
        ·
          refine ⟨12620137235487751234907051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 134614797178536013172341877 12620137235487751234907051)
          ·
            refine ⟨18930205853231626852360577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12620137235487751234907051 18930205853231626852360577)
            ·
              refine ⟨14197654389923720139270433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18930205853231626852360577 14197654389923720139270433)
              ·
                refine ⟨10648240792442790104452825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14197654389923720139270433 10648240792442790104452825)
                ·
                  refine ⟨7986180594332092578339619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10648240792442790104452825 7986180594332092578339619)
                  ·
                    refine ⟨11979270891498138867509429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7986180594332092578339619 11979270891498138867509429)
                    ·
                      refine ⟨1123056646077950518829009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11979270891498138867509429 1123056646077950518829009)
                      ·
                        rfl

theorem cell23_2187145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 1, 5].length) (baseStart_2187145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187145 prefixEnd_2187145 := by exact prefixLift 2187145
  have htrace : WordTrace (prefixWord ++ tailWord_2187145) baseStart_2187145 baseEnd_2187145 := by
    simpa [prefixWord, tailWord_2187145, baseEnd_2187145] using wordTrace_append hprefix tailTrace_2187145
  have hstable : (prefixWord ++ tailWord_2187145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187145).length < 2 ^ (prefixWord ++ tailWord_2187145).sum := by decide
  have hdescent : baseEnd_2187145 < baseStart_2187145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187159 : List Nat := [1, 1, 3, 3, 1, 3, 1, 2, 4, 2, 2]
def baseStart_2187159 : Nat := 118140960795 + 2187159 * 2 ^ 59
def prefixEnd_2187159 : Nat := 4983230072969 + 3 ^ 40 * 2187159 * 2
def baseEnd_2187159 : Nat := 1123063834807113464053945

theorem tailTrace_2187159 : CollatzResearch.WordTrace tailWord_2187159 prefixEnd_2187159 1123063834807113464053945 := by
  unfold tailWord_2187159
  simp only [CollatzResearch.WordTrace]
  refine ⟨79772242283303954863508531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53181494855535969909005687 79772242283303954863508531)
  ·
    refine ⟨119658363424955932295262797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79772242283303954863508531 119658363424955932295262797)
    ·
      refine ⟨44871886284358474610723549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119658363424955932295262797 44871886284358474610723549)
      ·
        refine ⟨16826957356634427979021331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44871886284358474610723549 16826957356634427979021331)
        ·
          refine ⟨25240436034951641968531997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16826957356634427979021331 25240436034951641968531997)
          ·
            refine ⟨9465163513106865738199499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25240436034951641968531997 9465163513106865738199499)
            ·
              refine ⟨14197745269660298607299249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9465163513106865738199499 14197745269660298607299249)
              ·
                refine ⟨10648308952245223955474437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14197745269660298607299249 10648308952245223955474437)
                ·
                  refine ⟨1996557928545979491651457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10648308952245223955474437 1996557928545979491651457)
                  ·
                    refine ⟨1497418446409484618738593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1996557928545979491651457 1497418446409484618738593)
                    ·
                      refine ⟨1123063834807113464053945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1497418446409484618738593 1123063834807113464053945)
                      ·
                        rfl

theorem cell23_2187159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_2187159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187159 prefixEnd_2187159 := by exact prefixLift 2187159
  have htrace : WordTrace (prefixWord ++ tailWord_2187159) baseStart_2187159 baseEnd_2187159 := by
    simpa [prefixWord, tailWord_2187159, baseEnd_2187159] using wordTrace_append hprefix tailTrace_2187159
  have hstable : (prefixWord ++ tailWord_2187159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187159).length < 2 ^ (prefixWord ++ tailWord_2187159).sum := by decide
  have hdescent : baseEnd_2187159 < baseStart_2187159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187162 : List Nat := [3, 1, 1, 4, 2, 2, 1, 1, 2, 1, 5]
def baseStart_2187162 : Nat := 118140960795 + 2187162 * 2 ^ 59
def prefixEnd_2187162 : Nat := 4983230072969 + 3 ^ 40 * 2187162 * 2
def baseEnd_2187162 : Nat := 1123065375249076952316431

theorem tailTrace_2187162 : CollatzResearch.WordTrace tailWord_2187162 prefixEnd_2187162 1123065375249076952316431 := by
  unfold tailWord_2187162
  simp only [CollatzResearch.WordTrace]
  refine ⟨19943087925573271593966935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53181567801528724250578493 19943087925573271593966935)
  ·
    refine ⟨29914631888359907390950403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19943087925573271593966935 29914631888359907390950403)
    ·
      refine ⟨44871947832539861086425605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29914631888359907390950403 44871947832539861086425605)
      ·
        refine ⟨8413490218601223953704801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44871947832539861086425605 8413490218601223953704801)
        ·
          refine ⟨6310117663950917965278601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8413490218601223953704801 6310117663950917965278601)
          ·
            refine ⟨4732588247963188473958951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6310117663950917965278601 4732588247963188473958951)
            ·
              refine ⟨7098882371944782710938427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4732588247963188473958951 7098882371944782710938427)
              ·
                refine ⟨10648323557917174066407641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7098882371944782710938427 10648323557917174066407641)
                ·
                  refine ⟨7986242668437880549805731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10648323557917174066407641 7986242668437880549805731)
                  ·
                    refine ⟨11979364002656820824708597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7986242668437880549805731 11979364002656820824708597)
                    ·
                      refine ⟨1123065375249076952316431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11979364002656820824708597 1123065375249076952316431)
                      ·
                        rfl

theorem cell23_2187162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_2187162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187162 prefixEnd_2187162 := by exact prefixLift 2187162
  have htrace : WordTrace (prefixWord ++ tailWord_2187162) baseStart_2187162 baseEnd_2187162 := by
    simpa [prefixWord, tailWord_2187162, baseEnd_2187162] using wordTrace_append hprefix tailTrace_2187162
  have hstable : (prefixWord ++ tailWord_2187162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187162).length < 2 ^ (prefixWord ++ tailWord_2187162).sum := by decide
  have hdescent : baseEnd_2187162 < baseStart_2187162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187212 : List Nat := [2, 2, 1, 4, 1, 2, 1, 3, 2, 5]
def baseStart_2187212 : Nat := 118140960795 + 2187212 * 2 ^ 59
def prefixEnd_2187212 : Nat := 4983230072969 + 3 ^ 40 * 2187212 * 2
def baseEnd_2187212 : Nat := 374363683093933918897067

theorem tailTrace_2187212 : CollatzResearch.WordTrace tailWord_2187212 prefixEnd_2187212 374363683093933918897067 := by
  unfold tailWord_2187212
  simp only [CollatzResearch.WordTrace]
  refine ⟨39887087676055972457593945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53182783568074629943458593 39887087676055972457593945)
  ·
    refine ⟨29915315757041979343195459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39887087676055972457593945 29915315757041979343195459)
    ·
      refine ⟨44872973635562969014793189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29915315757041979343195459 44872973635562969014793189)
      ·
        refine ⟨8413682556668056690273723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44872973635562969014793189 8413682556668056690273723)
        ·
          refine ⟨12620523835002085035410585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8413682556668056690273723 12620523835002085035410585)
          ·
            refine ⟨9465392876251563776557939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12620523835002085035410585 9465392876251563776557939)
            ·
              refine ⟨14198089314377345664836909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9465392876251563776557939 14198089314377345664836909)
              ·
                refine ⟨5324283492891504624313841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14198089314377345664836909 5324283492891504624313841)
                ·
                  refine ⟨3993212619668628468235381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5324283492891504624313841 3993212619668628468235381)
                  ·
                    refine ⟨374363683093933918897067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3993212619668628468235381 374363683093933918897067)
                    ·
                      rfl

theorem cell23_2187212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 2, 5].length) (baseStart_2187212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187212 prefixEnd_2187212 := by exact prefixLift 2187212
  have htrace : WordTrace (prefixWord ++ tailWord_2187212) baseStart_2187212 baseEnd_2187212 := by
    simpa [prefixWord, tailWord_2187212, baseEnd_2187212] using wordTrace_append hprefix tailTrace_2187212
  have hstable : (prefixWord ++ tailWord_2187212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187212).length < 2 ^ (prefixWord ++ tailWord_2187212).sum := by decide
  have hdescent : baseEnd_2187212 < baseStart_2187212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187232 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 3, 6, 2]
def baseStart_2187232 : Nat := 118140960795 + 2187232 * 2 ^ 59
def prefixEnd_2187232 : Nat := 4983230072969 + 3 ^ 40 * 2187232 * 2
def baseEnd_2187232 : Nat := 1123101318894891678441109

theorem tailTrace_2187232 : CollatzResearch.WordTrace tailWord_2187232 prefixEnd_2187232 1123101318894891678441109 := by
  unfold tailWord_2187232
  simp only [CollatzResearch.WordTrace]
  refine ⟨39887452406019744165457975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53183269874692992220610633 39887452406019744165457975)
  ·
    refine ⟨59831178609029616248186963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39887452406019744165457975 59831178609029616248186963)
    ·
      refine ⟨89746767913544424372280445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59831178609029616248186963 89746767913544424372280445)
      ·
        refine ⟨33655037967579159139605167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89746767913544424372280445 33655037967579159139605167)
        ·
          refine ⟨50482556951368738709407751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33655037967579159139605167 50482556951368738709407751)
          ·
            refine ⟨75723835427053108064111627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50482556951368738709407751 75723835427053108064111627)
            ·
              refine ⟨113585753140579662096167441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75723835427053108064111627 113585753140579662096167441)
              ·
                refine ⟨85189314855434746572125581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113585753140579662096167441 85189314855434746572125581)
                ·
                  refine ⟨31945993070788029964547093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85189314855434746572125581 31945993070788029964547093)
                  ·
                    refine ⟨1497468425193188904588145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31945993070788029964547093 1497468425193188904588145)
                    ·
                      refine ⟨1123101318894891678441109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1497468425193188904588145 1123101318894891678441109)
                      ·
                        rfl

theorem cell23_2187232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 3, 6, 2].length) (baseStart_2187232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187232 prefixEnd_2187232 := by exact prefixLift 2187232
  have htrace : WordTrace (prefixWord ++ tailWord_2187232) baseStart_2187232 baseEnd_2187232 := by
    simpa [prefixWord, tailWord_2187232, baseEnd_2187232] using wordTrace_append hprefix tailTrace_2187232
  have hstable : (prefixWord ++ tailWord_2187232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187232).length < 2 ^ (prefixWord ++ tailWord_2187232).sum := by decide
  have hdescent : baseEnd_2187232 < baseStart_2187232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187269 : List Nat := [1, 3, 1, 1, 2, 4, 3, 1, 2, 2, 3]
def baseStart_2187269 : Nat := 118140960795 + 2187269 * 2 ^ 59
def prefixEnd_2187269 : Nat := 4983230072969 + 3 ^ 40 * 2187269 * 2
def baseEnd_2187269 : Nat := 1123120317679108033678439

theorem tailTrace_2187269 : CollatzResearch.WordTrace tailWord_2187269 prefixEnd_2187269 1123120317679108033678439 := by
  unfold tailWord_2187269
  simp only [CollatzResearch.WordTrace]
  refine ⟨79776254312905443650012861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53184169541936962433341907 79776254312905443650012861)
  ·
    refine ⟨29916095367339541368754823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79776254312905443650012861 29916095367339541368754823)
    ·
      refine ⟨44874143051009312053132235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29916095367339541368754823 44874143051009312053132235)
      ·
        refine ⟨67311214576513968079698353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44874143051009312053132235 67311214576513968079698353)
        ·
          refine ⟨50483410932385476059773765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67311214576513968079698353 50483410932385476059773765)
          ·
            refine ⟨9465639549822276761207581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50483410932385476059773765 9465639549822276761207581)
            ·
              refine ⟨3549614831183353785452843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9465639549822276761207581 3549614831183353785452843)
              ·
                refine ⟨5324422246775030678179265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3549614831183353785452843 5324422246775030678179265)
                ·
                  refine ⟨3993316685081273008634449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5324422246775030678179265 3993316685081273008634449)
                  ·
                    refine ⟨2994987513810954756475837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3993316685081273008634449 2994987513810954756475837)
                    ·
                      refine ⟨1123120317679108033678439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2994987513810954756475837 1123120317679108033678439)
                      ·
                        rfl

theorem cell23_2187269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 2, 3].length) (baseStart_2187269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187269 prefixEnd_2187269 := by exact prefixLift 2187269
  have htrace : WordTrace (prefixWord ++ tailWord_2187269) baseStart_2187269 baseEnd_2187269 := by
    simpa [prefixWord, tailWord_2187269, baseEnd_2187269] using wordTrace_append hprefix tailTrace_2187269
  have hstable : (prefixWord ++ tailWord_2187269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187269).length < 2 ^ (prefixWord ++ tailWord_2187269).sum := by decide
  have hdescent : baseEnd_2187269 < baseStart_2187269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187276 : List Nat := [2, 2, 1, 2, 3, 1, 4, 3, 1, 4]
def baseStart_2187276 : Nat := 118140960795 + 2187276 * 2 ^ 59
def prefixEnd_2187276 : Nat := 4983230072969 + 3 ^ 40 * 2187276 * 2
def baseEnd_2187276 : Nat := 374374637347896502096969

theorem tailTrace_2187276 : CollatzResearch.WordTrace tailWord_2187276 prefixEnd_2187276 374374637347896502096969 := by
  unfold tailWord_2187276
  simp only [CollatzResearch.WordTrace]
  refine ⟨39888254811940041922758841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53184339749253389230345121 39888254811940041922758841)
  ·
    refine ⟨29916191108955031442069131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39888254811940041922758841 29916191108955031442069131)
    ·
      refine ⟨44874286663432547163103697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29916191108955031442069131 44874286663432547163103697)
      ·
        refine ⟨33655714997574410372327773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44874286663432547163103697 33655714997574410372327773)
        ·
          refine ⟨12620893124090403889622915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33655714997574410372327773 12620893124090403889622915)
          ·
            refine ⟨18931339686135605834434373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12620893124090403889622915 18931339686135605834434373)
            ·
              refine ⟨3549626191150426093956445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18931339686135605834434373 3549626191150426093956445)
              ·
                refine ⟨1331109821681409785233667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3549626191150426093956445 1331109821681409785233667)
                ·
                  refine ⟨1996664732522114677850501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1331109821681409785233667 1996664732522114677850501)
                  ·
                    refine ⟨374374637347896502096969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1996664732522114677850501 374374637347896502096969)
                    ·
                      rfl

theorem cell23_2187276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 3, 1, 4].length) (baseStart_2187276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187276 prefixEnd_2187276 := by exact prefixLift 2187276
  have htrace : WordTrace (prefixWord ++ tailWord_2187276) baseStart_2187276 baseEnd_2187276 := by
    simpa [prefixWord, tailWord_2187276, baseEnd_2187276] using wordTrace_append hprefix tailTrace_2187276
  have hstable : (prefixWord ++ tailWord_2187276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187276).length < 2 ^ (prefixWord ++ tailWord_2187276).sum := by decide
  have hdescent : baseEnd_2187276 < baseStart_2187276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187292 : List Nat := [2, 2, 3, 1, 3, 1, 1, 1, 1, 2, 6]
def baseStart_2187292 : Nat := 118140960795 + 2187292 * 2 ^ 59
def prefixEnd_2187292 : Nat := 4983230072969 + 3 ^ 40 * 2187292 * 2
def baseEnd_2187292 : Nat := 1123132127734161443690833

theorem tailTrace_2187292 : CollatzResearch.WordTrace tailWord_2187292 prefixEnd_2187292 1123132127734161443690833 := by
  unfold tailWord_2187292
  simp only [CollatzResearch.WordTrace]
  refine ⟨39888546595911059289050065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53184728794548079052066753 39888546595911059289050065)
  ·
    refine ⟨29916409946933294466787549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39888546595911059289050065 29916409946933294466787549)
    ·
      refine ⟨11218653730099985425045331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29916409946933294466787549 11218653730099985425045331)
      ·
        refine ⟨16827980595149978137567997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11218653730099985425045331 16827980595149978137567997)
        ·
          refine ⟨6310492723181241801587999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16827980595149978137567997 6310492723181241801587999)
          ·
            refine ⟨9465739084771862702381999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6310492723181241801587999 9465739084771862702381999)
            ·
              refine ⟨14198608627157794053572999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9465739084771862702381999 14198608627157794053572999)
              ·
                refine ⟨21297912940736691080359499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14198608627157794053572999 21297912940736691080359499)
                ·
                  refine ⟨31946869411105036620539249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21297912940736691080359499 31946869411105036620539249)
                  ·
                    refine ⟨23960152058328777465404437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31946869411105036620539249 23960152058328777465404437)
                    ·
                      refine ⟨1123132127734161443690833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23960152058328777465404437 1123132127734161443690833)
                      ·
                        rfl

theorem cell23_2187292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_2187292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187292 prefixEnd_2187292 := by exact prefixLift 2187292
  have htrace : WordTrace (prefixWord ++ tailWord_2187292) baseStart_2187292 baseEnd_2187292 := by
    simpa [prefixWord, tailWord_2187292, baseEnd_2187292] using wordTrace_append hprefix tailTrace_2187292
  have hstable : (prefixWord ++ tailWord_2187292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187292).length < 2 ^ (prefixWord ++ tailWord_2187292).sum := by decide
  have hdescent : baseEnd_2187292 < baseStart_2187292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187306 : List Nat := [3, 1, 4, 1, 2, 2, 3, 1, 6]
def baseStart_2187306 : Nat := 118140960795 + 2187306 * 2 ^ 59
def prefixEnd_2187306 : Nat := 4983230072969 + 3 ^ 40 * 2187306 * 2
def baseEnd_2187306 : Nat := 124793257384813820990641

theorem tailTrace_2187306 : CollatzResearch.WordTrace tailWord_2187306 prefixEnd_2187306 124793257384813820990641 := by
  unfold tailWord_2187306
  simp only [CollatzResearch.WordTrace]
  refine ⟨19944400953442849742277443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53185069209180932646073181 19944400953442849742277443)
  ·
    refine ⟨29916601430164274613416165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19944400953442849742277443 29916601430164274613416165)
    ·
      refine ⟨5609362768155801490015531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29916601430164274613416165 5609362768155801490015531)
      ·
        refine ⟨8414044152233702235023297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5609362768155801490015531 8414044152233702235023297)
        ·
          refine ⟨6310533114175276676267473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8414044152233702235023297 6310533114175276676267473)
          ·
            refine ⟨4732899835631457507200605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6310533114175276676267473 4732899835631457507200605)
            ·
              refine ⟨1774837438361796565200227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4732899835631457507200605 1774837438361796565200227)
              ·
                refine ⟨2662256157542694847800341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1774837438361796565200227 2662256157542694847800341)
                ·
                  refine ⟨124793257384813820990641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2662256157542694847800341 124793257384813820990641)
                  ·
                    rfl

theorem cell23_2187306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 6].length) (baseStart_2187306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187306 prefixEnd_2187306 := by exact prefixLift 2187306
  have htrace : WordTrace (prefixWord ++ tailWord_2187306) baseStart_2187306 baseEnd_2187306 := by
    simpa [prefixWord, tailWord_2187306, baseEnd_2187306] using wordTrace_append hprefix tailTrace_2187306
  have hstable : (prefixWord ++ tailWord_2187306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187306).length < 2 ^ (prefixWord ++ tailWord_2187306).sum := by decide
  have hdescent : baseEnd_2187306 < baseStart_2187306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187349 : List Nat := [1, 3, 2, 2, 1, 3, 2, 1, 4, 4]
def baseStart_2187349 : Nat := 118140960795 + 2187349 * 2 ^ 59
def prefixEnd_2187349 : Nat := 4983230072969 + 3 ^ 40 * 2187349 * 2
def baseEnd_2187349 : Nat := 374387132043822573559357

theorem tailTrace_2187349 : CollatzResearch.WordTrace tailWord_2187349 prefixEnd_2187349 374387132043822573559357 := by
  unfold tailWord_2187349
  simp only [CollatzResearch.WordTrace]
  refine ⟨79779172152615617312925101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53186114768410411541950067 79779172152615617312925101)
  ·
    refine ⟨29917189557230856492346913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79779172152615617312925101 29917189557230856492346913)
    ·
      refine ⟨22437892167923142369260185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29917189557230856492346913 22437892167923142369260185)
      ·
        refine ⟨16828419125942356776945139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22437892167923142369260185 16828419125942356776945139)
        ·
          refine ⟨25242628688913535165417709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16828419125942356776945139 25242628688913535165417709)
          ·
            refine ⟨9465985758342575687031641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25242628688913535165417709 9465985758342575687031641)
            ·
              refine ⟨7099489318756931765273731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9465985758342575687031641 7099489318756931765273731)
              ·
                refine ⟨10649233978135397647910597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7099489318756931765273731 10649233978135397647910597)
                ·
                  refine ⟨1996731370900387058983237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10649233978135397647910597 1996731370900387058983237)
                  ·
                    refine ⟨374387132043822573559357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1996731370900387058983237 374387132043822573559357)
                    ·
                      rfl

theorem cell23_2187349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_2187349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187349 prefixEnd_2187349 := by exact prefixLift 2187349
  have htrace : WordTrace (prefixWord ++ tailWord_2187349) baseStart_2187349 baseEnd_2187349 := by
    simpa [prefixWord, tailWord_2187349, baseEnd_2187349] using wordTrace_append hprefix tailTrace_2187349
  have hstable : (prefixWord ++ tailWord_2187349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187349).length < 2 ^ (prefixWord ++ tailWord_2187349).sum := by decide
  have hdescent : baseEnd_2187349 < baseStart_2187349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187350 : List Nat := [5, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_2187350 : Nat := 118140960795 + 2187350 * 2 ^ 59
def prefixEnd_2187350 : Nat := 4983230072969 + 3 ^ 40 * 2187350 * 2
def baseEnd_2187350 : Nat := 1123161909612122216765567

theorem tailTrace_2187350 : CollatzResearch.WordTrace tailWord_2187350 prefixEnd_2187350 1123161909612122216765567 := by
  unfold tailWord_2187350
  simp only [CollatzResearch.WordTrace]
  refine ⟨4986200539100749655231969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53186139083741329655807669 4986200539100749655231969)
  ·
    refine ⟨3739650404325562241423977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4986200539100749655231969 3739650404325562241423977)
    ·
      refine ⟨2804737803244171681067983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3739650404325562241423977 2804737803244171681067983)
      ·
        refine ⟨4207106704866257521601975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2804737803244171681067983 4207106704866257521601975)
        ·
          refine ⟨6310660057299386282402963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4207106704866257521601975 6310660057299386282402963)
          ·
            refine ⟨9465990085949079423604445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6310660057299386282402963 9465990085949079423604445)
            ·
              refine ⟨3549746282230904783851667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9465990085949079423604445 3549746282230904783851667)
              ·
                refine ⟨5324619423346357175777501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3549746282230904783851667 5324619423346357175777501)
                ·
                  refine ⟨1996732283754883940916563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5324619423346357175777501 1996732283754883940916563)
                  ·
                    refine ⟨2995098425632325911374845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1996732283754883940916563 2995098425632325911374845)
                    ·
                      refine ⟨1123161909612122216765567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2995098425632325911374845 1123161909612122216765567)
                      ·
                        rfl

theorem cell23_2187350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_2187350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187350 prefixEnd_2187350 := by exact prefixLift 2187350
  have htrace : WordTrace (prefixWord ++ tailWord_2187350) baseStart_2187350 baseEnd_2187350 := by
    simpa [prefixWord, tailWord_2187350, baseEnd_2187350] using wordTrace_append hprefix tailTrace_2187350
  have hstable : (prefixWord ++ tailWord_2187350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187350).length < 2 ^ (prefixWord ++ tailWord_2187350).sum := by decide
  have hdescent : baseEnd_2187350 < baseStart_2187350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187352 : List Nat := [2, 1, 2, 2, 1, 4, 1, 2, 1, 1, 6]
def baseStart_2187352 : Nat := 118140960795 + 2187352 * 2 ^ 59
def prefixEnd_2187352 : Nat := 4983230072969 + 3 ^ 40 * 2187352 * 2
def baseEnd_2187352 : Nat := 1123162936573431208940557

theorem tailTrace_2187352 : CollatzResearch.WordTrace tailWord_2187352 prefixEnd_2187352 1123162936573431208940557 := by
  unfold tailWord_2187352
  simp only [CollatzResearch.WordTrace]
  refine ⟨39889640785802374412642155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53186187714403165883522873 39889640785802374412642155)
  ·
    refine ⟨59834461178703561618963233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39889640785802374412642155 59834461178703561618963233)
    ·
      refine ⟨44875845884027671214222425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59834461178703561618963233 44875845884027671214222425)
      ·
        refine ⟨33656884413020753410666819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44875845884027671214222425 33656884413020753410666819)
        ·
          refine ⟨50485326619531130116000229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33656884413020753410666819 50485326619531130116000229)
          ·
            refine ⟨9465998741162086896750043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50485326619531130116000229 9465998741162086896750043)
            ·
              refine ⟨14198998111743130345125065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9465998741162086896750043 14198998111743130345125065)
              ·
                refine ⟨10649248583807347758843799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14198998111743130345125065 10649248583807347758843799)
                ·
                  refine ⟨15973872875711021638265699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10649248583807347758843799 15973872875711021638265699)
                  ·
                    refine ⟨23960809313566532457398549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15973872875711021638265699 23960809313566532457398549)
                    ·
                      refine ⟨1123162936573431208940557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23960809313566532457398549 1123162936573431208940557)
                      ·
                        rfl

theorem cell23_2187352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_2187352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187352 prefixEnd_2187352 := by exact prefixLift 2187352
  have htrace : WordTrace (prefixWord ++ tailWord_2187352) baseStart_2187352 baseEnd_2187352 := by
    simpa [prefixWord, tailWord_2187352, baseEnd_2187352] using wordTrace_append hprefix tailTrace_2187352
  have hstable : (prefixWord ++ tailWord_2187352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187352).length < 2 ^ (prefixWord ++ tailWord_2187352).sum := by decide
  have hdescent : baseEnd_2187352 < baseStart_2187352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187376 : List Nat := [2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 3]
def baseStart_2187376 : Nat := 118140960795 + 2187376 * 2 ^ 59
def prefixEnd_2187376 : Nat := 4983230072969 + 3 ^ 40 * 2187376 * 2
def baseEnd_2187376 : Nat := 1123175260109139115040447

theorem tailTrace_2187376 : CollatzResearch.WordTrace tailWord_2187376 prefixEnd_2187376 1123175260109139115040447 := by
  unfold tailWord_2187376
  simp only [CollatzResearch.WordTrace]
  refine ⟨39890078461758900462078991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53186771282345200616105321 39890078461758900462078991)
  ·
    refine ⟨59835117692638350693118487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39890078461758900462078991 59835117692638350693118487)
    ·
      refine ⟨89752676538957526039677731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59835117692638350693118487 89752676538957526039677731)
      ·
        refine ⟨134629014808436289059516597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89752676538957526039677731 134629014808436289059516597)
        ·
          refine ⟨12621470138290902099329681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 134629014808436289059516597 12621470138290902099329681)
          ·
            refine ⟨9466102603718176574497261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12621470138290902099329681 9466102603718176574497261)
            ·
              refine ⟨3549788476394316215436473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9466102603718176574497261 3549788476394316215436473)
              ·
                refine ⟨2662341357295737161577355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3549788476394316215436473 2662341357295737161577355)
                ·
                  refine ⟨3993512035943605742366033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2662341357295737161577355 3993512035943605742366033)
                  ·
                    refine ⟨2995134026957704306774525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3993512035943605742366033 2995134026957704306774525)
                    ·
                      refine ⟨1123175260109139115040447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2995134026957704306774525 1123175260109139115040447)
                      ·
                        rfl

theorem cell23_2187376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 3].length) (baseStart_2187376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187376 prefixEnd_2187376 := by exact prefixLift 2187376
  have htrace : WordTrace (prefixWord ++ tailWord_2187376) baseStart_2187376 baseEnd_2187376 := by
    simpa [prefixWord, tailWord_2187376, baseEnd_2187376] using wordTrace_append hprefix tailTrace_2187376
  have hstable : (prefixWord ++ tailWord_2187376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187376).length < 2 ^ (prefixWord ++ tailWord_2187376).sum := by decide
  have hdescent : baseEnd_2187376 < baseStart_2187376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187389 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 3, 3, 3]
def baseStart_2187389 : Nat := 118140960795 + 2187389 * 2 ^ 59
def prefixEnd_2187389 : Nat := 4983230072969 + 3 ^ 40 * 2187389 * 2
def baseEnd_2187389 : Nat := 1123181935357647564177887

theorem tailTrace_2187389 : CollatzResearch.WordTrace tailWord_2187389 prefixEnd_2187389 1123181935357647564177887 := by
  unfold tailWord_2187389
  simp only [CollatzResearch.WordTrace]
  refine ⟨79780631072470704144381221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53187087381647136096254147 79780631072470704144381221)
  ·
    refine ⟨14958868326088257027071479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79780631072470704144381221 14958868326088257027071479)
    ·
      refine ⟨22438302489132385540607219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14958868326088257027071479 22438302489132385540607219)
      ·
        refine ⟨33657453733698578310910829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22438302489132385540607219 33657453733698578310910829)
        ·
          refine ⟨12621545150136966866591561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33657453733698578310910829 12621545150136966866591561)
          ·
            refine ⟨9466158862602725149943671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12621545150136966866591561 9466158862602725149943671)
            ·
              refine ⟨14199238293904087724915507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9466158862602725149943671 14199238293904087724915507)
              ·
                refine ⟨21298857440856131587373261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14199238293904087724915507 21298857440856131587373261)
                ·
                  refine ⟨7987071540321049345264973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21298857440856131587373261 7987071540321049345264973)
                  ·
                    refine ⟨2995151827620393504474365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7987071540321049345264973 2995151827620393504474365)
                    ·
                      refine ⟨1123181935357647564177887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2995151827620393504474365 1123181935357647564177887)
                      ·
                        rfl

theorem cell23_2187389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_2187389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187389 prefixEnd_2187389 := by exact prefixLift 2187389
  have htrace : WordTrace (prefixWord ++ tailWord_2187389) baseStart_2187389 baseEnd_2187389 := by
    simpa [prefixWord, tailWord_2187389, baseEnd_2187389] using wordTrace_append hprefix tailTrace_2187389
  have hstable : (prefixWord ++ tailWord_2187389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187389).length < 2 ^ (prefixWord ++ tailWord_2187389).sum := by decide
  have hdescent : baseEnd_2187389 < baseStart_2187389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187393 : List Nat := [1, 2, 4, 2, 4, 1, 1, 1, 1, 1, 5]
def baseStart_2187393 : Nat := 118140960795 + 2187393 * 2 ^ 59
def prefixEnd_2187393 : Nat := 4983230072969 + 3 ^ 40 * 2187393 * 2
def baseEnd_2187393 : Nat := 1123183989280265548527869

theorem tailTrace_2187393 : CollatzResearch.WordTrace tailWord_2187393 prefixEnd_2187393 1123183989280265548527869 := by
  unfold tailWord_2187393
  simp only [CollatzResearch.WordTrace]
  refine ⟨79780776964456212827526833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53187184642970808551684555 79780776964456212827526833)
  ·
    refine ⟨59835582723342159620645125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79780776964456212827526833 59835582723342159620645125)
    ·
      refine ⟨11219171760626654928870961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59835582723342159620645125 11219171760626654928870961)
      ·
        refine ⟨8414378820469991196653221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11219171760626654928870961 8414378820469991196653221)
        ·
          refine ⟨1577696028838123349372479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8414378820469991196653221 1577696028838123349372479)
          ·
            refine ⟨2366544043257185024058719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1577696028838123349372479 2366544043257185024058719)
            ·
              refine ⟨3549816064885777536088079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2366544043257185024058719 3549816064885777536088079)
              ·
                refine ⟨5324724097328666304132119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3549816064885777536088079 5324724097328666304132119)
                ·
                  refine ⟨7987086145992999456198179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5324724097328666304132119 7987086145992999456198179)
                  ·
                    refine ⟨11980629218989499184297269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7987086145992999456198179 11980629218989499184297269)
                    ·
                      refine ⟨1123183989280265548527869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11980629218989499184297269 1123183989280265548527869)
                      ·
                        rfl

theorem cell23_2187393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_2187393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187393 prefixEnd_2187393 := by exact prefixLift 2187393
  have htrace : WordTrace (prefixWord ++ tailWord_2187393) baseStart_2187393 baseEnd_2187393 := by
    simpa [prefixWord, tailWord_2187393, baseEnd_2187393] using wordTrace_append hprefix tailTrace_2187393
  have hstable : (prefixWord ++ tailWord_2187393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187393).length < 2 ^ (prefixWord ++ tailWord_2187393).sum := by decide
  have hdescent : baseEnd_2187393 < baseStart_2187393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187423 : List Nat := [1, 1, 2, 6, 1, 1, 2, 3, 2, 1, 3]
def baseStart_2187423 : Nat := 118140960795 + 2187423 * 2 ^ 59
def prefixEnd_2187423 : Nat := 4983230072969 + 3 ^ 40 * 2187423 * 2
def baseEnd_2187423 : Nat := 1123199393699900431152731

theorem tailTrace_2187423 : CollatzResearch.WordTrace tailWord_2187423 prefixEnd_2187423 1123199393699900431152731 := by
  unfold tailWord_2187423
  simp only [CollatzResearch.WordTrace]
  refine ⟨79781871154347527951118923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53187914102898351967412615 79781871154347527951118923)
  ·
    refine ⟨119672806731521291926678385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79781871154347527951118923 119672806731521291926678385)
    ·
      refine ⟨89754605048640968945008789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119672806731521291926678385 89754605048640968945008789)
      ·
        refine ⟨4207247111655045419297287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 89754605048640968945008789 4207247111655045419297287)
        ·
          refine ⟨6310870667482568128945931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4207247111655045419297287 6310870667482568128945931)
          ·
            refine ⟨9466306001223852193418897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6310870667482568128945931 9466306001223852193418897)
            ·
              refine ⟨7099729500917889145064173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9466306001223852193418897 7099729500917889145064173)
              ·
                refine ⟨2662398562844208429399065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7099729500917889145064173 2662398562844208429399065)
                ·
                  refine ⟨1996798922133156322049299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2662398562844208429399065 1996798922133156322049299)
                  ·
                    refine ⟨2995198383199734483073949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1996798922133156322049299 2995198383199734483073949)
                    ·
                      refine ⟨1123199393699900431152731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2995198383199734483073949 1123199393699900431152731)
                      ·
                        rfl

theorem cell23_2187423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_2187423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187423 prefixEnd_2187423 := by exact prefixLift 2187423
  have htrace : WordTrace (prefixWord ++ tailWord_2187423) baseStart_2187423 baseEnd_2187423 := by
    simpa [prefixWord, tailWord_2187423, baseEnd_2187423] using wordTrace_append hprefix tailTrace_2187423
  have hstable : (prefixWord ++ tailWord_2187423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187423).length < 2 ^ (prefixWord ++ tailWord_2187423).sum := by decide
  have hdescent : baseEnd_2187423 < baseStart_2187423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187457 : List Nat := [1, 2, 6, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_2187457 : Nat := 118140960795 + 2187457 * 2 ^ 59
def prefixEnd_2187457 : Nat := 4983230072969 + 3 ^ 40 * 2187457 * 2
def baseEnd_2187457 : Nat := 1123216852042153298127575

theorem tailTrace_2187457 : CollatzResearch.WordTrace tailWord_2187457 prefixEnd_2187457 1123216852042153298127575 := by
  unfold tailWord_2187457
  simp only [CollatzResearch.WordTrace]
  refine ⟨79783111236224351757856625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53188740824149567838571083 79783111236224351757856625)
  ·
    refine ⟨59837333427168263818392469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79783111236224351757856625 59837333427168263818392469)
    ·
      refine ⟨2804875004398512366487147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 59837333427168263818392469 2804875004398512366487147)
      ·
        refine ⟨4207312506597768549730721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2804875004398512366487147 4207312506597768549730721)
        ·
          refine ⟨3155484379948326412298041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4207312506597768549730721 3155484379948326412298041)
          ·
            refine ⟨2366613284961244809223531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3155484379948326412298041 2366613284961244809223531)
            ·
              refine ⟨3549919927441867213835297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2366613284961244809223531 3549919927441867213835297)
              ·
                refine ⟨2662439945581400410376473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3549919927441867213835297 2662439945581400410376473)
                ·
                  refine ⟨1996829959186050307782355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2662439945581400410376473 1996829959186050307782355)
                  ·
                    refine ⟨2995244938779075461673533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1996829959186050307782355 2995244938779075461673533)
                    ·
                      refine ⟨1123216852042153298127575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2995244938779075461673533 1123216852042153298127575)
                      ·
                        rfl

theorem cell23_2187457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_2187457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187457 prefixEnd_2187457 := by exact prefixLift 2187457
  have htrace : WordTrace (prefixWord ++ tailWord_2187457) baseStart_2187457 baseEnd_2187457 := by
    simpa [prefixWord, tailWord_2187457, baseEnd_2187457] using wordTrace_append hprefix tailTrace_2187457
  have hstable : (prefixWord ++ tailWord_2187457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187457).length < 2 ^ (prefixWord ++ tailWord_2187457).sum := by decide
  have hdescent : baseEnd_2187457 < baseStart_2187457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187499 : List Nat := [1, 1, 1, 1, 2, 5, 2, 3, 2, 5]
def baseStart_2187499 : Nat := 118140960795 + 2187499 * 2 ^ 59
def prefixEnd_2187499 : Nat := 4983230072969 + 3 ^ 40 * 2187499 * 2
def baseEnd_2187499 : Nat := 374412806076547377934127

theorem tailTrace_2187499 : CollatzResearch.WordTrace tailWord_2187499 prefixEnd_2187499 374412806076547377934127 := by
  unfold tailWord_2187499
  simp only [CollatzResearch.WordTrace]
  refine ⟨79784643102072192930885551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53189762068048128620590367 79784643102072192930885551)
  ·
    refine ⟨119676964653108289396328327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79784643102072192930885551 119676964653108289396328327)
    ·
      refine ⟨179515446979662434094492491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119676964653108289396328327 179515446979662434094492491)
      ·
        refine ⟨269273170469493651141738737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179515446979662434094492491 269273170469493651141738737)
        ·
          refine ⟨201954877852120238356304053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269273170469493651141738737 201954877852120238356304053)
          ·
            refine ⟨18933269798636272345903505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 201954877852120238356304053 18933269798636272345903505)
            ·
              refine ⟨14199952348977204259427629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18933269798636272345903505 14199952348977204259427629)
              ·
                refine ⟨5324982130866451597285361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14199952348977204259427629 5324982130866451597285361)
                ·
                  refine ⟨3993736598149838697964021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5324982130866451597285361 3993736598149838697964021)
                  ·
                    refine ⟨374412806076547377934127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3993736598149838697964021 374412806076547377934127)
                    ·
                      rfl

theorem cell23_2187499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 5].length) (baseStart_2187499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187499 prefixEnd_2187499 := by exact prefixLift 2187499
  have htrace : WordTrace (prefixWord ++ tailWord_2187499) baseStart_2187499 baseEnd_2187499 := by
    simpa [prefixWord, tailWord_2187499, baseEnd_2187499] using wordTrace_append hprefix tailTrace_2187499
  have hstable : (prefixWord ++ tailWord_2187499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187499).length < 2 ^ (prefixWord ++ tailWord_2187499).sum := by decide
  have hdescent : baseEnd_2187499 < baseStart_2187499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187503 : List Nat := [1, 1, 2, 1, 6, 3, 1, 3, 5]
def baseStart_2187503 : Nat := 118140960795 + 2187503 * 2 ^ 59
def prefixEnd_2187503 : Nat := 4983230072969 + 3 ^ 40 * 2187503 * 2
def baseEnd_2187503 : Nat := 124804496905806679794707

theorem tailTrace_2187503 : CollatzResearch.WordTrace tailWord_2187503 prefixEnd_2187503 124804496905806679794707 := by
  unfold tailWord_2187503
  simp only [CollatzResearch.WordTrace]
  refine ⟨79784788994057701614031163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53189859329371801076020775 79784788994057701614031163)
  ·
    refine ⟨119677183491086552421046745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79784788994057701614031163 119677183491086552421046745)
    ·
      refine ⟨89757887618314914315785059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119677183491086552421046745 89757887618314914315785059)
      ·
        refine ⟨134636831427472371473677589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89757887618314914315785059 134636831427472371473677589)
        ·
          refine ⟨6311101473162767412828637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 134636831427472371473677589 6311101473162767412828637)
          ·
            refine ⟨2366663052436037779810739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6311101473162767412828637 2366663052436037779810739)
            ·
              refine ⟨3549994578654056669716109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2366663052436037779810739 3549994578654056669716109)
              ·
                refine ⟨1331247966995271251143541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3549994578654056669716109 1331247966995271251143541)
                ·
                  refine ⟨124804496905806679794707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1331247966995271251143541 124804496905806679794707)
                  ·
                    rfl

theorem cell23_2187503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 3, 5].length) (baseStart_2187503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187503 prefixEnd_2187503 := by exact prefixLift 2187503
  have htrace : WordTrace (prefixWord ++ tailWord_2187503) baseStart_2187503 baseEnd_2187503 := by
    simpa [prefixWord, tailWord_2187503, baseEnd_2187503] using wordTrace_append hprefix tailTrace_2187503
  have hstable : (prefixWord ++ tailWord_2187503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187503).length < 2 ^ (prefixWord ++ tailWord_2187503).sum := by decide
  have hdescent : baseEnd_2187503 < baseStart_2187503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2187516 : List Nat := [2, 2, 2, 1, 4, 2, 1, 2, 2, 5]
def baseStart_2187516 : Nat := 118140960795 + 2187516 * 2 ^ 59
def prefixEnd_2187516 : Nat := 4983230072969 + 3 ^ 40 * 2187516 * 2
def baseEnd_2187516 : Nat := 374415715800256189096601

theorem tailTrace_2187516 : CollatzResearch.WordTrace tailWord_2187516 prefixEnd_2187516 374415715800256189096601 := by
  unfold tailWord_2187516
  simp only [CollatzResearch.WordTrace]
  refine ⟨39892631571505302417127201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53190175428673736556169601 39892631571505302417127201)
  ·
    refine ⟨29919473678628976812845401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39892631571505302417127201 29919473678628976812845401)
    ·
      refine ⟨22439605258971732609634051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29919473678628976812845401 22439605258971732609634051)
      ·
        refine ⟨33659407888457598914451077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22439605258971732609634051 33659407888457598914451077)
        ·
          refine ⟨6311138979085799796459577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33659407888457598914451077 6311138979085799796459577)
          ·
            refine ⟨4733354234314349847344683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6311138979085799796459577 4733354234314349847344683)
            ·
              refine ⟨7100031351471524771017025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4733354234314349847344683 7100031351471524771017025)
              ·
                refine ⟨5325023513603643578262769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7100031351471524771017025 5325023513603643578262769)
                ·
                  refine ⟨3993767635202732683697077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5325023513603643578262769 3993767635202732683697077)
                  ·
                    refine ⟨374415715800256189096601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3993767635202732683697077 374415715800256189096601)
                    ·
                      rfl

theorem cell23_2187516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_2187516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2187516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2187516 prefixEnd_2187516 := by exact prefixLift 2187516
  have htrace : WordTrace (prefixWord ++ tailWord_2187516) baseStart_2187516 baseEnd_2187516 := by
    simpa [prefixWord, tailWord_2187516, baseEnd_2187516] using wordTrace_append hprefix tailTrace_2187516
  have hstable : (prefixWord ++ tailWord_2187516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2187516).length < 2 ^ (prefixWord ++ tailWord_2187516).sum := by decide
  have hdescent : baseEnd_2187516 < baseStart_2187516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2187516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
