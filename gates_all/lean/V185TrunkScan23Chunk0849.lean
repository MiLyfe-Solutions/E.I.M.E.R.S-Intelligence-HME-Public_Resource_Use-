import V185TrunkScan23Chunk0848

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5024738 : List Nat := [3, 3, 3, 1, 1, 1, 1, 5, 1, 4]
def baseStart_5024738 : Nat := 118140960795 + 5024738 * 2 ^ 59
def prefixEnd_5024738 : Nat := 4983230072969 + 3 ^ 40 * 5024738 * 2
def baseEnd_5024738 : Nat := 860035252303822307722219

theorem tailTrace_5024738 : CollatzResearch.WordTrace tailWord_5024738 prefixEnd_5024738 860035252303822307722219 := by
  unfold tailWord_5024738
  simp only [CollatzResearch.WordTrace]
  refine ⟨45816812717559964443536717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122178167246826571849431245 45816812717559964443536717)
  ·
    refine ⟨17181304769084986666326269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45816812717559964443536717 17181304769084986666326269)
    ·
      refine ⟨6442989288406869999872351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17181304769084986666326269 6442989288406869999872351)
      ·
        refine ⟨9664483932610304999808527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6442989288406869999872351 9664483932610304999808527)
        ·
          refine ⟨14496725898915457499712791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9664483932610304999808527 14496725898915457499712791)
          ·
            refine ⟨21745088848373186249569187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14496725898915457499712791 21745088848373186249569187)
            ·
              refine ⟨32617633272559779374353781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21745088848373186249569187 32617633272559779374353781)
              ·
                refine ⟨3057903119302479316345667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32617633272559779374353781 3057903119302479316345667)
                ·
                  refine ⟨4586854678953718974518501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3057903119302479316345667 4586854678953718974518501)
                  ·
                    refine ⟨860035252303822307722219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4586854678953718974518501 860035252303822307722219)
                    ·
                      rfl

theorem cell23_5024738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_5024738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024738 prefixEnd_5024738 := by exact prefixLift 5024738
  have htrace : WordTrace (prefixWord ++ tailWord_5024738) baseStart_5024738 baseEnd_5024738 := by
    simpa [prefixWord, tailWord_5024738, baseEnd_5024738] using wordTrace_append hprefix tailTrace_5024738
  have hstable : (prefixWord ++ tailWord_5024738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024738).length < 2 ^ (prefixWord ++ tailWord_5024738).sum := by decide
  have hdescent : baseEnd_5024738 < baseStart_5024738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024761 : List Nat := [1, 2, 1, 3, 1, 3, 1, 6, 1, 1, 3]
def baseStart_5024761 : Nat := 118140960795 + 5024761 * 2 ^ 59
def prefixEnd_5024761 : Nat := 4983230072969 + 3 ^ 40 * 5024761 * 2
def baseEnd_5024761 : Nat := 2580117566966520333179051

theorem tailTrace_5024761 : CollatzResearch.WordTrace tailWord_5024761 prefixEnd_5024761 2580117566966520333179051 := by
  unfold tailWord_5024761
  simp only [CollatzResearch.WordTrace]
  refine ⟨183268089749156532702234137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122178726499437688468156091 183268089749156532702234137)
  ·
    refine ⟨137451067311867399526675603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183268089749156532702234137 137451067311867399526675603)
    ·
      refine ⟨206176600967801099290013405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137451067311867399526675603 206176600967801099290013405)
      ·
        refine ⟨77316225362925412233755027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206176600967801099290013405 77316225362925412233755027)
        ·
          refine ⟨115974338044388118350632541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77316225362925412233755027 115974338044388118350632541)
          ·
            refine ⟨43490376766645544381487203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115974338044388118350632541 43490376766645544381487203)
            ·
              refine ⟨65235565149968316572230805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43490376766645544381487203 65235565149968316572230805)
              ·
                refine ⟨3057917116404764839323319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65235565149968316572230805 3057917116404764839323319)
                ·
                  refine ⟨4586875674607147258984979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3057917116404764839323319 4586875674607147258984979)
                  ·
                    refine ⟨6880313511910720888477469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4586875674607147258984979 6880313511910720888477469)
                    ·
                      refine ⟨2580117566966520333179051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6880313511910720888477469 2580117566966520333179051)
                      ·
                        rfl

theorem cell23_5024761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 6, 1, 1, 3].length) (baseStart_5024761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024761 prefixEnd_5024761 := by exact prefixLift 5024761
  have htrace : WordTrace (prefixWord ++ tailWord_5024761) baseStart_5024761 baseEnd_5024761 := by
    simpa [prefixWord, tailWord_5024761, baseEnd_5024761] using wordTrace_append hprefix tailTrace_5024761
  have hstable : (prefixWord ++ tailWord_5024761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024761).length < 2 ^ (prefixWord ++ tailWord_5024761).sum := by decide
  have hdescent : baseEnd_5024761 < baseStart_5024761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024804 : List Nat := [2, 3, 1, 4, 1, 1, 1, 3, 1, 1, 5]
def baseStart_5024804 : Nat := 118140960795 + 5024804 * 2 ^ 59
def prefixEnd_5024804 : Nat := 4983230072969 + 3 ^ 40 * 5024804 * 2
def baseEnd_5024804 : Nat := 2580139646634663664941353

theorem tailTrace_5024804 : CollatzResearch.WordTrace tailWord_5024804 prefixEnd_5024804 2580139646634663664941353 := by
  unfold tailWord_5024804
  simp only [CollatzResearch.WordTrace]
  refine ⟨91634829044000375523024733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122179772058667167364032977 91634829044000375523024733)
  ·
    refine ⟨34363060891500140821134275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91634829044000375523024733 34363060891500140821134275)
    ·
      refine ⟨51544591337250211231701413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34363060891500140821134275 51544591337250211231701413)
      ·
        refine ⟨9664610875734414605944015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51544591337250211231701413 9664610875734414605944015)
        ·
          refine ⟨14496916313601621908916023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9664610875734414605944015 14496916313601621908916023)
          ·
            refine ⟨21745374470402432863374035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14496916313601621908916023 21745374470402432863374035)
            ·
              refine ⟨32618061705603649295061053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21745374470402432863374035 32618061705603649295061053)
              ·
                refine ⟨12231773139601368485647895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32618061705603649295061053 12231773139601368485647895)
                ·
                  refine ⟨18347659709402052728471843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12231773139601368485647895 18347659709402052728471843)
                  ·
                    refine ⟨27521489564103079092707765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18347659709402052728471843 27521489564103079092707765)
                    ·
                      refine ⟨2580139646634663664941353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27521489564103079092707765 2580139646634663664941353)
                      ·
                        rfl

theorem cell23_5024804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_5024804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024804 prefixEnd_5024804 := by exact prefixLift 5024804
  have htrace : WordTrace (prefixWord ++ tailWord_5024804) baseStart_5024804 baseEnd_5024804 := by
    simpa [prefixWord, tailWord_5024804, baseEnd_5024804] using wordTrace_append hprefix tailTrace_5024804
  have hstable : (prefixWord ++ tailWord_5024804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024804).length < 2 ^ (prefixWord ++ tailWord_5024804).sum := by decide
  have hdescent : baseEnd_5024804 < baseStart_5024804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024828 : List Nat := [2, 2, 2, 2, 2, 4, 2, 1, 2, 4]
def baseStart_5024828 : Nat := 118140960795 + 5024828 * 2 ^ 59
def prefixEnd_5024828 : Nat := 4983230072969 + 3 ^ 40 * 5024828 * 2
def baseEnd_5024828 : Nat := 860050656723457190347081

theorem tailTrace_5024828 : CollatzResearch.WordTrace tailWord_5024828 prefixEnd_5024828 860050656723457190347081 := by
  unfold tailWord_5024828
  simp only [CollatzResearch.WordTrace]
  refine ⟨91635266719956901572461569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122180355626609202096615425 91635266719956901572461569)
  ·
    refine ⟨68726450039967676179346177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91635266719956901572461569 68726450039967676179346177)
    ·
      refine ⟨51544837529975757134509633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68726450039967676179346177 51544837529975757134509633)
      ·
        refine ⟨38658628147481817850882225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51544837529975757134509633 38658628147481817850882225)
        ·
          refine ⟨28993971110611363388161669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38658628147481817850882225 28993971110611363388161669)
          ·
            refine ⟨5436369583239630635280313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28993971110611363388161669 5436369583239630635280313)
            ·
              refine ⟨4077277187429722976460235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5436369583239630635280313 4077277187429722976460235)
              ·
                refine ⟨6115915781144584464690353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4077277187429722976460235 6115915781144584464690353)
                ·
                  refine ⟨4586936835858438348517765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6115915781144584464690353 4586936835858438348517765)
                  ·
                    refine ⟨860050656723457190347081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4586936835858438348517765 860050656723457190347081)
                    ·
                      rfl

theorem cell23_5024828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_5024828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024828 prefixEnd_5024828 := by exact prefixLift 5024828
  have htrace : WordTrace (prefixWord ++ tailWord_5024828) baseStart_5024828 baseEnd_5024828 := by
    simpa [prefixWord, tailWord_5024828, baseEnd_5024828] using wordTrace_append hprefix tailTrace_5024828
  have hstable : (prefixWord ++ tailWord_5024828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024828).length < 2 ^ (prefixWord ++ tailWord_5024828).sum := by decide
  have hdescent : baseEnd_5024828 < baseStart_5024828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024838 : List Nat := [6, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3]
def baseStart_5024838 : Nat := 118140960795 + 5024838 * 2 ^ 59
def prefixEnd_5024838 : Nat := 4983230072969 + 3 ^ 40 * 5024838 * 2
def baseEnd_5024838 : Nat := 2580157104976916531916197

theorem tailTrace_5024838 : CollatzResearch.WordTrace tailWord_5024838 prefixEnd_5024838 2580157104976916531916197 := by
  unfold tailWord_5024838
  simp only [CollatzResearch.WordTrace]
  refine ⟨5727215567808674214149599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 122180598779918383235191445 5727215567808674214149599)
  ·
    refine ⟨8590823351713011321224399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5727215567808674214149599 8590823351713011321224399)
    ·
      refine ⟨12886235027569516981836599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8590823351713011321224399 12886235027569516981836599)
      ·
        refine ⟨19329352541354275472754899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12886235027569516981836599 19329352541354275472754899)
        ·
          refine ⟨28994028812031413209132349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19329352541354275472754899 28994028812031413209132349)
          ·
            refine ⟨10872760804511779953424631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28994028812031413209132349 10872760804511779953424631)
            ·
              refine ⟨16309141206767669930136947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10872760804511779953424631 16309141206767669930136947)
              ·
                refine ⟨24463711810151504895205421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16309141206767669930136947 24463711810151504895205421)
                ·
                  refine ⟨9173891928806814335702033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24463711810151504895205421 9173891928806814335702033)
                  ·
                    refine ⟨6880418946605110751776525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9173891928806814335702033 6880418946605110751776525)
                    ·
                      refine ⟨2580157104976916531916197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6880418946605110751776525 2580157104976916531916197)
                      ·
                        rfl

theorem cell23_5024838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_5024838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024838 prefixEnd_5024838 := by exact prefixLift 5024838
  have htrace : WordTrace (prefixWord ++ tailWord_5024838) baseStart_5024838 baseEnd_5024838 := by
    simpa [prefixWord, tailWord_5024838, baseEnd_5024838] using wordTrace_append hprefix tailTrace_5024838
  have hstable : (prefixWord ++ tailWord_5024838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024838).length < 2 ^ (prefixWord ++ tailWord_5024838).sum := by decide
  have hdescent : baseEnd_5024838 < baseStart_5024838 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024867 : List Nat := [1, 1, 1, 5, 1, 1, 1, 4, 2, 6]
def baseStart_5024867 : Nat := 118140960795 + 5024867 * 2 ^ 59
def prefixEnd_5024867 : Nat := 4983230072969 + 3 ^ 40 * 5024867 * 2
def baseEnd_5024867 : Nat := 860057331971965639484521

theorem tailTrace_5024867 : CollatzResearch.WordTrace tailWord_5024867 prefixEnd_5024867 860057331971965639484521 := by
  unfold tailWord_5024867
  simp only [CollatzResearch.WordTrace]
  refine ⟨183271955886772512805592855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122181303924515008537061903 183271955886772512805592855)
  ·
    refine ⟨274907933830158769208389283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183271955886772512805592855 274907933830158769208389283)
    ·
      refine ⟨412361900745238153812583925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274907933830158769208389283 412361900745238153812583925)
      ·
        refine ⟨38658928194866076919929743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 412361900745238153812583925 38658928194866076919929743)
        ·
          refine ⟨57988392292299115379894615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38658928194866076919929743 57988392292299115379894615)
          ·
            refine ⟨86982588438448673069841923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57988392292299115379894615 86982588438448673069841923)
            ·
              refine ⟨130473882657673009604762885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86982588438448673069841923 130473882657673009604762885)
              ·
                refine ⟨24463852998313689300893041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130473882657673009604762885 24463852998313689300893041)
                ·
                  refine ⟨18347889748735266975669781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24463852998313689300893041 18347889748735266975669781)
                  ·
                    refine ⟨860057331971965639484521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18347889748735266975669781 860057331971965639484521)
                    ·
                      rfl

theorem cell23_5024867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 6].length) (baseStart_5024867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024867 prefixEnd_5024867 := by exact prefixLift 5024867
  have htrace : WordTrace (prefixWord ++ tailWord_5024867) baseStart_5024867 baseEnd_5024867 := by
    simpa [prefixWord, tailWord_5024867, baseEnd_5024867] using wordTrace_append hprefix tailTrace_5024867
  have hstable : (prefixWord ++ tailWord_5024867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024867).length < 2 ^ (prefixWord ++ tailWord_5024867).sum := by decide
  have hdescent : baseEnd_5024867 < baseStart_5024867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024874 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 2, 3, 4]
def baseStart_5024874 : Nat := 118140960795 + 5024874 * 2 ^ 59
def prefixEnd_5024874 : Nat := 4983230072969 + 3 ^ 40 * 5024874 * 2
def baseEnd_5024874 : Nat := 2580175590280478391066031

theorem tailTrace_5024874 : CollatzResearch.WordTrace tailWord_5024874 prefixEnd_5024874 2580175590280478391066031 := by
  unfold tailWord_5024874
  simp only [CollatzResearch.WordTrace]
  refine ⟨45818052799436788250274419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122181474131831435334065117 45818052799436788250274419)
  ·
    refine ⟨68727079199155182375411629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45818052799436788250274419 68727079199155182375411629)
    ·
      refine ⟨25772654699683193390779361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68727079199155182375411629 25772654699683193390779361)
      ·
        refine ⟨19329491024762395043084521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25772654699683193390779361 19329491024762395043084521)
        ·
          refine ⟨14497118268571796282313391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19329491024762395043084521 14497118268571796282313391)
          ·
            refine ⟨21745677402857694423470087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14497118268571796282313391 21745677402857694423470087)
            ·
              refine ⟨32618516104286541635205131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21745677402857694423470087 32618516104286541635205131)
              ·
                refine ⟨48927774156429812452807697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32618516104286541635205131 48927774156429812452807697)
                ·
                  refine ⟨36695830617322359339605773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48927774156429812452807697 36695830617322359339605773)
                  ·
                    refine ⟨13760936481495884752352165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36695830617322359339605773 13760936481495884752352165)
                    ·
                      refine ⟨2580175590280478391066031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13760936481495884752352165 2580175590280478391066031)
                      ·
                        rfl

theorem cell23_5024874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_5024874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024874 prefixEnd_5024874 := by exact prefixLift 5024874
  have htrace : WordTrace (prefixWord ++ tailWord_5024874) baseStart_5024874 baseEnd_5024874 := by
    simpa [prefixWord, tailWord_5024874, baseEnd_5024874] using wordTrace_append hprefix tailTrace_5024874
  have hstable : (prefixWord ++ tailWord_5024874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024874).length < 2 ^ (prefixWord ++ tailWord_5024874).sum := by decide
  have hdescent : baseEnd_5024874 < baseStart_5024874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024961 : List Nat := [1, 2, 6, 1, 1, 1, 2, 1, 1, 7]
def baseStart_5024961 : Nat := 118140960795 + 5024961 * 2 ^ 59
def prefixEnd_5024961 : Nat := 4983230072969 + 3 ^ 40 * 5024961 * 2
def baseEnd_5024961 : Nat := 860073421032473183559377

theorem tailTrace_5024961 : CollatzResearch.WordTrace tailWord_5024961 prefixEnd_5024961 860073421032473183559377 := by
  unfold tailWord_5024961
  simp only [CollatzResearch.WordTrace]
  refine ⟨183275384348431966859514737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122183589565621311239676491 183275384348431966859514737)
  ·
    refine ⟨137456538261323975144636053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183275384348431966859514737 137456538261323975144636053)
    ·
      refine ⟨6443275230999561334904815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 137456538261323975144636053 6443275230999561334904815)
      ·
        refine ⟨9664912846499342002357223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6443275230999561334904815 9664912846499342002357223)
        ·
          refine ⟨14497369269749013003535835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9664912846499342002357223 14497369269749013003535835)
          ·
            refine ⟨21746053904623519505303753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14497369269749013003535835 21746053904623519505303753)
            ·
              refine ⟨16309540428467639628977815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21746053904623519505303753 16309540428467639628977815)
              ·
                refine ⟨24464310642701459443466723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16309540428467639628977815 24464310642701459443466723)
                ·
                  refine ⟨36696465964052189165200085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24464310642701459443466723 36696465964052189165200085)
                  ·
                    refine ⟨860073421032473183559377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36696465964052189165200085 860073421032473183559377)
                    ·
                      rfl

theorem cell23_5024961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_5024961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024961 prefixEnd_5024961 := by exact prefixLift 5024961
  have htrace : WordTrace (prefixWord ++ tailWord_5024961) baseStart_5024961 baseEnd_5024961 := by
    simpa [prefixWord, tailWord_5024961, baseEnd_5024961] using wordTrace_append hprefix tailTrace_5024961
  have hstable : (prefixWord ++ tailWord_5024961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024961).length < 2 ^ (prefixWord ++ tailWord_5024961).sum := by decide
  have hdescent : baseEnd_5024961 < baseStart_5024961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024981 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 4, 1, 4]
def baseStart_5024981 : Nat := 118140960795 + 5024981 * 2 ^ 59
def prefixEnd_5024981 : Nat := 4983230072969 + 3 ^ 40 * 5024981 * 2
def baseEnd_5024981 : Nat := 2580230532710509472428039

theorem tailTrace_5024981 : CollatzResearch.WordTrace tailWord_5024981 prefixEnd_5024981 2580230532710509472428039 := by
  unfold tailWord_5024981
  simp only [CollatzResearch.WordTrace]
  refine ⟨183276113808359510275242797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122184075872239673516828531 183276113808359510275242797)
  ·
    refine ⟨68728542678134816353216049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183276113808359510275242797 68728542678134816353216049)
    ·
      refine ⟨51546407008601112264912037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68728542678134816353216049 51546407008601112264912037)
      ·
        refine ⟨9664951314112708549671007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51546407008601112264912037 9664951314112708549671007)
        ·
          refine ⟨14497426971169062824506511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9664951314112708549671007 14497426971169062824506511)
          ·
            refine ⟨21746140456753594236759767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14497426971169062824506511 21746140456753594236759767)
            ·
              refine ⟨32619210685130391355139651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21746140456753594236759767 32619210685130391355139651)
              ·
                refine ⟨48928816027695587032709477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32619210685130391355139651 48928816027695587032709477)
                ·
                  refine ⟨9174153005192922568633027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48928816027695587032709477 9174153005192922568633027)
                  ·
                    refine ⟨13761229507789383852949541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9174153005192922568633027 13761229507789383852949541)
                    ·
                      refine ⟨2580230532710509472428039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13761229507789383852949541 2580230532710509472428039)
                      ·
                        rfl

theorem cell23_5024981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_5024981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024981 prefixEnd_5024981 := by exact prefixLift 5024981
  have htrace : WordTrace (prefixWord ++ tailWord_5024981) baseStart_5024981 baseEnd_5024981 := by
    simpa [prefixWord, tailWord_5024981, baseEnd_5024981] using wordTrace_append hprefix tailTrace_5024981
  have hstable : (prefixWord ++ tailWord_5024981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024981).length < 2 ^ (prefixWord ++ tailWord_5024981).sum := by decide
  have hdescent : baseEnd_5024981 < baseStart_5024981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024982 : List Nat := [5, 2, 1, 2, 2, 1, 3, 2, 5]
def baseStart_5024982 : Nat := 118140960795 + 5024982 * 2 ^ 59
def prefixEnd_5024982 : Nat := 4983230072969 + 3 ^ 40 * 5024982 * 2
def baseEnd_5024982 : Nat := 286692338465684885390615

theorem tailTrace_5024982 : CollatzResearch.WordTrace tailWord_5024982 prefixEnd_5024982 286692338465684885390615 := by
  unfold tailWord_5024982
  simp only [CollatzResearch.WordTrace]
  refine ⟨11454759392584742965376825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122184100187570591630686133 11454759392584742965376825)
  ·
    refine ⟨8591069544438557224032619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11454759392584742965376825 8591069544438557224032619)
    ·
      refine ⟨12886604316657835836048929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8591069544438557224032619 12886604316657835836048929)
      ·
        refine ⟨9664953237493376877036697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12886604316657835836048929 9664953237493376877036697)
        ·
          refine ⟨7248714928120032657777523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9664953237493376877036697 7248714928120032657777523)
          ·
            refine ⟨10873072392180048986666285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7248714928120032657777523 10873072392180048986666285)
            ·
              refine ⟨4077402147067518369999857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10873072392180048986666285 4077402147067518369999857)
              ·
                refine ⟨3058051610300638777499893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4077402147067518369999857 3058051610300638777499893)
                ·
                  refine ⟨286692338465684885390615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3058051610300638777499893 286692338465684885390615)
                  ·
                    rfl

theorem cell23_5024982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_5024982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024982 prefixEnd_5024982 := by exact prefixLift 5024982
  have htrace : WordTrace (prefixWord ++ tailWord_5024982) baseStart_5024982 baseEnd_5024982 := by
    simpa [prefixWord, tailWord_5024982, baseEnd_5024982] using wordTrace_append hprefix tailTrace_5024982
  have hstable : (prefixWord ++ tailWord_5024982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024982).length < 2 ^ (prefixWord ++ tailWord_5024982).sum := by decide
  have hdescent : baseEnd_5024982 < baseStart_5024982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024987 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 12]
def baseStart_5024987 : Nat := 118140960795 + 5024987 * 2 ^ 59
def prefixEnd_5024987 : Nat := 4983230072969 + 3 ^ 40 * 5024987 * 2
def baseEnd_5024987 : Nat := 286692623732715160994779

theorem tailTrace_5024987 : CollatzResearch.WordTrace tailWord_5024987 prefixEnd_5024987 286692623732715160994779 := by
  unfold tailWord_5024987
  simp only [CollatzResearch.WordTrace]
  refine ⟨183276332646337773299961215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122184221764225182199974143 183276332646337773299961215)
  ·
    refine ⟨274914498969506659949941823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183276332646337773299961215 274914498969506659949941823)
    ·
      refine ⟨412371748454259989924912735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274914498969506659949941823 412371748454259989924912735)
      ·
        refine ⟨618557622681389984887369103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412371748454259989924912735 618557622681389984887369103)
        ·
          refine ⟨927836434022084977331053655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 618557622681389984887369103 927836434022084977331053655)
          ·
            refine ⟨1391754651033127465996580483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 927836434022084977331053655 1391754651033127465996580483)
            ·
              refine ⟨2087631976549691198994870725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1391754651033127465996580483 2087631976549691198994870725)
              ·
                refine ⟨391430995603067099811538261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2087631976549691198994870725 391430995603067099811538261)
                ·
                  refine ⟨286692623732715160994779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 391430995603067099811538261 286692623732715160994779)
                  ·
                    rfl

theorem cell23_5024987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 12].length) (baseStart_5024987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024987 prefixEnd_5024987 := by exact prefixLift 5024987
  have htrace : WordTrace (prefixWord ++ tailWord_5024987) baseStart_5024987 baseEnd_5024987 := by
    simpa [prefixWord, tailWord_5024987, baseEnd_5024987] using wordTrace_append hprefix tailTrace_5024987
  have hstable : (prefixWord ++ tailWord_5024987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024987).length < 2 ^ (prefixWord ++ tailWord_5024987).sum := by decide
  have hdescent : baseEnd_5024987 < baseStart_5024987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024991 : List Nat := [1, 1, 2, 3, 2, 1, 5, 1, 3, 4]
def baseStart_5024991 : Nat := 118140960795 + 5024991 * 2 ^ 59
def prefixEnd_5024991 : Nat := 4983230072969 + 3 ^ 40 * 5024991 * 2
def baseEnd_5024991 : Nat := 860078555839018144434331

theorem tailTrace_5024991 : CollatzResearch.WordTrace tailWord_5024991 prefixEnd_5024991 860078555839018144434331 := by
  unfold tailWord_5024991
  simp only [CollatzResearch.WordTrace]
  refine ⟨183276478538323281983106827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122184319025548854655404551 183276478538323281983106827)
  ·
    refine ⟨274914717807484922974660241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183276478538323281983106827 274914717807484922974660241)
    ·
      refine ⟨206186038355613692230995181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274914717807484922974660241 206186038355613692230995181)
      ·
        refine ⟨77319764383355134586623193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206186038355613692230995181 77319764383355134586623193)
        ·
          refine ⟨57989823287516350939967395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77319764383355134586623193 57989823287516350939967395)
          ·
            refine ⟨86984734931274526409951093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57989823287516350939967395 86984734931274526409951093)
            ·
              refine ⟨8154818899806986850932915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86984734931274526409951093 8154818899806986850932915)
              ·
                refine ⟨12232228349710480276399373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8154818899806986850932915 12232228349710480276399373)
                ·
                  refine ⟨4587085631141430103649765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12232228349710480276399373 4587085631141430103649765)
                  ·
                    refine ⟨860078555839018144434331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4587085631141430103649765 860078555839018144434331)
                    ·
                      rfl

theorem cell23_5024991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 3, 4].length) (baseStart_5024991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024991 prefixEnd_5024991 := by exact prefixLift 5024991
  have htrace : WordTrace (prefixWord ++ tailWord_5024991) baseStart_5024991 baseEnd_5024991 := by
    simpa [prefixWord, tailWord_5024991, baseEnd_5024991] using wordTrace_append hprefix tailTrace_5024991
  have hstable : (prefixWord ++ tailWord_5024991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024991).length < 2 ^ (prefixWord ++ tailWord_5024991).sum := by decide
  have hdescent : baseEnd_5024991 < baseStart_5024991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025012 : List Nat := [2, 6, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_5025012 : Nat := 118140960795 + 5025012 * 2 ^ 59
def prefixEnd_5025012 : Nat := 4983230072969 + 3 ^ 40 * 5025012 * 2
def baseEnd_5025012 : Nat := 860082150203599617046799

theorem tailTrace_5025012 : CollatzResearch.WordTrace tailWord_5025012 prefixEnd_5025012 860082150203599617046799 := by
  unfold tailWord_5025012
  simp only [CollatzResearch.WordTrace]
  refine ⟨91638622235623601284810645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122184829647498135046414193 91638622235623601284810645)
  ·
    refine ⟨4295560417294856310225499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 91638622235623601284810645 4295560417294856310225499)
    ·
      refine ⟨6443340625942284465338249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4295560417294856310225499 6443340625942284465338249)
      ·
        refine ⟨4832505469456713349003687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6443340625942284465338249 4832505469456713349003687)
        ·
          refine ⟨7248758204185070023505531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4832505469456713349003687 7248758204185070023505531)
          ·
            refine ⟨10873137306277605035258297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7248758204185070023505531 10873137306277605035258297)
            ·
              refine ⟨8154852979708203776443723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10873137306277605035258297 8154852979708203776443723)
              ·
                refine ⟨12232279469562305664665585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8154852979708203776443723 12232279469562305664665585)
                ·
                  refine ⟨9174209602171729248499189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12232279469562305664665585 9174209602171729248499189)
                  ·
                    refine ⟨860082150203599617046799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9174209602171729248499189 860082150203599617046799)
                    ·
                      rfl

theorem cell23_5025012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_5025012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025012 prefixEnd_5025012 := by exact prefixLift 5025012
  have htrace : WordTrace (prefixWord ++ tailWord_5025012) baseStart_5025012 baseEnd_5025012 := by
    simpa [prefixWord, tailWord_5025012, baseEnd_5025012] using wordTrace_append hprefix tailTrace_5025012
  have hstable : (prefixWord ++ tailWord_5025012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025012).length < 2 ^ (prefixWord ++ tailWord_5025012).sum := by decide
  have hdescent : baseEnd_5025012 < baseStart_5025012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025071 : List Nat := [1, 1, 2, 1, 2, 1, 3, 6, 1, 1, 4]
def baseStart_5025071 : Nat := 118140960795 + 5025071 * 2 ^ 59
def prefixEnd_5025071 : Nat := 4983230072969 + 3 ^ 40 * 5025071 * 2
def baseEnd_5025071 : Nat := 2580276745969414120302625

theorem tailTrace_5025071 : CollatzResearch.WordTrace tailWord_5025071 prefixEnd_5025071 2580276745969414120302625 := by
  unfold tailWord_5025071
  simp only [CollatzResearch.WordTrace]
  refine ⟨183279396378033455646019067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122186264252022303764012711 183279396378033455646019067)
  ·
    refine ⟨274919094567050183469028601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183279396378033455646019067 274919094567050183469028601)
    ·
      refine ⟨206189320925287637601771451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274919094567050183469028601 206189320925287637601771451)
      ·
        refine ⟨309283981387931456402657177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206189320925287637601771451 309283981387931456402657177)
        ·
          refine ⟨231962986040948592301992883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309283981387931456402657177 231962986040948592301992883)
          ·
            refine ⟨347944479061422888452989325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231962986040948592301992883 347944479061422888452989325)
            ·
              refine ⟨130479179648033583169870997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 347944479061422888452989325 130479179648033583169870997)
              ·
                refine ⟨6116211546001574211087703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 130479179648033583169870997 6116211546001574211087703)
                ·
                  refine ⟨9174317319002361316631555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6116211546001574211087703 9174317319002361316631555)
                  ·
                    refine ⟨13761475978503541974947333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9174317319002361316631555 13761475978503541974947333)
                    ·
                      refine ⟨2580276745969414120302625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13761475978503541974947333 2580276745969414120302625)
                      ·
                        rfl

theorem cell23_5025071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 1, 4].length) (baseStart_5025071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025071 prefixEnd_5025071 := by exact prefixLift 5025071
  have htrace : WordTrace (prefixWord ++ tailWord_5025071) baseStart_5025071 baseEnd_5025071 := by
    simpa [prefixWord, tailWord_5025071, baseEnd_5025071] using wordTrace_append hprefix tailTrace_5025071
  have hstable : (prefixWord ++ tailWord_5025071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025071).length < 2 ^ (prefixWord ++ tailWord_5025071).sum := by decide
  have hdescent : baseEnd_5025071 < baseStart_5025071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025075 : List Nat := [1, 1, 1, 2, 5, 4, 1, 1, 2, 3, 2]
def baseStart_5025075 : Nat := 118140960795 + 5025075 * 2 ^ 59
def prefixEnd_5025075 : Nat := 4983230072969 + 3 ^ 40 * 5025075 * 2
def baseEnd_5025075 : Nat := 2580278799892032104652607

theorem tailTrace_5025075 : CollatzResearch.WordTrace tailWord_5025075 prefixEnd_5025075 2580278799892032104652607 := by
  unfold tailWord_5025075
  simp only [CollatzResearch.WordTrace]
  refine ⟨183279542270018964329164679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122186361513345976219443119 183279542270018964329164679)
  ·
    refine ⟨274919313405028446493747019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183279542270018964329164679 274919313405028446493747019)
    ·
      refine ⟨412378970107542669740620529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274919313405028446493747019 412378970107542669740620529)
      ·
        refine ⟨309284227580657002305465397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412378970107542669740620529 309284227580657002305465397)
        ·
          refine ⟨28995396335686593966137381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 309284227580657002305465397 28995396335686593966137381)
          ·
            refine ⟨5436636812941236368650759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28995396335686593966137381 5436636812941236368650759)
            ·
              refine ⟨8154955219411854552976139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5436636812941236368650759 8154955219411854552976139)
              ·
                refine ⟨12232432829117781829464209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8154955219411854552976139 12232432829117781829464209)
                ·
                  refine ⟨9174324621838336372098157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12232432829117781829464209 9174324621838336372098157)
                  ·
                    refine ⟨3440371733189376139536809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9174324621838336372098157 3440371733189376139536809)
                    ·
                      refine ⟨2580278799892032104652607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3440371733189376139536809 2580278799892032104652607)
                      ·
                        rfl

theorem cell23_5025075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 3, 2].length) (baseStart_5025075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025075 prefixEnd_5025075 := by exact prefixLift 5025075
  have htrace : WordTrace (prefixWord ++ tailWord_5025075) baseStart_5025075 baseEnd_5025075 := by
    simpa [prefixWord, tailWord_5025075, baseEnd_5025075] using wordTrace_append hprefix tailTrace_5025075
  have hstable : (prefixWord ++ tailWord_5025075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025075).length < 2 ^ (prefixWord ++ tailWord_5025075).sum := by decide
  have hdescent : baseEnd_5025075 < baseStart_5025075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025085 : List Nat := [1, 4, 1, 5, 1, 1, 1, 3, 1, 5]
def baseStart_5025085 : Nat := 118140960795 + 5025085 * 2 ^ 59
def prefixEnd_5025085 : Nat := 4983230072969 + 3 ^ 40 * 5025085 * 2
def baseEnd_5025085 : Nat := 860094644899525688509187

theorem tailTrace_5025085 : CollatzResearch.WordTrace tailWord_5025085 prefixEnd_5025085 860094644899525688509187 := by
  unfold tailWord_5025085
  simp only [CollatzResearch.WordTrace]
  refine ⟨183279906999982736037028709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122186604666655157358019139 183279906999982736037028709)
  ·
    refine ⟨34364982562496763006942883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183279906999982736037028709 34364982562496763006942883)
    ·
      refine ⟨51547473843745144510414325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34364982562496763006942883 51547473843745144510414325)
      ·
        refine ⟨4832575672851107297851343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51547473843745144510414325 4832575672851107297851343)
        ·
          refine ⟨7248863509276660946777015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4832575672851107297851343 7248863509276660946777015)
          ·
            refine ⟨10873295263914991420165523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7248863509276660946777015 10873295263914991420165523)
            ·
              refine ⟨16309942895872487130248285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10873295263914991420165523 16309942895872487130248285)
              ·
                refine ⟨6116228585952182673843107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16309942895872487130248285 6116228585952182673843107)
                ·
                  refine ⟨9174342878928274010764661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6116228585952182673843107 9174342878928274010764661)
                  ·
                    refine ⟨860094644899525688509187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9174342878928274010764661 860094644899525688509187)
                    ·
                      rfl

theorem cell23_5025085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_5025085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025085 prefixEnd_5025085 := by exact prefixLift 5025085
  have htrace : WordTrace (prefixWord ++ tailWord_5025085) baseStart_5025085 baseEnd_5025085 := by
    simpa [prefixWord, tailWord_5025085, baseEnd_5025085] using wordTrace_append hprefix tailTrace_5025085
  have hstable : (prefixWord ++ tailWord_5025085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025085).length < 2 ^ (prefixWord ++ tailWord_5025085).sum := by decide
  have hdescent : baseEnd_5025085 < baseStart_5025085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025088 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 5, 2, 2]
def baseStart_5025088 : Nat := 118140960795 + 5025088 * 2 ^ 59
def prefixEnd_5025088 : Nat := 4983230072969 + 3 ^ 40 * 5025088 * 2
def baseEnd_5025088 : Nat := 2580285475140540553790047

theorem tailTrace_5025088 : CollatzResearch.WordTrace tailWord_5025088 prefixEnd_5025088 2580285475140540553790047 := by
  unfold tailWord_5025088
  simp only [CollatzResearch.WordTrace]
  refine ⟨91640008209485933774693959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122186677612647911699591945 91640008209485933774693959)
  ·
    refine ⟨137460012314228900662040939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91640008209485933774693959 137460012314228900662040939)
    ·
      refine ⟨206190018471343350993061409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137460012314228900662040939 206190018471343350993061409)
      ·
        refine ⟨154642513853507513244796057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206190018471343350993061409 154642513853507513244796057)
        ·
          refine ⟨115981885390130634933597043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154642513853507513244796057 115981885390130634933597043)
          ·
            refine ⟨173972828085195952400395565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115981885390130634933597043 173972828085195952400395565)
            ·
              refine ⟨65239810531948482150148337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 173972828085195952400395565 65239810531948482150148337)
              ·
                refine ⟨48929857898961361612611253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65239810531948482150148337 48929857898961361612611253)
                ·
                  refine ⟨4587174178027627651182305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48929857898961361612611253 4587174178027627651182305)
                  ·
                    refine ⟨3440380633520720738386729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4587174178027627651182305 3440380633520720738386729)
                    ·
                      refine ⟨2580285475140540553790047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3440380633520720738386729 2580285475140540553790047)
                      ·
                        rfl

theorem cell23_5025088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 5, 2, 2].length) (baseStart_5025088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025088 prefixEnd_5025088 := by exact prefixLift 5025088
  have htrace : WordTrace (prefixWord ++ tailWord_5025088) baseStart_5025088 baseEnd_5025088 := by
    simpa [prefixWord, tailWord_5025088, baseEnd_5025088] using wordTrace_append hprefix tailTrace_5025088
  have hstable : (prefixWord ++ tailWord_5025088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025088).length < 2 ^ (prefixWord ++ tailWord_5025088).sum := by decide
  have hdescent : baseEnd_5025088 < baseStart_5025088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025105 : List Nat := [1, 2, 2, 1, 4, 1, 4, 1, 3, 2, 2]
def baseStart_5025105 : Nat := 118140960795 + 5025105 * 2 ^ 59
def prefixEnd_5025105 : Nat := 4983230072969 + 3 ^ 40 * 5025105 * 2
def baseEnd_5025105 : Nat := 2580294204311666987277469

theorem tailTrace_5025105 : CollatzResearch.WordTrace tailWord_5025105 prefixEnd_5025105 2580294204311666987277469 := by
  unfold tailWord_5025105
  simp only [CollatzResearch.WordTrace]
  refine ⟨183280636459910279452756769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122187090973273519635171179 183280636459910279452756769)
  ·
    refine ⟨137460477344932709589567577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183280636459910279452756769 137460477344932709589567577)
    ·
      refine ⟨103095358008699532192175683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137460477344932709589567577 103095358008699532192175683)
      ·
        refine ⟨154643037013049298288263525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103095358008699532192175683 154643037013049298288263525)
        ·
          refine ⟨28995569439946743429049411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154643037013049298288263525 28995569439946743429049411)
          ·
            refine ⟨43493354159920115143574117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28995569439946743429049411 43493354159920115143574117)
            ·
              refine ⟨8155003904985021589420147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43493354159920115143574117 8155003904985021589420147)
              ·
                refine ⟨12232505857477532384130221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8155003904985021589420147 12232505857477532384130221)
                ·
                  refine ⟨4587189696554074644048833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12232505857477532384130221 4587189696554074644048833)
                  ·
                    refine ⟨3440392272415555983036625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4587189696554074644048833 3440392272415555983036625)
                    ·
                      refine ⟨2580294204311666987277469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3440392272415555983036625 2580294204311666987277469)
                      ·
                        rfl

theorem cell23_5025105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 3, 2, 2].length) (baseStart_5025105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025105 prefixEnd_5025105 := by exact prefixLift 5025105
  have htrace : WordTrace (prefixWord ++ tailWord_5025105) baseStart_5025105 baseEnd_5025105 := by
    simpa [prefixWord, tailWord_5025105, baseEnd_5025105] using wordTrace_append hprefix tailTrace_5025105
  have hstable : (prefixWord ++ tailWord_5025105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025105).length < 2 ^ (prefixWord ++ tailWord_5025105).sum := by decide
  have hdescent : baseEnd_5025105 < baseStart_5025105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025138 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 6, 1, 3]
def baseStart_5025138 : Nat := 118140960795 + 5025138 * 2 ^ 59
def prefixEnd_5025138 : Nat := 4983230072969 + 3 ^ 40 * 5025138 * 2
def baseEnd_5025138 : Nat := 2580311149173265358164817

theorem tailTrace_5025138 : CollatzResearch.WordTrace tailWord_5025138 prefixEnd_5025138 2580311149173265358164817 := by
  unfold tailWord_5025138
  simp only [CollatzResearch.WordTrace]
  refine ⟨45820460017197681522177017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122187893379193817392472045 45820460017197681522177017)
  ·
    refine ⟨34365345012898261141632763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45820460017197681522177017 34365345012898261141632763)
    ·
      refine ⟨51548017519347391712449145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34365345012898261141632763 51548017519347391712449145)
      ·
        refine ⟨38661013139510543784336859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51548017519347391712449145 38661013139510543784336859)
        ·
          refine ⟨57991519709265815676505289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38661013139510543784336859 57991519709265815676505289)
          ·
            refine ⟨43493639781949361757378967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57991519709265815676505289 43493639781949361757378967)
            ·
              refine ⟨65240459672924042636068451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43493639781949361757378967 65240459672924042636068451)
              ·
                refine ⟨97860689509386063954102677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65240459672924042636068451 97860689509386063954102677)
                ·
                  refine ⟨4587219820752471747848563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 97860689509386063954102677 4587219820752471747848563)
                  ·
                    refine ⟨6880829731128707621772845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4587219820752471747848563 6880829731128707621772845)
                    ·
                      refine ⟨2580311149173265358164817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6880829731128707621772845 2580311149173265358164817)
                      ·
                        rfl

theorem cell23_5025138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_5025138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025138 prefixEnd_5025138 := by exact prefixLift 5025138
  have htrace : WordTrace (prefixWord ++ tailWord_5025138) baseStart_5025138 baseEnd_5025138 := by
    simpa [prefixWord, tailWord_5025138, baseEnd_5025138] using wordTrace_append hprefix tailTrace_5025138
  have hstable : (prefixWord ++ tailWord_5025138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025138).length < 2 ^ (prefixWord ++ tailWord_5025138).sum := by decide
  have hdescent : baseEnd_5025138 < baseStart_5025138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025144 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 3, 2, 8]
def baseStart_5025144 : Nat := 118140960795 + 5025144 * 2 ^ 59
def prefixEnd_5025144 : Nat := 4983230072969 + 3 ^ 40 * 5025144 * 2
def baseEnd_5025144 : Nat := 2580314230057192334689789

theorem tailTrace_5025144 : CollatzResearch.WordTrace tailWord_5025144 prefixEnd_5025144 2580314230057192334689789 := by
  unfold tailWord_5025144
  simp only [CollatzResearch.WordTrace]
  refine ⟨91641029453384494556713243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122188039271179326075617657 91641029453384494556713243)
  ·
    refine ⟨137461544180076741835069865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91641029453384494556713243 137461544180076741835069865)
    ·
      refine ⟨103096158135057556376302399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137461544180076741835069865 103096158135057556376302399)
      ·
        refine ⟨154644237202586334564453599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103096158135057556376302399 154644237202586334564453599)
        ·
          refine ⟨231966355803879501846680399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154644237202586334564453599 231966355803879501846680399)
          ·
            refine ⟨347949533705819252770020599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231966355803879501846680399 347949533705819252770020599)
            ·
              refine ⟨521924300558728879155030899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 347949533705819252770020599 521924300558728879155030899)
              ·
                refine ⟨782886450838093318732546349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 521924300558728879155030899 782886450838093318732546349)
                ·
                  refine ⟨293582419064284994524704881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 782886450838093318732546349 293582419064284994524704881)
                  ·
                    refine ⟨220186814298213745893528661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 293582419064284994524704881 220186814298213745893528661)
                    ·
                      refine ⟨2580314230057192334689789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 220186814298213745893528661 2580314230057192334689789)
                      ·
                        rfl

theorem cell23_5025144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_5025144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025144 prefixEnd_5025144 := by exact prefixLift 5025144
  have htrace : WordTrace (prefixWord ++ tailWord_5025144) baseStart_5025144 baseEnd_5025144 := by
    simpa [prefixWord, tailWord_5025144, baseEnd_5025144] using wordTrace_append hprefix tailTrace_5025144
  have hstable : (prefixWord ++ tailWord_5025144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025144).length < 2 ^ (prefixWord ++ tailWord_5025144).sum := by decide
  have hdescent : baseEnd_5025144 < baseStart_5025144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025172 : List Nat := [2, 4, 2, 1, 2, 2, 1, 3, 2, 1, 3]
def baseStart_5025172 : Nat := 118140960795 + 5025172 * 2 ^ 59
def prefixEnd_5025172 : Nat := 4983230072969 + 3 ^ 40 * 5025172 * 2
def baseEnd_5025172 : Nat := 2580328607515518225139661

theorem tailTrace_5025172 : CollatzResearch.WordTrace tailWord_5025172 prefixEnd_5025172 2580328607515518225139661 := by
  unfold tailWord_5025172
  simp only [CollatzResearch.WordTrace]
  refine ⟨91641540075333774947722885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122188720100445033263630513 91641540075333774947722885)
  ·
    refine ⟨17182788764125082802698041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91641540075333774947722885 17182788764125082802698041)
    ·
      refine ⟨12887091573093812102023531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17182788764125082802698041 12887091573093812102023531)
      ·
        refine ⟨19330637359640718153035297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12887091573093812102023531 19330637359640718153035297)
        ·
          refine ⟨14497978019730538614776473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19330637359640718153035297 14497978019730538614776473)
          ·
            refine ⟨10873483514797903961082355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14497978019730538614776473 10873483514797903961082355)
            ·
              refine ⟨16310225272196855941623533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10873483514797903961082355 16310225272196855941623533)
              ·
                refine ⟨6116334477073820978108825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16310225272196855941623533 6116334477073820978108825)
                ·
                  refine ⟨4587250857805365733581619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6116334477073820978108825 4587250857805365733581619)
                  ·
                    refine ⟨6880876286708048600372429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4587250857805365733581619 6880876286708048600372429)
                    ·
                      refine ⟨2580328607515518225139661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6880876286708048600372429 2580328607515518225139661)
                      ·
                        rfl

theorem cell23_5025172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_5025172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025172 prefixEnd_5025172 := by exact prefixLift 5025172
  have htrace : WordTrace (prefixWord ++ tailWord_5025172) baseStart_5025172 baseEnd_5025172 := by
    simpa [prefixWord, tailWord_5025172, baseEnd_5025172] using wordTrace_append hprefix tailTrace_5025172
  have hstable : (prefixWord ++ tailWord_5025172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025172).length < 2 ^ (prefixWord ++ tailWord_5025172).sum := by decide
  have hdescent : baseEnd_5025172 < baseStart_5025172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025228 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 1, 5, 3]
def baseStart_5025228 : Nat := 118140960795 + 5025228 * 2 ^ 59
def prefixEnd_5025228 : Nat := 4983230072969 + 3 ^ 40 * 5025228 * 2
def baseEnd_5025228 : Nat := 2580357362432170006039403

theorem tailTrace_5025228 : CollatzResearch.WordTrace tailWord_5025228 prefixEnd_5025228 2580357362432170006039403 := by
  unfold tailWord_5025228
  simp only [CollatzResearch.WordTrace]
  refine ⟨91642561319232335729742169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122190081758976447639656225 91642561319232335729742169)
  ·
    refine ⟨68731920989424251797306627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91642561319232335729742169 68731920989424251797306627)
    ·
      refine ⟨103097881484136377695959941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68731920989424251797306627 103097881484136377695959941)
      ·
        refine ⟨19330852778275570817992489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103097881484136377695959941 19330852778275570817992489)
        ·
          refine ⟨14498139583706678113494367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19330852778275570817992489 14498139583706678113494367)
          ·
            refine ⟨21747209375560017170241551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14498139583706678113494367 21747209375560017170241551)
            ·
              refine ⟨32620814063340025755362327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21747209375560017170241551 32620814063340025755362327)
              ·
                refine ⟨48931221095010038633043491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32620814063340025755362327 48931221095010038633043491)
                ·
                  refine ⟨73396831642515057949565237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48931221095010038633043491 73396831642515057949565237)
                  ·
                    refine ⟨6880952966485786682771741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73396831642515057949565237 6880952966485786682771741)
                    ·
                      refine ⟨2580357362432170006039403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6880952966485786682771741 2580357362432170006039403)
                      ·
                        rfl

theorem cell23_5025228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_5025228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025228 prefixEnd_5025228 := by exact prefixLift 5025228
  have htrace : WordTrace (prefixWord ++ tailWord_5025228) baseStart_5025228 baseEnd_5025228 := by
    simpa [prefixWord, tailWord_5025228, baseEnd_5025228] using wordTrace_append hprefix tailTrace_5025228
  have hstable : (prefixWord ++ tailWord_5025228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025228).length < 2 ^ (prefixWord ++ tailWord_5025228).sum := by decide
  have hdescent : baseEnd_5025228 < baseStart_5025228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025231 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 4, 5]
def baseStart_5025231 : Nat := 118140960795 + 5025231 * 2 ^ 59
def prefixEnd_5025231 : Nat := 4983230072969 + 3 ^ 40 * 5025231 * 2
def baseEnd_5025231 : Nat := 860119634291377831433963

theorem tailTrace_5025231 : CollatzResearch.WordTrace tailWord_5025231 prefixEnd_5025231 860119634291377831433963 := by
  unfold tailWord_5025231
  simp only [CollatzResearch.WordTrace]
  refine ⟨183285232057453802971843547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122190154704969201981229031 183285232057453802971843547)
  ·
    refine ⟨274927848086180704457765321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183285232057453802971843547 274927848086180704457765321)
    ·
      refine ⟨206195886064635528343323991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274927848086180704457765321 206195886064635528343323991)
      ·
        refine ⟨309293829096953292514985987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206195886064635528343323991 309293829096953292514985987)
        ·
          refine ⟨463940743645429938772478981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309293829096953292514985987 463940743645429938772478981)
          ·
            refine ⟨86988889433518113519839809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 463940743645429938772478981 86988889433518113519839809)
            ·
              refine ⟨65241667075138585139879857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86988889433518113519839809 65241667075138585139879857)
              ·
                refine ⟨48931250306353938854909893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65241667075138585139879857 48931250306353938854909893)
                ·
                  refine ⟨9174609432441363535295605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48931250306353938854909893 9174609432441363535295605)
                  ·
                    refine ⟨860119634291377831433963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9174609432441363535295605 860119634291377831433963)
                    ·
                      rfl

theorem cell23_5025231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 5].length) (baseStart_5025231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025231 prefixEnd_5025231 := by exact prefixLift 5025231
  have htrace : WordTrace (prefixWord ++ tailWord_5025231) baseStart_5025231 baseEnd_5025231 := by
    simpa [prefixWord, tailWord_5025231, baseEnd_5025231] using wordTrace_append hprefix tailTrace_5025231
  have hstable : (prefixWord ++ tailWord_5025231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025231).length < 2 ^ (prefixWord ++ tailWord_5025231).sum := by decide
  have hdescent : baseEnd_5025231 < baseStart_5025231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025288 : List Nat := [2, 1, 3, 2, 1, 1, 3, 2, 1, 4, 3]
def baseStart_5025288 : Nat := 118140960795 + 5025288 * 2 ^ 59
def prefixEnd_5025288 : Nat := 4983230072969 + 3 ^ 40 * 5025288 * 2
def baseEnd_5025288 : Nat := 2580388171271439771289127

theorem tailTrace_5025288 : CollatzResearch.WordTrace tailWord_5025288 prefixEnd_5025288 2580388171271439771289127 := by
  unfold tailWord_5025288
  simp only [CollatzResearch.WordTrace]
  refine ⟨91643655509123650853334259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122191540678831534471112345 91643655509123650853334259)
  ·
    refine ⟨137465483263685476280001389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91643655509123650853334259 137465483263685476280001389)
    ·
      refine ⟨51549556223882053605000521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137465483263685476280001389 51549556223882053605000521)
      ·
        refine ⟨38662167167911540203750391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51549556223882053605000521 38662167167911540203750391)
        ·
          refine ⟨57993250751867310305625587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38662167167911540203750391 57993250751867310305625587)
          ·
            refine ⟨86989876127800965458438381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57993250751867310305625587 86989876127800965458438381)
            ·
              refine ⟨32621203547925362046914393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86989876127800965458438381 32621203547925362046914393)
              ·
                refine ⟨24465902660944021535185795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32621203547925362046914393 24465902660944021535185795)
                ·
                  refine ⟨36698853991416032302778693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24465902660944021535185795 36698853991416032302778693)
                  ·
                    refine ⟨6881035123390506056771005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36698853991416032302778693 6881035123390506056771005)
                    ·
                      refine ⟨2580388171271439771289127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6881035123390506056771005 2580388171271439771289127)
                      ·
                        rfl

theorem cell23_5025288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_5025288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025288 prefixEnd_5025288 := by exact prefixLift 5025288
  have htrace : WordTrace (prefixWord ++ tailWord_5025288) baseStart_5025288 baseEnd_5025288 := by
    simpa [prefixWord, tailWord_5025288, baseEnd_5025288] using wordTrace_append hprefix tailTrace_5025288
  have hstable : (prefixWord ++ tailWord_5025288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025288).length < 2 ^ (prefixWord ++ tailWord_5025288).sum := by decide
  have hdescent : baseEnd_5025288 < baseStart_5025288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025338 : List Nat := [3, 1, 1, 1, 3, 2, 2, 2, 3, 5]
def baseStart_5025338 : Nat := 118140960795 + 5025338 * 2 ^ 59
def prefixEnd_5025338 : Nat := 4983230072969 + 3 ^ 40 * 5025338 * 2
def baseEnd_5025338 : Nat := 860137948434721525221299

theorem tailTrace_5025338 : CollatzResearch.WordTrace tailWord_5025338 prefixEnd_5025338 860137948434721525221299 := by
  unfold tailWord_5025338
  simp only [CollatzResearch.WordTrace]
  refine ⟨45822283667016540061497167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122192756445377440163992445 45822283667016540061497167)
  ·
    refine ⟨68733425500524810092245751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45822283667016540061497167 68733425500524810092245751)
    ·
      refine ⟨103100138250787215138368627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68733425500524810092245751 103100138250787215138368627)
      ·
        refine ⟨154650207376180822707552941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103100138250787215138368627 154650207376180822707552941)
        ·
          refine ⟨57993827766067808515332353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154650207376180822707552941 57993827766067808515332353)
          ·
            refine ⟨43495370824550856386499265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57993827766067808515332353 43495370824550856386499265)
            ·
              refine ⟨32621528118413142289874449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43495370824550856386499265 32621528118413142289874449)
              ·
                refine ⟨24466146088809856717405837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32621528118413142289874449 24466146088809856717405837)
                ·
                  refine ⟨9174804783303696269027189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24466146088809856717405837 9174804783303696269027189)
                  ·
                    refine ⟨860137948434721525221299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9174804783303696269027189 860137948434721525221299)
                    ·
                      rfl

theorem cell23_5025338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 3, 5].length) (baseStart_5025338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025338 prefixEnd_5025338 := by exact prefixLift 5025338
  have htrace : WordTrace (prefixWord ++ tailWord_5025338) baseStart_5025338 baseEnd_5025338 := by
    simpa [prefixWord, tailWord_5025338, baseEnd_5025338] using wordTrace_append hprefix tailTrace_5025338
  have hstable : (prefixWord ++ tailWord_5025338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025338).length < 2 ^ (prefixWord ++ tailWord_5025338).sum := by decide
  have hdescent : baseEnd_5025338 < baseStart_5025338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025362 : List Nat := [3, 2, 2, 1, 2, 2, 1, 3, 2, 3, 2]
def baseStart_5025362 : Nat := 118140960795 + 5025362 * 2 ^ 59
def prefixEnd_5025362 : Nat := 4983230072969 + 3 ^ 40 * 5025362 * 2
def baseEnd_5025362 : Nat := 2580426168839872481763787

theorem tailTrace_5025362 : CollatzResearch.WordTrace tailWord_5025362 prefixEnd_5025362 2580426168839872481763787 := by
  unfold tailWord_5025362
  simp only [CollatzResearch.WordTrace]
  refine ⟨45822502504994803086215585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122193340013319474896574893 45822502504994803086215585)
  ·
    refine ⟨34366876878746102314661689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45822502504994803086215585 34366876878746102314661689)
    ·
      refine ⟨25775157659059576735996267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34366876878746102314661689 25775157659059576735996267)
      ·
        refine ⟨38662736488589365103994401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25775157659059576735996267 38662736488589365103994401)
        ·
          refine ⟨28997052366442023827995801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38662736488589365103994401 28997052366442023827995801)
          ·
            refine ⟨21747789274831517870996851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28997052366442023827995801 21747789274831517870996851)
            ·
              refine ⟨32621683912247276806495277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21747789274831517870996851 32621683912247276806495277)
              ·
                refine ⟨12233131467092728802435729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32621683912247276806495277 12233131467092728802435729)
                ·
                  refine ⟨9174848600319546601826797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12233131467092728802435729 9174848600319546601826797)
                  ·
                    refine ⟨3440568225119829975685049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9174848600319546601826797 3440568225119829975685049)
                    ·
                      refine ⟨2580426168839872481763787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3440568225119829975685049 2580426168839872481763787)
                      ·
                        rfl

theorem cell23_5025362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_5025362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025362 prefixEnd_5025362 := by exact prefixLift 5025362
  have htrace : WordTrace (prefixWord ++ tailWord_5025362) baseStart_5025362 baseEnd_5025362 := by
    simpa [prefixWord, tailWord_5025362, baseEnd_5025362] using wordTrace_append hprefix tailTrace_5025362
  have hstable : (prefixWord ++ tailWord_5025362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025362).length < 2 ^ (prefixWord ++ tailWord_5025362).sum := by decide
  have hdescent : baseEnd_5025362 < baseStart_5025362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025385 : List Nat := [1, 2, 1, 1, 1, 4, 3, 4, 2, 4]
def baseStart_5025385 : Nat := 118140960795 + 5025385 * 2 ^ 59
def prefixEnd_5025385 : Nat := 4983230072969 + 3 ^ 40 * 5025385 * 2
def baseEnd_5025385 : Nat := 860145992964975297258727

theorem tailTrace_5025385 : CollatzResearch.WordTrace tailWord_5025385 prefixEnd_5025385 860145992964975297258727 := by
  unfold tailWord_5025385
  simp only [CollatzResearch.WordTrace]
  refine ⟨183290848898895887272949609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122193899265930591515299739 183290848898895887272949609)
  ·
    refine ⟨137468136674171915454712207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183290848898895887272949609 137468136674171915454712207)
    ·
      refine ⟨206202205011257873182068311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137468136674171915454712207 206202205011257873182068311)
      ·
        refine ⟨309303307516886809773102467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206202205011257873182068311 309303307516886809773102467)
        ·
          refine ⟨463954961275330214659653701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309303307516886809773102467 463954961275330214659653701)
          ·
            refine ⟨86991555239124415248685069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 463954961275330214659653701 86991555239124415248685069)
            ·
              refine ⟨32621833214671655718256901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86991555239124415248685069 32621833214671655718256901)
              ·
                refine ⟨6116593727750935447173169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32621833214671655718256901 6116593727750935447173169)
                ·
                  refine ⟨4587445295813201585379877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6116593727750935447173169 4587445295813201585379877)
                  ·
                    refine ⟨860145992964975297258727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4587445295813201585379877 860145992964975297258727)
                    ·
                      rfl

theorem cell23_5025385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 2, 4].length) (baseStart_5025385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025385 prefixEnd_5025385 := by exact prefixLift 5025385
  have htrace : WordTrace (prefixWord ++ tailWord_5025385) baseStart_5025385 baseEnd_5025385 := by
    simpa [prefixWord, tailWord_5025385, baseEnd_5025385] using wordTrace_append hprefix tailTrace_5025385
  have hstable : (prefixWord ++ tailWord_5025385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025385).length < 2 ^ (prefixWord ++ tailWord_5025385).sum := by decide
  have hdescent : baseEnd_5025385 < baseStart_5025385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025386 : List Nat := [3, 1, 3, 2, 1, 2, 4, 2, 1, 1, 3]
def baseStart_5025386 : Nat := 118140960795 + 5025386 * 2 ^ 59
def prefixEnd_5025386 : Nat := 4983230072969 + 3 ^ 40 * 5025386 * 2
def baseEnd_5025386 : Nat := 2580438492375580387863677

theorem tailTrace_5025386 : CollatzResearch.WordTrace tailWord_5025386 prefixEnd_5025386 2580438492375580387863677 := by
  unfold tailWord_5025386
  simp only [CollatzResearch.WordTrace]
  refine ⟨45822721342973066110934003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122193923581261509629157341 45822721342973066110934003)
  ·
    refine ⟨68734082014459599166401005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45822721342973066110934003 68734082014459599166401005)
    ·
      refine ⟨25775280755422349687400377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68734082014459599166401005 25775280755422349687400377)
      ·
        refine ⟨19331460566566762265550283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25775280755422349687400377 19331460566566762265550283)
        ·
          refine ⟨28997190849850143398325425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19331460566566762265550283 28997190849850143398325425)
          ·
            refine ⟨21747893137387607548744069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28997190849850143398325425 21747893137387607548744069)
            ·
              refine ⟨4077729963260176415389513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21747893137387607548744069 4077729963260176415389513)
              ·
                refine ⟨3058297472445132311542135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4077729963260176415389513 3058297472445132311542135)
                ·
                  refine ⟨4587446208667698467313203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3058297472445132311542135 4587446208667698467313203)
                  ·
                    refine ⟨6881169313001547700969805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4587446208667698467313203 6881169313001547700969805)
                    ·
                      refine ⟨2580438492375580387863677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6881169313001547700969805 2580438492375580387863677)
                      ·
                        rfl

theorem cell23_5025386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_5025386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025386 prefixEnd_5025386 := by exact prefixLift 5025386
  have htrace : WordTrace (prefixWord ++ tailWord_5025386) baseStart_5025386 baseEnd_5025386 := by
    simpa [prefixWord, tailWord_5025386, baseEnd_5025386] using wordTrace_append hprefix tailTrace_5025386
  have hstable : (prefixWord ++ tailWord_5025386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025386).length < 2 ^ (prefixWord ++ tailWord_5025386).sum := by decide
  have hdescent : baseEnd_5025386 < baseStart_5025386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025388 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 4]
def baseStart_5025388 : Nat := 118140960795 + 5025388 * 2 ^ 59
def prefixEnd_5025388 : Nat := 4983230072969 + 3 ^ 40 * 5025388 * 2
def baseEnd_5025388 : Nat := 2580439519336889380038667

theorem tailTrace_5025388 : CollatzResearch.WordTrace tailWord_5025388 prefixEnd_5025388 2580439519336889380038667 := by
  unfold tailWord_5025388
  simp only [CollatzResearch.WordTrace]
  refine ⟨91645479158942509392654409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122193972211923345856872545 91645479158942509392654409)
  ·
    refine ⟨68734109369206882044490807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91645479158942509392654409 68734109369206882044490807)
    ·
      refine ⟨103101164053810323066736211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68734109369206882044490807 103101164053810323066736211)
      ·
        refine ⟨154651746080715484600104317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103101164053810323066736211 154651746080715484600104317)
        ·
          refine ⟨57994404780268306725039119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154651746080715484600104317 57994404780268306725039119)
          ·
            refine ⟨86991607170402460087558679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57994404780268306725039119 86991607170402460087558679)
            ·
              refine ⟨130487410755603690131338019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86991607170402460087558679 130487410755603690131338019)
              ·
                refine ⟨195731116133405535197007029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130487410755603690131338019 195731116133405535197007029)
                ·
                  refine ⟨18349792137506768924719409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 195731116133405535197007029 18349792137506768924719409)
                  ·
                    refine ⟨13762344103130076693539557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18349792137506768924719409 13762344103130076693539557)
                    ·
                      refine ⟨2580439519336889380038667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13762344103130076693539557 2580439519336889380038667)
                      ·
                        rfl

theorem cell23_5025388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_5025388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025388 prefixEnd_5025388 := by exact prefixLift 5025388
  have htrace : WordTrace (prefixWord ++ tailWord_5025388) baseStart_5025388 baseEnd_5025388 := by
    simpa [prefixWord, tailWord_5025388, baseEnd_5025388] using wordTrace_append hprefix tailTrace_5025388
  have hstable : (prefixWord ++ tailWord_5025388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025388).length < 2 ^ (prefixWord ++ tailWord_5025388).sum := by decide
  have hdescent : baseEnd_5025388 < baseStart_5025388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025405 : List Nat := [1, 4, 1, 1, 4, 1, 1, 3, 1, 2, 4]
def baseStart_5025405 : Nat := 118140960795 + 5025405 * 2 ^ 59
def prefixEnd_5025405 : Nat := 4983230072969 + 3 ^ 40 * 5025405 * 2
def baseEnd_5025405 : Nat := 2580448248508015813526089

theorem tailTrace_5025405 : CollatzResearch.WordTrace tailWord_5025405 prefixEnd_5025405 2580448248508015813526089 := by
  unfold tailWord_5025405
  simp only [CollatzResearch.WordTrace]
  refine ⟨183291578358823430688677669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122194385572548953792451779 183291578358823430688677669)
  ·
    refine ⟨34367170942279393254127063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183291578358823430688677669 34367170942279393254127063)
    ·
      refine ⟨51550756413419089881190595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34367170942279393254127063 51550756413419089881190595)
      ·
        refine ⟨77326134620128634821785893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51550756413419089881190595 77326134620128634821785893)
        ·
          refine ⟨14498650241274119029084855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77326134620128634821785893 14498650241274119029084855)
          ·
            refine ⟨21747975361911178543627283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14498650241274119029084855 21747975361911178543627283)
            ·
              refine ⟨32621963042866767815440925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21747975361911178543627283 32621963042866767815440925)
              ·
                refine ⟨12233236141075037930790347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32621963042866767815440925 12233236141075037930790347)
                ·
                  refine ⟨18349854211612556896185521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12233236141075037930790347 18349854211612556896185521)
                  ·
                    refine ⟨13762390658709417672139141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18349854211612556896185521 13762390658709417672139141)
                    ·
                      refine ⟨2580448248508015813526089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13762390658709417672139141 2580448248508015813526089)
                      ·
                        rfl

theorem cell23_5025405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_5025405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025405 prefixEnd_5025405 := by exact prefixLift 5025405
  have htrace : WordTrace (prefixWord ++ tailWord_5025405) baseStart_5025405 baseEnd_5025405 := by
    simpa [prefixWord, tailWord_5025405, baseEnd_5025405] using wordTrace_append hprefix tailTrace_5025405
  have hstable : (prefixWord ++ tailWord_5025405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025405).length < 2 ^ (prefixWord ++ tailWord_5025405).sum := by decide
  have hdescent : baseEnd_5025405 < baseStart_5025405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025409 : List Nat := [1, 2, 4, 2, 1, 3, 1, 2, 3, 2, 2]
def baseStart_5025409 : Nat := 118140960795 + 5025409 * 2 ^ 59
def prefixEnd_5025409 : Nat := 4983230072969 + 3 ^ 40 * 5025409 * 2
def baseEnd_5025409 : Nat := 2580450302430633797876071

theorem tailTrace_5025409 : CollatzResearch.WordTrace tailWord_5025409 prefixEnd_5025409 2580450302430633797876071 := by
  unfold tailWord_5025409
  simp only [CollatzResearch.WordTrace]
  refine ⟨183291724250808939371823281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122194482833872626247882187 183291724250808939371823281)
  ·
    refine ⟨137468793188106704528867461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183291724250808939371823281 137468793188106704528867461)
    ·
      refine ⟨25775398722770007099162649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137468793188106704528867461 25775398722770007099162649)
      ·
        refine ⟨19331549042077505324371987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25775398722770007099162649 19331549042077505324371987)
        ·
          refine ⟨28997323563116257986557981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19331549042077505324371987 28997323563116257986557981)
          ·
            refine ⟨10873996336168596744959243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28997323563116257986557981 10873996336168596744959243)
            ·
              refine ⟨16310994504252895117438865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10873996336168596744959243 16310994504252895117438865)
              ·
                refine ⟨12233245878189671338079149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16310994504252895117438865 12233245878189671338079149)
                ·
                  refine ⟨4587467204321126751779681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12233245878189671338079149 4587467204321126751779681)
                  ·
                    refine ⟨3440600403240845063834761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4587467204321126751779681 3440600403240845063834761)
                    ·
                      refine ⟨2580450302430633797876071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3440600403240845063834761 2580450302430633797876071)
                      ·
                        rfl

theorem cell23_5025409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_5025409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025409 prefixEnd_5025409 := by exact prefixLift 5025409
  have htrace : WordTrace (prefixWord ++ tailWord_5025409) baseStart_5025409 baseEnd_5025409 := by
    simpa [prefixWord, tailWord_5025409, baseEnd_5025409] using wordTrace_append hprefix tailTrace_5025409
  have hstable : (prefixWord ++ tailWord_5025409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025409).length < 2 ^ (prefixWord ++ tailWord_5025409).sum := by decide
  have hdescent : baseEnd_5025409 < baseStart_5025409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025415 : List Nat := [1, 1, 4, 2, 1, 4, 3, 7]
def baseStart_5025415 : Nat := 118140960795 + 5025415 * 2 ^ 59
def prefixEnd_5025415 : Nat := 4983230072969 + 3 ^ 40 * 5025415 * 2
def baseEnd_5025415 : Nat := 95572347530168917570409

theorem tailTrace_5025415 : CollatzResearch.WordTrace tailWord_5025415 prefixEnd_5025415 95572347530168917570409 := by
  unfold tailWord_5025415
  simp only [CollatzResearch.WordTrace]
  refine ⟨183291943088787202396541699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122194628725858134931027799 183291943088787202396541699)
  ·
    refine ⟨274937914633180803594812549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183291943088787202396541699 274937914633180803594812549)
    ·
      refine ⟨51550858993721400674027353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 274937914633180803594812549 51550858993721400674027353)
      ·
        refine ⟨38663144245291050505520515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51550858993721400674027353 38663144245291050505520515)
        ·
          refine ⟨57994716367936575758280773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38663144245291050505520515 57994716367936575758280773)
          ·
            refine ⟨10874009318988107954677645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57994716367936575758280773 10874009318988107954677645)
            ·
              refine ⟨4077753494620540483004117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10874009318988107954677645 4077753494620540483004117)
              ·
                refine ⟨95572347530168917570409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4077753494620540483004117 95572347530168917570409)
                ·
                  rfl

theorem cell23_5025415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 7].length) (baseStart_5025415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025415 prefixEnd_5025415 := by exact prefixLift 5025415
  have htrace : WordTrace (prefixWord ++ tailWord_5025415) baseStart_5025415 baseEnd_5025415 := by
    simpa [prefixWord, tailWord_5025415, baseEnd_5025415] using wordTrace_append hprefix tailTrace_5025415
  have hstable : (prefixWord ++ tailWord_5025415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025415).length < 2 ^ (prefixWord ++ tailWord_5025415).sum := by decide
  have hdescent : baseEnd_5025415 < baseStart_5025415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025426 : List Nat := [3, 2, 3, 1, 3, 2, 2, 1, 1, 1, 4]
def baseStart_5025426 : Nat := 118140960795 + 5025426 * 2 ^ 59
def prefixEnd_5025426 : Nat := 4983230072969 + 3 ^ 40 * 5025426 * 2
def baseEnd_5025426 : Nat := 2580459031601760231363493

theorem tailTrace_5025426 : CollatzResearch.WordTrace tailWord_5025426 prefixEnd_5025426 2580459031601760231363493 := by
  unfold tailWord_5025426
  simp only [CollatzResearch.WordTrace]
  refine ⟨45823086072936837818798033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122194896194498234183461421 45823086072936837818798033)
  ·
    refine ⟨34367314554702628364098525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45823086072936837818798033 34367314554702628364098525)
    ·
      refine ⟨12887742958013485636536947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34367314554702628364098525 12887742958013485636536947)
      ·
        refine ⟨19331614437020228454805421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12887742958013485636536947 19331614437020228454805421)
        ·
          refine ⟨7249355413882585670552033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19331614437020228454805421 7249355413882585670552033)
          ·
            refine ⟨5437016560411939252914025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7249355413882585670552033 5437016560411939252914025)
            ·
              refine ⟨4077762420308954439685519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5437016560411939252914025 4077762420308954439685519)
              ·
                refine ⟨6116643630463431659528279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4077762420308954439685519 6116643630463431659528279)
                ·
                  refine ⟨9174965445695147489292419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6116643630463431659528279 9174965445695147489292419)
                  ·
                    refine ⟨13762448168542721233938629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9174965445695147489292419 13762448168542721233938629)
                    ·
                      refine ⟨2580459031601760231363493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13762448168542721233938629 2580459031601760231363493)
                      ·
                        rfl

theorem cell23_5025426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_5025426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025426 prefixEnd_5025426 := by exact prefixLift 5025426
  have htrace : WordTrace (prefixWord ++ tailWord_5025426) baseStart_5025426 baseEnd_5025426 := by
    simpa [prefixWord, tailWord_5025426, baseEnd_5025426] using wordTrace_append hprefix tailTrace_5025426
  have hstable : (prefixWord ++ tailWord_5025426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025426).length < 2 ^ (prefixWord ++ tailWord_5025426).sum := by decide
  have hdescent : baseEnd_5025426 < baseStart_5025426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025436 : List Nat := [2, 2, 3, 2, 4, 1, 1, 2, 2, 4]
def baseStart_5025436 : Nat := 118140960795 + 5025436 * 2 ^ 59
def prefixEnd_5025436 : Nat := 4983230072969 + 3 ^ 40 * 5025436 * 2
def baseEnd_5025436 : Nat := 860154722136101730746149

theorem tailTrace_5025436 : CollatzResearch.WordTrace tailWord_5025436 prefixEnd_5025436 860154722136101730746149 := by
  unfold tailWord_5025436
  simp only [CollatzResearch.WordTrace]
  refine ⟨91646354510855561491528081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122195139347807415322037441 91646354510855561491528081)
  ·
    refine ⟨68734765883141671118646061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91646354510855561491528081 68734765883141671118646061)
    ·
      refine ⟨25775537206178126669492273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68734765883141671118646061 25775537206178126669492273)
      ·
        refine ⟨19331652904633595002119205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25775537206178126669492273 19331652904633595002119205)
        ·
          refine ⟨3624684919618799062897351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19331652904633595002119205 3624684919618799062897351)
          ·
            refine ⟨5437027379428198594346027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3624684919618799062897351 5437027379428198594346027)
            ·
              refine ⟨8155541069142297891519041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5437027379428198594346027 8155541069142297891519041)
              ·
                refine ⟨6116655801856723418639281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8155541069142297891519041 6116655801856723418639281)
                ·
                  refine ⟨4587491851392542563979461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6116655801856723418639281 4587491851392542563979461)
                  ·
                    refine ⟨860154722136101730746149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4587491851392542563979461 860154722136101730746149)
                    ·
                      rfl

theorem cell23_5025436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_5025436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025436 prefixEnd_5025436 := by exact prefixLift 5025436
  have htrace : WordTrace (prefixWord ++ tailWord_5025436) baseStart_5025436 baseEnd_5025436 := by
    simpa [prefixWord, tailWord_5025436, baseEnd_5025436] using wordTrace_append hprefix tailTrace_5025436
  have hstable : (prefixWord ++ tailWord_5025436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025436).length < 2 ^ (prefixWord ++ tailWord_5025436).sum := by decide
  have hdescent : baseEnd_5025436 < baseStart_5025436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025459 : List Nat := [1, 1, 1, 2, 3, 3, 5, 1, 2, 1, 3]
def baseStart_5025459 : Nat := 118140960795 + 5025459 * 2 ^ 59
def prefixEnd_5025459 : Nat := 4983230072969 + 3 ^ 40 * 5025459 * 2
def baseEnd_5025459 : Nat := 2580475976463358602250841

theorem tailTrace_5025459 : CollatzResearch.WordTrace tailWord_5025459 prefixEnd_5025459 2580475976463358602250841 := by
  unfold tailWord_5025459
  simp only [CollatzResearch.WordTrace]
  refine ⟨183293547900627797911143431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122195698600418531940762287 183293547900627797911143431)
  ·
    refine ⟨274940321850941696866715147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183293547900627797911143431 274940321850941696866715147)
    ·
      refine ⟨412410482776412545300072721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274940321850941696866715147 412410482776412545300072721)
      ·
        refine ⟨309307862082309408975054541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412410482776412545300072721 309307862082309408975054541)
        ·
          refine ⟨115990448280866028365645453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 309307862082309408975054541 115990448280866028365645453)
          ·
            refine ⟨43496418105324760637117045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115990448280866028365645453 43496418105324760637117045)
            ·
              refine ⟨4077789197374196309729723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43496418105324760637117045 4077789197374196309729723)
              ·
                refine ⟨6116683796061294464594585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4077789197374196309729723 6116683796061294464594585)
                ·
                  refine ⟨4587512847045970848445939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6116683796061294464594585 4587512847045970848445939)
                  ·
                    refine ⟨6881269270568956272668909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4587512847045970848445939 6881269270568956272668909)
                    ·
                      refine ⟨2580475976463358602250841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6881269270568956272668909 2580475976463358602250841)
                      ·
                        rfl

theorem cell23_5025459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 2, 1, 3].length) (baseStart_5025459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025459 prefixEnd_5025459 := by exact prefixLift 5025459
  have htrace : WordTrace (prefixWord ++ tailWord_5025459) baseStart_5025459 baseEnd_5025459 := by
    simpa [prefixWord, tailWord_5025459, baseEnd_5025459] using wordTrace_append hprefix tailTrace_5025459
  have hstable : (prefixWord ++ tailWord_5025459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025459).length < 2 ^ (prefixWord ++ tailWord_5025459).sum := by decide
  have hdescent : baseEnd_5025459 < baseStart_5025459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025469 : List Nat := [1, 4, 1, 2, 1, 2, 4, 2, 1, 3, 2]
def baseStart_5025469 : Nat := 118140960795 + 5025469 * 2 ^ 59
def prefixEnd_5025469 : Nat := 4983230072969 + 3 ^ 40 * 5025469 * 2
def baseEnd_5025469 : Nat := 2580481111269903563125795

theorem tailTrace_5025469 : CollatzResearch.WordTrace tailWord_5025469 prefixEnd_5025469 2580481111269903563125795 := by
  unfold tailWord_5025469
  simp only [CollatzResearch.WordTrace]
  refine ⟨183293912630591569619007461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122195941753727713079338307 183293912630591569619007461)
  ·
    refine ⟨34367608618235919303563899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183293912630591569619007461 34367608618235919303563899)
    ·
      refine ⟨51551412927353878955345849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34367608618235919303563899 51551412927353878955345849)
      ·
        refine ⟨38663559695515409216509387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51551412927353878955345849 38663559695515409216509387)
        ·
          refine ⟨57995339543273113824764081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38663559695515409216509387 57995339543273113824764081)
          ·
            refine ⟨43496504657454835368573061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57995339543273113824764081 43496504657454835368573061)
            ·
              refine ⟨8155594623272781631607449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43496504657454835368573061 8155594623272781631607449)
              ·
                refine ⟨6116695967454586223705587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8155594623272781631607449 6116695967454586223705587)
                ·
                  refine ⟨9175043951181879335558381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6116695967454586223705587 9175043951181879335558381)
                  ·
                    refine ⟨3440641481693204750834393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9175043951181879335558381 3440641481693204750834393)
                    ·
                      refine ⟨2580481111269903563125795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3440641481693204750834393 2580481111269903563125795)
                      ·
                        rfl

theorem cell23_5025469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_5025469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025469 prefixEnd_5025469 := by exact prefixLift 5025469
  have htrace : WordTrace (prefixWord ++ tailWord_5025469) baseStart_5025469 baseEnd_5025469 := by
    simpa [prefixWord, tailWord_5025469, baseEnd_5025469] using wordTrace_append hprefix tailTrace_5025469
  have hstable : (prefixWord ++ tailWord_5025469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025469).length < 2 ^ (prefixWord ++ tailWord_5025469).sum := by decide
  have hdescent : baseEnd_5025469 < baseStart_5025469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025515 : List Nat := [1, 1, 1, 1, 2, 4, 2, 3, 2, 3, 3]
def baseStart_5025515 : Nat := 118140960795 + 5025515 * 2 ^ 59
def prefixEnd_5025515 : Nat := 4983230072969 + 3 ^ 40 * 5025515 * 2
def baseEnd_5025515 : Nat := 2580504731380010383150583

theorem tailTrace_5025515 : CollatzResearch.WordTrace tailWord_5025515 prefixEnd_5025515 2580504731380010383150583 := by
  unfold tailWord_5025515
  simp only [CollatzResearch.WordTrace]
  refine ⟨183295590388424919475181999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122197060258949946316787999 183295590388424919475181999)
  ·
    refine ⟨274943385582637379212772999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183295590388424919475181999 274943385582637379212772999)
    ·
      refine ⟨412415078373956068819159499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274943385582637379212772999 412415078373956068819159499)
      ·
        refine ⟨618622617560934103228739249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412415078373956068819159499 618622617560934103228739249)
        ·
          refine ⟨463966963170700577421554437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 618622617560934103228739249 463966963170700577421554437)
          ·
            refine ⟨86993805594506358266541457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 463966963170700577421554437 86993805594506358266541457)
            ·
              refine ⟨65245354195879768699906093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86993805594506358266541457 65245354195879768699906093)
              ·
                refine ⟨24467007823454913262464785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65245354195879768699906093 24467007823454913262464785)
                ·
                  refine ⟨18350255867591184946848589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24467007823454913262464785 18350255867591184946848589)
                  ·
                    refine ⟨6881345950346694355068221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18350255867591184946848589 6881345950346694355068221)
                    ·
                      refine ⟨2580504731380010383150583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6881345950346694355068221 2580504731380010383150583)
                      ·
                        rfl

theorem cell23_5025515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 2, 3, 3].length) (baseStart_5025515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025515 prefixEnd_5025515 := by exact prefixLift 5025515
  have htrace : WordTrace (prefixWord ++ tailWord_5025515) baseStart_5025515 baseEnd_5025515 := by
    simpa [prefixWord, tailWord_5025515, baseEnd_5025515] using wordTrace_append hprefix tailTrace_5025515
  have hstable : (prefixWord ++ tailWord_5025515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025515).length < 2 ^ (prefixWord ++ tailWord_5025515).sum := by decide
  have hdescent : baseEnd_5025515 < baseStart_5025515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025516 : List Nat := [2, 2, 1, 1, 2, 2, 6, 1, 2, 2, 2]
def baseStart_5025516 : Nat := 118140960795 + 5025516 * 2 ^ 59
def prefixEnd_5025516 : Nat := 4983230072969 + 3 ^ 40 * 5025516 * 2
def baseEnd_5025516 : Nat := 2580505244860664879238079

theorem tailTrace_5025516 : CollatzResearch.WordTrace tailWord_5025516 prefixEnd_5025516 2580505244860664879238079 := by
  unfold tailWord_5025516
  simp only [CollatzResearch.WordTrace]
  refine ⟨91647813430710648322984201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122197084574280864430645601 91647813430710648322984201)
  ·
    refine ⟨68735860073032986242238151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91647813430710648322984201 68735860073032986242238151)
    ·
      refine ⟨103103790109549479363357227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68735860073032986242238151 103103790109549479363357227)
      ·
        refine ⟨154655685164324219045035841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103103790109549479363357227 154655685164324219045035841)
        ·
          refine ⟨115991763873243164283776881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154655685164324219045035841 115991763873243164283776881)
          ·
            refine ⟨86993822904932373212832661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115991763873243164283776881 86993822904932373212832661)
            ·
              refine ⟨4077835448668704994351531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86993822904932373212832661 4077835448668704994351531)
              ·
                refine ⟨6116753173003057491527297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4077835448668704994351531 6116753173003057491527297)
                ·
                  refine ⟨4587564879752293118645473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6116753173003057491527297 4587564879752293118645473)
                  ·
                    refine ⟨3440673659814219838984105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4587564879752293118645473 3440673659814219838984105)
                    ·
                      refine ⟨2580505244860664879238079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3440673659814219838984105 2580505244860664879238079)
                      ·
                        rfl

theorem cell23_5025516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 2, 2].length) (baseStart_5025516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025516 prefixEnd_5025516 := by exact prefixLift 5025516
  have htrace : WordTrace (prefixWord ++ tailWord_5025516) baseStart_5025516 baseEnd_5025516 := by
    simpa [prefixWord, tailWord_5025516, baseEnd_5025516] using wordTrace_append hprefix tailTrace_5025516
  have hstable : (prefixWord ++ tailWord_5025516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025516).length < 2 ^ (prefixWord ++ tailWord_5025516).sum := by decide
  have hdescent : baseEnd_5025516 < baseStart_5025516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025535 : List Nat := [1, 1, 2, 2, 1, 3, 3, 3, 2, 5]
def baseStart_5025535 : Nat := 118140960795 + 5025535 * 2 ^ 59
def prefixEnd_5025535 : Nat := 4983230072969 + 3 ^ 40 * 5025535 * 2
def baseEnd_5025535 : Nat := 860171666997700101633497

theorem tailTrace_5025535 : CollatzResearch.WordTrace tailWord_5025535 prefixEnd_5025535 860171666997700101633497 := by
  unfold tailWord_5025535
  simp only [CollatzResearch.WordTrace]
  refine ⟨183296319848352462890910059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122197546565568308593940039 183296319848352462890910059)
  ·
    refine ⟨274944479772528694336365089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183296319848352462890910059 274944479772528694336365089)
    ·
      refine ⟨206208359829396520752273817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274944479772528694336365089 206208359829396520752273817)
      ·
        refine ⟨154656269872047390564205363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206208359829396520752273817 154656269872047390564205363)
        ·
          refine ⟨231984404808071085846308045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154656269872047390564205363 231984404808071085846308045)
          ·
            refine ⟨86994151803026657192365517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231984404808071085846308045 86994151803026657192365517)
            ·
              refine ⟨32622806926134996447137069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86994151803026657192365517 32622806926134996447137069)
              ·
                refine ⟨12233552597300623667676401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32622806926134996447137069 12233552597300623667676401)
                ·
                  refine ⟨9175164447975467750757301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12233552597300623667676401 9175164447975467750757301)
                  ·
                    refine ⟨860171666997700101633497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9175164447975467750757301 860171666997700101633497)
                    ·
                      rfl

theorem cell23_5025535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 5].length) (baseStart_5025535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025535 prefixEnd_5025535 := by exact prefixLift 5025535
  have htrace : WordTrace (prefixWord ++ tailWord_5025535) baseStart_5025535 baseEnd_5025535 := by
    simpa [prefixWord, tailWord_5025535, baseEnd_5025535] using wordTrace_append hprefix tailTrace_5025535
  have hstable : (prefixWord ++ tailWord_5025535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025535).length < 2 ^ (prefixWord ++ tailWord_5025535).sum := by decide
  have hdescent : baseEnd_5025535 < baseStart_5025535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025555 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 4]
def baseStart_5025555 : Nat := 118140960795 + 5025555 * 2 ^ 59
def prefixEnd_5025555 : Nat := 4983230072969 + 3 ^ 40 * 5025555 * 2
def baseEnd_5025555 : Nat := 2580525270606190226650399

theorem tailTrace_5025555 : CollatzResearch.WordTrace tailWord_5025555 prefixEnd_5025555 2580525270606190226650399 := by
  unfold tailWord_5025555
  simp only [CollatzResearch.WordTrace]
  refine ⟨183297049308280006306638119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122198032872186670871092079 183297049308280006306638119)
  ·
    refine ⟨274945573962420009459957179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183297049308280006306638119 274945573962420009459957179)
    ·
      refine ⟨412418360943630014189935769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274945573962420009459957179 412418360943630014189935769)
      ·
        refine ⟨309313770707722510642451827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412418360943630014189935769 309313770707722510642451827)
        ·
          refine ⟨463970656061583765963677741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309313770707722510642451827 463970656061583765963677741)
          ·
            refine ⟨173988996023093912236379153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 463970656061583765963677741 173988996023093912236379153)
            ·
              refine ⟨130491747017320434177284365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173988996023093912236379153 130491747017320434177284365)
              ·
                refine ⟨48934405131495162816481637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130491747017320434177284365 48934405131495162816481637)
                ·
                  refine ⟨9175200962155343028090307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48934405131495162816481637 9175200962155343028090307)
                  ·
                    refine ⟨13762801443233014542135461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9175200962155343028090307 13762801443233014542135461)
                    ·
                      refine ⟨2580525270606190226650399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13762801443233014542135461 2580525270606190226650399)
                      ·
                        rfl

theorem cell23_5025555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 4].length) (baseStart_5025555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025555 prefixEnd_5025555 := by exact prefixLift 5025555
  have htrace : WordTrace (prefixWord ++ tailWord_5025555) baseStart_5025555 baseEnd_5025555 := by
    simpa [prefixWord, tailWord_5025555, baseEnd_5025555] using wordTrace_append hprefix tailTrace_5025555
  have hstable : (prefixWord ++ tailWord_5025555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025555).length < 2 ^ (prefixWord ++ tailWord_5025555).sum := by decide
  have hdescent : baseEnd_5025555 < baseStart_5025555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025592 : List Nat := [2, 1, 2, 1, 3, 4, 1, 1, 1, 4, 3]
def baseStart_5025592 : Nat := 118140960795 + 5025592 * 2 ^ 59
def prefixEnd_5025592 : Nat := 4983230072969 + 3 ^ 40 * 5025592 * 2
def baseEnd_5025592 : Nat := 2580544269390406581887729

theorem tailTrace_5025592 : CollatzResearch.WordTrace tailWord_5025592 prefixEnd_5025592 2580544269390406581887729 := by
  unfold tailWord_5025592
  simp only [CollatzResearch.WordTrace]
  refine ⟨91649199404572980812867515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122198932539430641083823353 91649199404572980812867515)
  ·
    refine ⟨137473799106859471219301273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91649199404572980812867515 137473799106859471219301273)
    ·
      refine ⟨103105349330144603414475955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137473799106859471219301273 103105349330144603414475955)
      ·
        refine ⟨154658023995216905121713933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103105349330144603414475955 154658023995216905121713933)
        ·
          refine ⟨57996758998206339420642725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154658023995216905121713933 57996758998206339420642725)
          ·
            refine ⟨10874392312163688641370511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57996758998206339420642725 10874392312163688641370511)
            ·
              refine ⟨16311588468245532962055767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10874392312163688641370511 16311588468245532962055767)
              ·
                refine ⟨24467382702368299443083651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16311588468245532962055767 24467382702368299443083651)
                ·
                  refine ⟨36701074053552449164625477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24467382702368299443083651 36701074053552449164625477)
                  ·
                    refine ⟨6881451385041084218367277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36701074053552449164625477 6881451385041084218367277)
                    ·
                      refine ⟨2580544269390406581887729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6881451385041084218367277 2580544269390406581887729)
                      ·
                        rfl

theorem cell23_5025592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 1, 4, 3].length) (baseStart_5025592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025592 prefixEnd_5025592 := by exact prefixLift 5025592
  have htrace : WordTrace (prefixWord ++ tailWord_5025592) baseStart_5025592 baseEnd_5025592 := by
    simpa [prefixWord, tailWord_5025592, baseEnd_5025592] using wordTrace_append hprefix tailTrace_5025592
  have hstable : (prefixWord ++ tailWord_5025592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025592).length < 2 ^ (prefixWord ++ tailWord_5025592).sum := by decide
  have hdescent : baseEnd_5025592 < baseStart_5025592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025612 : List Nat := [2, 2, 1, 3, 4, 1, 1, 1, 8]
def baseStart_5025612 : Nat := 118140960795 + 5025612 * 2 ^ 59
def prefixEnd_5025612 : Nat := 4983230072969 + 3 ^ 40 * 5025612 * 2
def baseEnd_5025612 : Nat := 286728282111499611515293

theorem tailTrace_5025612 : CollatzResearch.WordTrace tailWord_5025612 prefixEnd_5025612 286728282111499611515293 := by
  unfold tailWord_5025612
  simp only [CollatzResearch.WordTrace]
  refine ⟨91649564134536752520731545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122199418846049003360975393 91649564134536752520731545)
  ·
    refine ⟨68737173100902564390548659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91649564134536752520731545 68737173100902564390548659)
    ·
      refine ⟨103105759651353846585822989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68737173100902564390548659 103105759651353846585822989)
      ·
        refine ⟨38664659869257692469683621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103105759651353846585822989 38664659869257692469683621)
        ·
          refine ⟨7249623725485817338065679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38664659869257692469683621 7249623725485817338065679)
          ·
            refine ⟨10874435588228726007098519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7249623725485817338065679 10874435588228726007098519)
            ·
              refine ⟨16311653382343089010647779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10874435588228726007098519 16311653382343089010647779)
              ·
                refine ⟨24467480073514633515971669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16311653382343089010647779 24467480073514633515971669)
                ·
                  refine ⟨286728282111499611515293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24467480073514633515971669 286728282111499611515293)
                  ·
                    rfl

theorem cell23_5025612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 8].length) (baseStart_5025612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025612 prefixEnd_5025612 := by exact prefixLift 5025612
  have htrace : WordTrace (prefixWord ++ tailWord_5025612) baseStart_5025612 baseEnd_5025612 := by
    simpa [prefixWord, tailWord_5025612, baseEnd_5025612] using wordTrace_append hprefix tailTrace_5025612
  have hstable : (prefixWord ++ tailWord_5025612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025612).length < 2 ^ (prefixWord ++ tailWord_5025612).sum := by decide
  have hdescent : baseEnd_5025612 < baseStart_5025612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025639 : List Nat := [1, 1, 5, 1, 2, 1, 1, 4, 3, 1, 3]
def baseStart_5025639 : Nat := 118140960795 + 5025639 * 2 ^ 59
def prefixEnd_5025639 : Nat := 4983230072969 + 3 ^ 40 * 5025639 * 2
def baseEnd_5025639 : Nat := 2580568402981167898000013

theorem tailTrace_5025639 : CollatzResearch.WordTrace tailWord_5025639 prefixEnd_5025639 2580568402981167898000013 := by
  unfold tailWord_5025639
  simp only [CollatzResearch.WordTrace]
  refine ⟨183300113039975688652695971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122200075359983792435130647 183300113039975688652695971)
  ·
    refine ⟨274950169559963532979043957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183300113039975688652695971 274950169559963532979043957)
    ·
      refine ⟨25776578396246581216785371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 274950169559963532979043957 25776578396246581216785371)
      ·
        refine ⟨38664867594369871825178057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25776578396246581216785371 38664867594369871825178057)
        ·
          refine ⟨28998650695777403868883543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38664867594369871825178057 28998650695777403868883543)
          ·
            refine ⟨43497976043666105803325315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28998650695777403868883543 43497976043666105803325315)
            ·
              refine ⟨65246964065499158704987973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43497976043666105803325315 65246964065499158704987973)
              ·
                refine ⟨12233805762281092257185245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65246964065499158704987973 12233805762281092257185245)
                ·
                  refine ⟨4587677160855409596444467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12233805762281092257185245 4587677160855409596444467)
                  ·
                    refine ⟨6881515741283114394666701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4587677160855409596444467 6881515741283114394666701)
                    ·
                      refine ⟨2580568402981167898000013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6881515741283114394666701 2580568402981167898000013)
                      ·
                        rfl

theorem cell23_5025639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_5025639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025639 prefixEnd_5025639 := by exact prefixLift 5025639
  have htrace : WordTrace (prefixWord ++ tailWord_5025639) baseStart_5025639 baseEnd_5025639 := by
    simpa [prefixWord, tailWord_5025639, baseEnd_5025639] using wordTrace_append hprefix tailTrace_5025639
  have hstable : (prefixWord ++ tailWord_5025639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025639).length < 2 ^ (prefixWord ++ tailWord_5025639).sum := by decide
  have hdescent : baseEnd_5025639 < baseStart_5025639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025649 : List Nat := [1, 2, 2, 2, 1, 3, 2, 3, 2, 3, 2]
def baseStart_5025649 : Nat := 118140960795 + 5025649 * 2 ^ 59
def prefixEnd_5025649 : Nat := 4983230072969 + 3 ^ 40 * 5025649 * 2
def baseEnd_5025649 : Nat := 2580573537787712858874967

theorem tailTrace_5025649 : CollatzResearch.WordTrace tailWord_5025649 prefixEnd_5025649 2580573537787712858874967 := by
  unfold tailWord_5025649
  simp only [CollatzResearch.WordTrace]
  refine ⟨183300477769939460360560001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122200318513292973573706667 183300477769939460360560001)
  ·
    refine ⟨137475358327454595270420001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183300477769939460360560001 137475358327454595270420001)
    ·
      refine ⟨103106518745590946452815001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137475358327454595270420001 103106518745590946452815001)
      ·
        refine ⟨77329889059193209839611251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103106518745590946452815001 77329889059193209839611251)
        ·
          refine ⟨115994833588789814759416877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77329889059193209839611251 115994833588789814759416877)
          ·
            refine ⟨43498062595796180534781329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115994833588789814759416877 43498062595796180534781329)
            ·
              refine ⟨32623546946847135401085997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43498062595796180534781329 32623546946847135401085997)
              ·
                refine ⟨12233830105067675775407249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32623546946847135401085997 12233830105067675775407249)
                ·
                  refine ⟨9175372578800756831555437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12233830105067675775407249 9175372578800756831555437)
                  ·
                    refine ⟨3440764717050283811833289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9175372578800756831555437 3440764717050283811833289)
                    ·
                      refine ⟨2580573537787712858874967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3440764717050283811833289 2580573537787712858874967)
                      ·
                        rfl

theorem cell23_5025649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 3, 2].length) (baseStart_5025649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025649 prefixEnd_5025649 := by exact prefixLift 5025649
  have htrace : WordTrace (prefixWord ++ tailWord_5025649) baseStart_5025649 baseEnd_5025649 := by
    simpa [prefixWord, tailWord_5025649, baseEnd_5025649] using wordTrace_append hprefix tailTrace_5025649
  have hstable : (prefixWord ++ tailWord_5025649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025649).length < 2 ^ (prefixWord ++ tailWord_5025649).sum := by decide
  have hdescent : baseEnd_5025649 < baseStart_5025649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025673 : List Nat := [1, 2, 1, 1, 5, 1, 5, 2, 1, 1, 3]
def baseStart_5025673 : Nat := 118140960795 + 5025673 * 2 ^ 59
def prefixEnd_5025673 : Nat := 4983230072969 + 3 ^ 40 * 5025673 * 2
def baseEnd_5025673 : Nat := 2580585861323420764974857

theorem tailTrace_5025673 : CollatzResearch.WordTrace tailWord_5025673 prefixEnd_5025673 2580585861323420764974857 := by
  unfold tailWord_5025673
  simp only [CollatzResearch.WordTrace]
  refine ⟨183301353121852512459433673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122200902081235008306289115 183301353121852512459433673)
  ·
    refine ⟨137476014841389384344575255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183301353121852512459433673 137476014841389384344575255)
    ·
      refine ⟨206214022262084076516862883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137476014841389384344575255 206214022262084076516862883)
      ·
        refine ⟨309321033393126114775294325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206214022262084076516862883 309321033393126114775294325)
        ·
          refine ⟨28998846880605573260183843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 309321033393126114775294325 28998846880605573260183843)
          ·
            refine ⟨43498270320908359890275765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28998846880605573260183843 43498270320908359890275765)
            ·
              refine ⟨4077962842585158739713353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43498270320908359890275765 4077962842585158739713353)
              ·
                refine ⟨3058472131938869054785015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4077962842585158739713353 3058472131938869054785015)
                ·
                  refine ⟨4587708197908303582177523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3058472131938869054785015 4587708197908303582177523)
                  ·
                    refine ⟨6881562296862455373266285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4587708197908303582177523 6881562296862455373266285)
                    ·
                      refine ⟨2580585861323420764974857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6881562296862455373266285 2580585861323420764974857)
                      ·
                        rfl

theorem cell23_5025673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 2, 1, 1, 3].length) (baseStart_5025673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025673 prefixEnd_5025673 := by exact prefixLift 5025673
  have htrace : WordTrace (prefixWord ++ tailWord_5025673) baseStart_5025673 baseEnd_5025673 := by
    simpa [prefixWord, tailWord_5025673, baseEnd_5025673] using wordTrace_append hprefix tailTrace_5025673
  have hstable : (prefixWord ++ tailWord_5025673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025673).length < 2 ^ (prefixWord ++ tailWord_5025673).sum := by decide
  have hdescent : baseEnd_5025673 < baseStart_5025673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025724 : List Nat := [2, 2, 2, 5, 2, 1, 2, 2, 1, 1, 3]
def baseStart_5025724 : Nat := 118140960795 + 5025724 * 2 ^ 59
def prefixEnd_5025724 : Nat := 4983230072969 + 3 ^ 40 * 5025724 * 2
def baseEnd_5025724 : Nat := 2580612048836800065437123

theorem tailTrace_5025724 : CollatzResearch.WordTrace tailWord_5025724 prefixEnd_5025724 2580612048836800065437123 := by
  unfold tailWord_5025724
  simp only [CollatzResearch.WordTrace]
  refine ⟨91651606622333874084770113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122202142163111832113026817 91651606622333874084770113)
  ·
    refine ⟨68738704966750405563577585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91651606622333874084770113 68738704966750405563577585)
    ·
      refine ⟨51554028725062804172683189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68738704966750405563577585 51554028725062804172683189)
      ·
        refine ⟨4833190192974637891189049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51554028725062804172683189 4833190192974637891189049)
        ·
          refine ⟨3624892644730978418391787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4833190192974637891189049 3624892644730978418391787)
          ·
            refine ⟨5437338967096467627587681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3624892644730978418391787 5437338967096467627587681)
            ·
              refine ⟨4078004225322350720690761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5437338967096467627587681 4078004225322350720690761)
              ·
                refine ⟨3058503168991763040518071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4078004225322350720690761 3058503168991763040518071)
                ·
                  refine ⟨4587754753487644560777107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3058503168991763040518071 4587754753487644560777107)
                  ·
                    refine ⟨6881632130231466841165661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4587754753487644560777107 6881632130231466841165661)
                    ·
                      refine ⟨2580612048836800065437123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6881632130231466841165661 2580612048836800065437123)
                      ·
                        rfl

theorem cell23_5025724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_5025724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025724 prefixEnd_5025724 := by exact prefixLift 5025724
  have htrace : WordTrace (prefixWord ++ tailWord_5025724) baseStart_5025724 baseEnd_5025724 := by
    simpa [prefixWord, tailWord_5025724, baseEnd_5025724] using wordTrace_append hprefix tailTrace_5025724
  have hstable : (prefixWord ++ tailWord_5025724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025724).length < 2 ^ (prefixWord ++ tailWord_5025724).sum := by decide
  have hdescent : baseEnd_5025724 < baseStart_5025724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025739 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 5, 3, 2]
def baseStart_5025739 : Nat := 118140960795 + 5025739 * 2 ^ 59
def prefixEnd_5025739 : Nat := 4983230072969 + 3 ^ 40 * 5025739 * 2
def baseEnd_5025739 : Nat := 2580619751046617506749553

theorem tailTrace_5025739 : CollatzResearch.WordTrace tailWord_5025739 prefixEnd_5025739 2580619751046617506749553 := by
  unfold tailWord_5025739
  simp only [CollatzResearch.WordTrace]
  refine ⟨183303760339613405731336271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122202506893075603820890847 183303760339613405731336271)
  ·
    refine ⟨274955640509420108597004407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183303760339613405731336271 274955640509420108597004407)
    ·
      refine ⟨412433460764130162895506611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274955640509420108597004407 412433460764130162895506611)
      ·
        refine ⟨618650191146195244343259917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412433460764130162895506611 618650191146195244343259917)
        ·
          refine ⟨231993821679823216628722469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 618650191146195244343259917 231993821679823216628722469)
          ·
            refine ⟨43498841564966853117885463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 231993821679823216628722469 43498841564966853117885463)
            ·
              refine ⟨65248262347450279676828195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43498841564966853117885463 65248262347450279676828195)
              ·
                refine ⟨97872393521175419515242293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65248262347450279676828195 97872393521175419515242293)
                ·
                  refine ⟨9175536892610195579553965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97872393521175419515242293 9175536892610195579553965)
                  ·
                    refine ⟨3440826334728823342332737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9175536892610195579553965 3440826334728823342332737)
                    ·
                      refine ⟨2580619751046617506749553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3440826334728823342332737 2580619751046617506749553)
                      ·
                        rfl

theorem cell23_5025739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 3, 2].length) (baseStart_5025739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025739 prefixEnd_5025739 := by exact prefixLift 5025739
  have htrace : WordTrace (prefixWord ++ tailWord_5025739) baseStart_5025739 baseEnd_5025739 := by
    simpa [prefixWord, tailWord_5025739, baseEnd_5025739] using wordTrace_append hprefix tailTrace_5025739
  have hstable : (prefixWord ++ tailWord_5025739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025739).length < 2 ^ (prefixWord ++ tailWord_5025739).sum := by decide
  have hdescent : baseEnd_5025739 < baseStart_5025739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025752 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 2, 3, 4]
def baseStart_5025752 : Nat := 118140960795 + 5025752 * 2 ^ 59
def prefixEnd_5025752 : Nat := 4983230072969 + 3 ^ 40 * 5025752 * 2
def baseEnd_5025752 : Nat := 2580626426295125955886993

theorem tailTrace_5025752 : CollatzResearch.WordTrace tailWord_5025752 prefixEnd_5025752 2580626426295125955886993 := by
  unfold tailWord_5025752
  simp only [CollatzResearch.WordTrace]
  refine ⟨91652117244283154475779755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122202822992377539301039673 91652117244283154475779755)
  ·
    refine ⟨137478175866424731713669633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91652117244283154475779755 137478175866424731713669633)
    ·
      refine ⟨103108631899818548785252225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137478175866424731713669633 103108631899818548785252225)
      ·
        refine ⟨77331473924863911588939169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103108631899818548785252225 77331473924863911588939169)
        ·
          refine ⟨57998605443647933691704377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77331473924863911588939169 57998605443647933691704377)
          ·
            refine ⟨43498954082735950268778283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57998605443647933691704377 43498954082735950268778283)
            ·
              refine ⟨65248431124103925403167425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43498954082735950268778283 65248431124103925403167425)
              ·
                refine ⟨48936323343077944052375569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65248431124103925403167425 48936323343077944052375569)
                ·
                  refine ⟨36702242507308458039281677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48936323343077944052375569 36702242507308458039281677)
                  ·
                    refine ⟨13763340940240671764730629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36702242507308458039281677 13763340940240671764730629)
                    ·
                      refine ⟨2580626426295125955886993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13763340940240671764730629 2580626426295125955886993)
                      ·
                        rfl

theorem cell23_5025752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_5025752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025752 prefixEnd_5025752 := by exact prefixLift 5025752
  have htrace : WordTrace (prefixWord ++ tailWord_5025752) baseStart_5025752 baseEnd_5025752 := by
    simpa [prefixWord, tailWord_5025752, baseEnd_5025752] using wordTrace_append hprefix tailTrace_5025752
  have hstable : (prefixWord ++ tailWord_5025752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025752).length < 2 ^ (prefixWord ++ tailWord_5025752).sum := by decide
  have hdescent : baseEnd_5025752 < baseStart_5025752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025772 : List Nat := [2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 5]
def baseStart_5025772 : Nat := 118140960795 + 5025772 * 2 ^ 59
def prefixEnd_5025772 : Nat := 4983230072969 + 3 ^ 40 * 5025772 * 2
def baseEnd_5025772 : Nat := 2580636695908215877636901

theorem tailTrace_5025772 : CollatzResearch.WordTrace tailWord_5025772 prefixEnd_5025772 2580636695908215877636901 := by
  unfold tailWord_5025772
  simp only [CollatzResearch.WordTrace]
  refine ⟨91652481974246926183643785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122203309298995901578191713 91652481974246926183643785)
  ·
    refine ⟨68739361480685194637732839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91652481974246926183643785 68739361480685194637732839)
    ·
      refine ⟨103109042221027791956599259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68739361480685194637732839 103109042221027791956599259)
      ·
        refine ⟨154663563331541687934898889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103109042221027791956599259 154663563331541687934898889)
        ·
          refine ⟨115997672498656265951174167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154663563331541687934898889 115997672498656265951174167)
          ·
            refine ⟨173996508747984398926761251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115997672498656265951174167 173996508747984398926761251)
            ·
              refine ⟨260994763121976598390141877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173996508747984398926761251 260994763121976598390141877)
              ·
                refine ⟨24468259042685306099075801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 260994763121976598390141877 24468259042685306099075801)
                ·
                  refine ⟨18351194282013979574306851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24468259042685306099075801 18351194282013979574306851)
                  ·
                    refine ⟨27526791423020969361460277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18351194282013979574306851 27526791423020969361460277)
                    ·
                      refine ⟨2580636695908215877636901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27526791423020969361460277 2580636695908215877636901)
                      ·
                        rfl

theorem cell23_5025772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_5025772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025772 prefixEnd_5025772 := by exact prefixLift 5025772
  have htrace : WordTrace (prefixWord ++ tailWord_5025772) baseStart_5025772 baseEnd_5025772 := by
    simpa [prefixWord, tailWord_5025772, baseEnd_5025772] using wordTrace_append hprefix tailTrace_5025772
  have hstable : (prefixWord ++ tailWord_5025772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025772).length < 2 ^ (prefixWord ++ tailWord_5025772).sum := by decide
  have hdescent : baseEnd_5025772 < baseStart_5025772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025799 : List Nat := [1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 4]
def baseStart_5025799 : Nat := 118140960795 + 5025799 * 2 ^ 59
def prefixEnd_5025799 : Nat := 4983230072969 + 3 ^ 40 * 5025799 * 2
def baseEnd_5025799 : Nat := 2580650559885887271999277

theorem tailTrace_5025799 : CollatzResearch.WordTrace tailWord_5025799 prefixEnd_5025799 2580650559885887271999277 := by
  unfold tailWord_5025799
  simp only [CollatzResearch.WordTrace]
  refine ⟨183305948719396035978520451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122203965812930690652346967 183305948719396035978520451)
  ·
    refine ⟨274958923079094053967780677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183305948719396035978520451 274958923079094053967780677)
    ·
      refine ⟨51554798077330135118958877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 274958923079094053967780677 51554798077330135118958877)
      ·
        refine ⟨19333049278998800669609579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51554798077330135118958877 19333049278998800669609579)
        ·
          refine ⟨28999573918498201004414369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19333049278998800669609579 28999573918498201004414369)
          ·
            refine ⟨21749680438873650753310777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28999573918498201004414369 21749680438873650753310777)
            ·
              refine ⟨16312260329155238064983083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21749680438873650753310777 16312260329155238064983083)
              ·
                refine ⟨24468390493732857097474625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16312260329155238064983083 24468390493732857097474625)
                ·
                  refine ⟨18351292870299642823105969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24468390493732857097474625 18351292870299642823105969)
                  ·
                    refine ⟨13763469652724732117329477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18351292870299642823105969 13763469652724732117329477)
                    ·
                      refine ⟨2580650559885887271999277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13763469652724732117329477 2580650559885887271999277)
                      ·
                        rfl

theorem cell23_5025799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_5025799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025799 prefixEnd_5025799 := by exact prefixLift 5025799
  have htrace : WordTrace (prefixWord ++ tailWord_5025799) baseStart_5025799 baseEnd_5025799 := by
    simpa [prefixWord, tailWord_5025799, baseEnd_5025799] using wordTrace_append hprefix tailTrace_5025799
  have hstable : (prefixWord ++ tailWord_5025799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025799).length < 2 ^ (prefixWord ++ tailWord_5025799).sum := by decide
  have hdescent : baseEnd_5025799 < baseStart_5025799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025854 : List Nat := [4, 2, 1, 3, 2, 2, 2, 1, 2, 2, 2]
def baseStart_5025854 : Nat := 118140960795 + 5025854 * 2 ^ 59
def prefixEnd_5025854 : Nat := 4983230072969 + 3 ^ 40 * 5025854 * 2
def baseEnd_5025854 : Nat := 2580678801321884556811525

theorem tailTrace_5025854 : CollatzResearch.WordTrace tailWord_5025854 prefixEnd_5025854 2580678801321884556811525 := by
  unfold tailWord_5025854
  simp only [CollatzResearch.WordTrace]
  refine ⟨22913494341774597546471577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122205303156131186914515077 22913494341774597546471577)
  ·
    refine ⟨17185120756330948159853683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22913494341774597546471577 17185120756330948159853683)
    ·
      refine ⟨25777681134496422239780525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17185120756330948159853683 25777681134496422239780525)
      ·
        refine ⟨9666630425436158339917697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25777681134496422239780525 9666630425436158339917697)
        ·
          refine ⟨7249972819077118754938273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9666630425436158339917697 7249972819077118754938273)
          ·
            refine ⟨5437479614307839066203705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7249972819077118754938273 5437479614307839066203705)
            ·
              refine ⟨4078109710730879299652779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5437479614307839066203705 4078109710730879299652779)
              ·
                refine ⟨6117164566096318949479169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4078109710730879299652779 6117164566096318949479169)
                ·
                  refine ⟨4587873424572239212109377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6117164566096318949479169 4587873424572239212109377)
                  ·
                    refine ⟨3440905068429179409082033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4587873424572239212109377 3440905068429179409082033)
                    ·
                      refine ⟨2580678801321884556811525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3440905068429179409082033 2580678801321884556811525)
                      ·
                        rfl

theorem cell23_5025854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_5025854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025854 prefixEnd_5025854 := by exact prefixLift 5025854
  have htrace : WordTrace (prefixWord ++ tailWord_5025854) baseStart_5025854 baseEnd_5025854 := by
    simpa [prefixWord, tailWord_5025854, baseEnd_5025854] using wordTrace_append hprefix tailTrace_5025854
  have hstable : (prefixWord ++ tailWord_5025854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025854).length < 2 ^ (prefixWord ++ tailWord_5025854).sum := by decide
  have hdescent : baseEnd_5025854 < baseStart_5025854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025872 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 6]
def baseStart_5025872 : Nat := 118140960795 + 5025872 * 2 ^ 59
def prefixEnd_5025872 : Nat := 4983230072969 + 3 ^ 40 * 5025872 * 2
def baseEnd_5025872 : Nat := 2580688043973665486386441

theorem tailTrace_5025872 : CollatzResearch.WordTrace tailWord_5025872 prefixEnd_5025872 2580688043973665486386441 := by
  unfold tailWord_5025872
  simp only [CollatzResearch.WordTrace]
  refine ⟨91654305624065784722963935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122205740832087712963951913 91654305624065784722963935)
  ·
    refine ⟨137481458436098677084445903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91654305624065784722963935 137481458436098677084445903)
    ·
      refine ⟨206222187654148015626668855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137481458436098677084445903 206222187654148015626668855)
      ·
        refine ⟨309333281481222023440003283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206222187654148015626668855 309333281481222023440003283)
        ·
          refine ⟨463999922221833035160004925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309333281481222023440003283 463999922221833035160004925)
          ·
            refine ⟨173999970833187388185001847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 463999922221833035160004925 173999970833187388185001847)
            ·
              refine ⟨260999956249781082277502771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173999970833187388185001847 260999956249781082277502771)
              ·
                refine ⟨391499934374671623416254157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260999956249781082277502771 391499934374671623416254157)
                ·
                  refine ⟨146812475390501858781095309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 391499934374671623416254157 146812475390501858781095309)
                  ·
                    refine ⟨55054678271438197042910741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 146812475390501858781095309 55054678271438197042910741)
                    ·
                      refine ⟨2580688043973665486386441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55054678271438197042910741 2580688043973665486386441)
                      ·
                        rfl

theorem cell23_5025872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 6].length) (baseStart_5025872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025872 prefixEnd_5025872 := by exact prefixLift 5025872
  have htrace : WordTrace (prefixWord ++ tailWord_5025872) baseStart_5025872 baseEnd_5025872 := by
    simpa [prefixWord, tailWord_5025872, baseEnd_5025872] using wordTrace_append hprefix tailTrace_5025872
  have hstable : (prefixWord ++ tailWord_5025872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025872).length < 2 ^ (prefixWord ++ tailWord_5025872).sum := by decide
  have hdescent : baseEnd_5025872 < baseStart_5025872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025876 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 4, 4, 2]
def baseStart_5025876 : Nat := 118140960795 + 5025876 * 2 ^ 59
def prefixEnd_5025876 : Nat := 4983230072969 + 3 ^ 40 * 5025876 * 2
def baseEnd_5025876 : Nat := 2580690097896283470736423

theorem tailTrace_5025876 : CollatzResearch.WordTrace tailWord_5025876 prefixEnd_5025876 2580690097896283470736423 := by
  unfold tailWord_5025876
  simp only [CollatzResearch.WordTrace]
  refine ⟨91654378570058539064536741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122205838093411385419382321 91654378570058539064536741)
  ·
    refine ⟨17185195981885976074600639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91654378570058539064536741 17185195981885976074600639)
    ·
      refine ⟨25777793972828964111900959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17185195981885976074600639 25777793972828964111900959)
      ·
        refine ⟨38666690959243446167851439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25777793972828964111900959 38666690959243446167851439)
        ·
          refine ⟨58000036438865169251777159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38666690959243446167851439 58000036438865169251777159)
          ·
            refine ⟨87000054658297753877665739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58000036438865169251777159 87000054658297753877665739)
            ·
              refine ⟨130500081987446630816498609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87000054658297753877665739 130500081987446630816498609)
              ·
                refine ⟨97875061490584973112373957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130500081987446630816498609 97875061490584973112373957)
                ·
                  refine ⟨18351574029484682458570117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97875061490584973112373957 18351574029484682458570117)
                  ·
                    refine ⟨3440920130528377960981897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18351574029484682458570117 3440920130528377960981897)
                    ·
                      refine ⟨2580690097896283470736423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3440920130528377960981897 2580690097896283470736423)
                      ·
                        rfl

theorem cell23_5025876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_5025876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025876 prefixEnd_5025876 := by exact prefixLift 5025876
  have htrace : WordTrace (prefixWord ++ tailWord_5025876) baseStart_5025876 baseEnd_5025876 := by
    simpa [prefixWord, tailWord_5025876, baseEnd_5025876] using wordTrace_append hprefix tailTrace_5025876
  have hstable : (prefixWord ++ tailWord_5025876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025876).length < 2 ^ (prefixWord ++ tailWord_5025876).sum := by decide
  have hdescent : baseEnd_5025876 < baseStart_5025876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025879 : List Nat := [1, 1, 3, 2, 2, 1, 2, 3, 1, 4, 3]
def baseStart_5025879 : Nat := 118140960795 + 5025879 * 2 ^ 59
def prefixEnd_5025879 : Nat := 4983230072969 + 3 ^ 40 * 5025879 * 2
def baseEnd_5025879 : Nat := 2580691638338246958998909

theorem tailTrace_5025879 : CollatzResearch.WordTrace tailWord_5025879 prefixEnd_5025879 2580691638338246958998909 := by
  unfold tailWord_5025879
  simp only [CollatzResearch.WordTrace]
  refine ⟨183308866559106209641432691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122205911039404139760955127 183308866559106209641432691)
  ·
    refine ⟨274963299838659314462149037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183308866559106209641432691 274963299838659314462149037)
    ·
      refine ⟨103111237439497242923305889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 274963299838659314462149037 103111237439497242923305889)
      ·
        refine ⟨77333428079622932192479417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103111237439497242923305889 77333428079622932192479417)
        ·
          refine ⟨58000071059717199144359563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77333428079622932192479417 58000071059717199144359563)
          ·
            refine ⟨87000106589575798716539345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58000071059717199144359563 87000106589575798716539345)
            ·
              refine ⟨65250079942181849037404509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87000106589575798716539345 65250079942181849037404509)
              ·
                refine ⟨24468779978318193389026691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65250079942181849037404509 24468779978318193389026691)
                ·
                  refine ⟨36703169967477290083540037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24468779978318193389026691 36703169967477290083540037)
                  ·
                    refine ⟨6881844368901991890663757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36703169967477290083540037 6881844368901991890663757)
                    ·
                      refine ⟨2580691638338246958998909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6881844368901991890663757 2580691638338246958998909)
                      ·
                        rfl

theorem cell23_5025879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_5025879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025879 prefixEnd_5025879 := by exact prefixLift 5025879
  have htrace : WordTrace (prefixWord ++ tailWord_5025879) baseStart_5025879 baseEnd_5025879 := by
    simpa [prefixWord, tailWord_5025879, baseEnd_5025879] using wordTrace_append hprefix tailTrace_5025879
  have hstable : (prefixWord ++ tailWord_5025879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025879).length < 2 ^ (prefixWord ++ tailWord_5025879).sum := by decide
  have hdescent : baseEnd_5025879 < baseStart_5025879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025903 : List Nat := [1, 1, 2, 1, 3, 5, 1, 4, 1, 4]
def baseStart_5025903 : Nat := 118140960795 + 5025903 * 2 ^ 59
def prefixEnd_5025903 : Nat := 4983230072969 + 3 ^ 40 * 5025903 * 2
def baseEnd_5025903 : Nat := 860234653957984955032933

theorem tailTrace_5025903 : CollatzResearch.WordTrace tailWord_5025903 prefixEnd_5025903 860234653957984955032933 := by
  unfold tailWord_5025903
  simp only [CollatzResearch.WordTrace]
  refine ⟨183309741911019261740306363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122206494607346174493537575 183309741911019261740306363)
  ·
    refine ⟨274964612866528892610459545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183309741911019261740306363 274964612866528892610459545)
    ·
      refine ⟨206223459649896669457844659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274964612866528892610459545 206223459649896669457844659)
      ·
        refine ⟨309335189474845004186766989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206223459649896669457844659 309335189474845004186766989)
        ·
          refine ⟨116000696053066876570037621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 309335189474845004186766989 116000696053066876570037621)
          ·
            refine ⟨10875065254975019678441027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 116000696053066876570037621 10875065254975019678441027)
            ·
              refine ⟨16312597882462529517661541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10875065254975019678441027 16312597882462529517661541)
              ·
                refine ⟨3058612102961724284561539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16312597882462529517661541 3058612102961724284561539)
                ·
                  refine ⟨4587918154442586426842309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3058612102961724284561539 4587918154442586426842309)
                  ·
                    refine ⟨860234653957984955032933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4587918154442586426842309 860234653957984955032933)
                    ·
                      rfl

theorem cell23_5025903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 4, 1, 4].length) (baseStart_5025903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025903 prefixEnd_5025903 := by exact prefixLift 5025903
  have htrace : WordTrace (prefixWord ++ tailWord_5025903) baseStart_5025903 baseEnd_5025903 := by
    simpa [prefixWord, tailWord_5025903, baseEnd_5025903] using wordTrace_append hprefix tailTrace_5025903
  have hstable : (prefixWord ++ tailWord_5025903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025903).length < 2 ^ (prefixWord ++ tailWord_5025903).sum := by decide
  have hdescent : baseEnd_5025903 < baseStart_5025903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025929 : List Nat := [1, 2, 1, 1, 4, 2, 1, 3, 3, 5]
def baseStart_5025929 : Nat := 118140960795 + 5025929 * 2 ^ 59
def prefixEnd_5025929 : Nat := 4983230072969 + 3 ^ 40 * 5025929 * 2
def baseEnd_5025929 : Nat := 860239104123657254457893

theorem tailTrace_5025929 : CollatzResearch.WordTrace tailWord_5025929 prefixEnd_5025929 860239104123657254457893 := by
  unfold tailWord_5025929
  simp only [CollatzResearch.WordTrace]
  refine ⟨183310690208925068180752841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122207126805950045453835227 183310690208925068180752841)
  ·
    refine ⟨137483017656693801135564631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183310690208925068180752841 137483017656693801135564631)
    ·
      refine ⟨206224526485040701703346947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137483017656693801135564631 206224526485040701703346947)
      ·
        refine ⟨309336789727561052555020421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206224526485040701703346947 309336789727561052555020421)
        ·
          refine ⟨58000648073917697354066329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 309336789727561052555020421 58000648073917697354066329)
          ·
            refine ⟨43500486055438273015549747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58000648073917697354066329 43500486055438273015549747)
            ·
              refine ⟨65250729083157409523324621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43500486055438273015549747 65250729083157409523324621)
              ·
                refine ⟨24469023406184028571246733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65250729083157409523324621 24469023406184028571246733)
                ·
                  refine ⟨9175883777319010714217525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24469023406184028571246733 9175883777319010714217525)
                  ·
                    refine ⟨860239104123657254457893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9175883777319010714217525 860239104123657254457893)
                    ·
                      rfl

theorem cell23_5025929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 5].length) (baseStart_5025929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025929 prefixEnd_5025929 := by exact prefixLift 5025929
  have htrace : WordTrace (prefixWord ++ tailWord_5025929) baseStart_5025929 baseEnd_5025929 := by
    simpa [prefixWord, tailWord_5025929, baseEnd_5025929] using wordTrace_append hprefix tailTrace_5025929
  have hstable : (prefixWord ++ tailWord_5025929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025929).length < 2 ^ (prefixWord ++ tailWord_5025929).sum := by decide
  have hdescent : baseEnd_5025929 < baseStart_5025929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025936 : List Nat := [2, 1, 1, 1, 1, 1, 7, 1, 1, 5, 2]
def baseStart_5025936 : Nat := 118140960795 + 5025936 * 2 ^ 59
def prefixEnd_5025936 : Nat := 4983230072969 + 3 ^ 40 * 5025936 * 2
def baseEnd_5025936 : Nat := 2580720906735553235986147

theorem tailTrace_5025936 : CollatzResearch.WordTrace tailWord_5025936 prefixEnd_5025936 2580720906735553235986147 := by
  unfold tailWord_5025936
  simp only [CollatzResearch.WordTrace]
  refine ⟨91655472759949854188128831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122207297013266472250838441 91655472759949854188128831)
  ·
    refine ⟨137483209139924781282193247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91655472759949854188128831 137483209139924781282193247)
    ·
      refine ⟨206224813709887171923289871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137483209139924781282193247 206224813709887171923289871)
      ·
        refine ⟨309337220564830757884934807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206224813709887171923289871 309337220564830757884934807)
        ·
          refine ⟨464005830847246136827402211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309337220564830757884934807 464005830847246136827402211)
          ·
            refine ⟨696008746270869205241103317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464005830847246136827402211 696008746270869205241103317)
            ·
              refine ⟨16312704990723496997838359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 696008746270869205241103317 16312704990723496997838359)
              ·
                refine ⟨24469057486085245496757539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16312704990723496997838359 24469057486085245496757539)
                ·
                  refine ⟨36703586229127868245136309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24469057486085245496757539 36703586229127868245136309)
                  ·
                    refine ⟨3440961208980737647981529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36703586229127868245136309 3440961208980737647981529)
                    ·
                      refine ⟨2580720906735553235986147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3440961208980737647981529 2580720906735553235986147)
                      ·
                        rfl

theorem cell23_5025936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 1, 5, 2].length) (baseStart_5025936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025936 prefixEnd_5025936 := by exact prefixLift 5025936
  have htrace : WordTrace (prefixWord ++ tailWord_5025936) baseStart_5025936 baseEnd_5025936 := by
    simpa [prefixWord, tailWord_5025936, baseEnd_5025936] using wordTrace_append hprefix tailTrace_5025936
  have hstable : (prefixWord ++ tailWord_5025936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025936).length < 2 ^ (prefixWord ++ tailWord_5025936).sum := by decide
  have hdescent : baseEnd_5025936 < baseStart_5025936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025950 : List Nat := [4, 3, 1, 1, 3, 2, 1, 2, 6]
def baseStart_5025950 : Nat := 118140960795 + 5025950 * 2 ^ 59
def prefixEnd_5025950 : Nat := 4983230072969 + 3 ^ 40 * 5025950 * 2
def baseEnd_5025950 : Nat := 286747566162746242356787

theorem tailTrace_5025950 : CollatzResearch.WordTrace tailWord_5025950 prefixEnd_5025950 286747566162746242356787 := by
  unfold tailWord_5025950
  simp only [CollatzResearch.WordTrace]
  refine ⟨22913932017731123595908413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122207637427899325844844869 22913932017731123595908413)
  ·
    refine ⟨8592724506649171348465655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22913932017731123595908413 8592724506649171348465655)
    ·
      refine ⟨12889086759973757022698483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8592724506649171348465655 12889086759973757022698483)
      ·
        refine ⟨19333630139960635534047725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12889086759973757022698483 19333630139960635534047725)
        ·
          refine ⟨7250111302485238325267897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19333630139960635534047725 7250111302485238325267897)
          ·
            refine ⟨5437583476863928743950923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7250111302485238325267897 5437583476863928743950923)
            ·
              refine ⟨8156375215295893115926385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5437583476863928743950923 8156375215295893115926385)
              ·
                refine ⟨6117281411471919836944789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8156375215295893115926385 6117281411471919836944789)
                ·
                  refine ⟨286747566162746242356787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6117281411471919836944789 286747566162746242356787)
                  ·
                    rfl

theorem cell23_5025950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_5025950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025950 prefixEnd_5025950 := by exact prefixLift 5025950
  have htrace : WordTrace (prefixWord ++ tailWord_5025950) baseStart_5025950 baseEnd_5025950 := by
    simpa [prefixWord, tailWord_5025950, baseEnd_5025950] using wordTrace_append hprefix tailTrace_5025950
  have hstable : (prefixWord ++ tailWord_5025950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025950).length < 2 ^ (prefixWord ++ tailWord_5025950).sum := by decide
  have hdescent : baseEnd_5025950 < baseStart_5025950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5025979 : List Nat := [1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 6]
def baseStart_5025979 : Nat := 118140960795 + 5025979 * 2 ^ 59
def prefixEnd_5025979 : Nat := 4983230072969 + 3 ^ 40 * 5025979 * 2
def baseEnd_5025979 : Nat := 2580742986403696567748449

theorem tailTrace_5025979 : CollatzResearch.WordTrace tailWord_5025979 prefixEnd_5025979 2580742986403696567748449 := by
  unfold tailWord_5025979
  simp only [CollatzResearch.WordTrace]
  refine ⟨183312513858743926720072991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122208342572495951146715327 183312513858743926720072991)
  ·
    refine ⟨274968770788115890080109487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183312513858743926720072991 274968770788115890080109487)
    ·
      refine ⟨412453156182173835120164231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274968770788115890080109487 412453156182173835120164231)
      ·
        refine ⟨618679734273260752680246347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412453156182173835120164231 618679734273260752680246347)
        ·
          refine ⟨928019601409891129020369521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 618679734273260752680246347 928019601409891129020369521)
          ·
            refine ⟨696014701057418346765277141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 928019601409891129020369521 696014701057418346765277141)
            ·
              refine ⟨16312844556033242502311183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 696014701057418346765277141 16312844556033242502311183)
              ·
                refine ⟨24469266834049863753466775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16312844556033242502311183 24469266834049863753466775)
                ·
                  refine ⟨36703900251074795630200163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24469266834049863753466775 36703900251074795630200163)
                  ·
                    refine ⟨55055850376612193445300245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36703900251074795630200163 55055850376612193445300245)
                    ·
                      refine ⟨2580742986403696567748449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55055850376612193445300245 2580742986403696567748449)
                      ·
                        rfl

theorem cell23_5025979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 6].length) (baseStart_5025979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5025979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5025979 prefixEnd_5025979 := by exact prefixLift 5025979
  have htrace : WordTrace (prefixWord ++ tailWord_5025979) baseStart_5025979 baseEnd_5025979 := by
    simpa [prefixWord, tailWord_5025979, baseEnd_5025979] using wordTrace_append hprefix tailTrace_5025979
  have hstable : (prefixWord ++ tailWord_5025979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5025979).length < 2 ^ (prefixWord ++ tailWord_5025979).sum := by decide
  have hdescent : baseEnd_5025979 < baseStart_5025979 := by decide
  rcases family_descends (prefixWord ++ tailWord_5025979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026050 : List Nat := [3, 4, 1, 1, 2, 2, 1, 2, 1, 3, 3]
def baseStart_5026050 : Nat := 118140960795 + 5026050 * 2 ^ 59
def prefixEnd_5026050 : Nat := 4983230072969 + 3 ^ 40 * 5026050 * 2
def baseEnd_5026050 : Nat := 2580779443530165789960623

theorem tailTrace_5026050 : CollatzResearch.WordTrace tailWord_5026050 prefixEnd_5026050 2580779443530165789960623 := by
  unfold tailWord_5026050
  simp only [CollatzResearch.WordTrace]
  refine ⟨45828775860371676461476901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122210068960991137230605069 45828775860371676461476901)
  ·
    refine ⟨8592895473819689336526919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45828775860371676461476901 8592895473819689336526919)
    ·
      refine ⟨12889343210729534004790379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8592895473819689336526919 12889343210729534004790379)
      ·
        refine ⟨19334014816094301007185569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12889343210729534004790379 19334014816094301007185569)
        ·
          refine ⟨14500511112070725755389177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19334014816094301007185569 14500511112070725755389177)
          ·
            refine ⟨10875383334053044316541883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14500511112070725755389177 10875383334053044316541883)
            ·
              refine ⟨16313075001079566474812825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10875383334053044316541883 16313075001079566474812825)
              ·
                refine ⟨12234806250809674856109619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16313075001079566474812825 12234806250809674856109619)
                ·
                  refine ⟨18352209376214512284164429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12234806250809674856109619 18352209376214512284164429)
                  ·
                    refine ⟨6882078516080442106561661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18352209376214512284164429 6882078516080442106561661)
                    ·
                      refine ⟨2580779443530165789960623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6882078516080442106561661 2580779443530165789960623)
                      ·
                        rfl

theorem cell23_5026050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_5026050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026050 prefixEnd_5026050 := by exact prefixLift 5026050
  have htrace : WordTrace (prefixWord ++ tailWord_5026050) baseStart_5026050 baseEnd_5026050 := by
    simpa [prefixWord, tailWord_5026050, baseEnd_5026050] using wordTrace_append hprefix tailTrace_5026050
  have hstable : (prefixWord ++ tailWord_5026050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026050).length < 2 ^ (prefixWord ++ tailWord_5026050).sum := by decide
  have hdescent : baseEnd_5026050 < baseStart_5026050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026263 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 8, 4]
def baseStart_5026263 : Nat := 118140960795 + 5026263 * 2 ^ 59
def prefixEnd_5026263 : Nat := 4983230072969 + 3 ^ 40 * 5026263 * 2
def baseEnd_5026263 : Nat := 860296271636524485532381

theorem tailTrace_5026263 : CollatzResearch.WordTrace tailWord_5026263 prefixEnd_5026263 860296271636524485532381 := by
  unfold tailWord_5026263
  simp only [CollatzResearch.WordTrace]
  refine ⟨183322872189715043223411443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122215248126476695482274295 183322872189715043223411443)
  ·
    refine ⟨274984308284572564835117165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183322872189715043223411443 274984308284572564835117165)
    ·
      refine ⟨103119115606714711813168937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 274984308284572564835117165 103119115606714711813168937)
      ·
        refine ⟨77339336705036033859876703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103119115606714711813168937 77339336705036033859876703)
        ·
          refine ⟨116009005057554050789815055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77339336705036033859876703 116009005057554050789815055)
          ·
            refine ⟨174013507586331076184722583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116009005057554050789815055 174013507586331076184722583)
            ·
              refine ⟨261020261379496614277083875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174013507586331076184722583 261020261379496614277083875)
              ·
                refine ⟨391530392069244921415625813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261020261379496614277083875 391530392069244921415625813)
                ·
                  refine ⟨4588246782061463922839365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 391530392069244921415625813 4588246782061463922839365)
                  ·
                    refine ⟨860296271636524485532381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4588246782061463922839365 860296271636524485532381)
                    ·
                      rfl

theorem cell23_5026263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 8, 4].length) (baseStart_5026263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026263 prefixEnd_5026263 := by exact prefixLift 5026263
  have htrace : WordTrace (prefixWord ++ tailWord_5026263) baseStart_5026263 baseEnd_5026263 := by
    simpa [prefixWord, tailWord_5026263, baseEnd_5026263] using wordTrace_append hprefix tailTrace_5026263
  have hstable : (prefixWord ++ tailWord_5026263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026263).length < 2 ^ (prefixWord ++ tailWord_5026263).sum := by decide
  have hdescent : baseEnd_5026263 < baseStart_5026263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026283 : List Nat := [1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 4]
def baseStart_5026283 : Nat := 118140960795 + 5026283 * 2 ^ 59
def prefixEnd_5026283 : Nat := 4983230072969 + 3 ^ 40 * 5026283 * 2
def baseEnd_5026283 : Nat := 2580899084522663378347051

theorem tailTrace_5026283 : CollatzResearch.WordTrace tailWord_5026283 prefixEnd_5026283 2580899084522663378347051 := by
  unfold tailWord_5026283
  simp only [CollatzResearch.WordTrace]
  refine ⟨183323601649642586639139503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122215734433095057759426335 183323601649642586639139503)
  ·
    refine ⟨274985402474463879958709255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183323601649642586639139503 274985402474463879958709255)
    ·
      refine ⟨412478103711695819938063883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274985402474463879958709255 412478103711695819938063883)
      ·
        refine ⟨618717155567543729907095825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412478103711695819938063883 618717155567543729907095825)
        ·
          refine ⟨464037866675657797430321869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 618717155567543729907095825 464037866675657797430321869)
          ·
            refine ⟨174014200003371674036370701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 464037866675657797430321869 174014200003371674036370701)
            ·
              refine ⟨65255325001264377763639013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174014200003371674036370701 65255325001264377763639013)
              ·
                refine ⟨12235373437737070830682315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65255325001264377763639013 12235373437737070830682315)
                ·
                  refine ⟨18353060156605606246023473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12235373437737070830682315 18353060156605606246023473)
                  ·
                    refine ⟨13764795117454204684517605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18353060156605606246023473 13764795117454204684517605)
                    ·
                      refine ⟨2580899084522663378347051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13764795117454204684517605 2580899084522663378347051)
                      ·
                        rfl

theorem cell23_5026283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 4].length) (baseStart_5026283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026283 prefixEnd_5026283 := by exact prefixLift 5026283
  have htrace : WordTrace (prefixWord ++ tailWord_5026283) baseStart_5026283 baseEnd_5026283 := by
    simpa [prefixWord, tailWord_5026283, baseEnd_5026283] using wordTrace_append hprefix tailTrace_5026283
  have hstable : (prefixWord ++ tailWord_5026283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026283).length < 2 ^ (prefixWord ++ tailWord_5026283).sum := by decide
  have hdescent : baseEnd_5026283 < baseStart_5026283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026324 : List Nat := [2, 4, 3, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_5026324 : Nat := 118140960795 + 5026324 * 2 ^ 59
def prefixEnd_5026324 : Nat := 4983230072969 + 3 ^ 40 * 5026324 * 2
def baseEnd_5026324 : Nat := 2580920137229497717934363

theorem tailTrace_5026324 : CollatzResearch.WordTrace tailWord_5026324 prefixEnd_5026324 2580920137229497717934363 := by
  unfold tailWord_5026324
  simp only [CollatzResearch.WordTrace]
  refine ⟨91662548521247025320691013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122216731361662700427588017 91662548521247025320691013)
  ·
    refine ⟨17186727847733817247629565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91662548521247025320691013 17186727847733817247629565)
    ·
      refine ⟨6445022942900181467861087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17186727847733817247629565 6445022942900181467861087)
      ·
        refine ⟨9667534414350272201791631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6445022942900181467861087 9667534414350272201791631)
        ·
          refine ⟨14501301621525408302687447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9667534414350272201791631 14501301621525408302687447)
          ·
            refine ⟨21751952432288112454031171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14501301621525408302687447 21751952432288112454031171)
            ·
              refine ⟨32627928648432168681046757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21751952432288112454031171 32627928648432168681046757)
              ·
                refine ⟨6117736621581031627696267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32627928648432168681046757 6117736621581031627696267)
                ·
                  refine ⟨9176604932371547441544401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6117736621581031627696267 9176604932371547441544401)
                  ·
                    refine ⟨6882453699278660581158301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9176604932371547441544401 6882453699278660581158301)
                    ·
                      refine ⟨2580920137229497717934363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6882453699278660581158301 2580920137229497717934363)
                      ·
                        rfl

theorem cell23_5026324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_5026324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026324 prefixEnd_5026324 := by exact prefixLift 5026324
  have htrace : WordTrace (prefixWord ++ tailWord_5026324) baseStart_5026324 baseEnd_5026324 := by
    simpa [prefixWord, tailWord_5026324, baseEnd_5026324] using wordTrace_append hprefix tailTrace_5026324
  have hstable : (prefixWord ++ tailWord_5026324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026324).length < 2 ^ (prefixWord ++ tailWord_5026324).sum := by decide
  have hdescent : baseEnd_5026324 < baseStart_5026324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026353 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 4, 6]
def baseStart_5026353 : Nat := 118140960795 + 5026353 * 2 ^ 59
def prefixEnd_5026353 : Nat := 4983230072969 + 3 ^ 40 * 5026353 * 2
def baseEnd_5026353 : Nat := 860311676056159368157243

theorem tailTrace_5026353 : CollatzResearch.WordTrace tailWord_5026353 prefixEnd_5026353 860311676056159368157243 := by
  unfold tailWord_5026353
  simp only [CollatzResearch.WordTrace]
  refine ⟨183326154759388988594187713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122217436506259325729458475 183326154759388988594187713)
  ·
    refine ⟨137494616069541741445640785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183326154759388988594187713 137494616069541741445640785)
    ·
      refine ⟨103120962052156306084230589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137494616069541741445640785 103120962052156306084230589)
      ·
        refine ⟨38670360769558614781586471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103120962052156306084230589 38670360769558614781586471)
        ·
          refine ⟨58005541154337922172379707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38670360769558614781586471 58005541154337922172379707)
          ·
            refine ⟨87008311731506883258569561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58005541154337922172379707 87008311731506883258569561)
            ·
              refine ⟨65256233798630162443927171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87008311731506883258569561 65256233798630162443927171)
              ·
                refine ⟨97884350697945243665890757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65256233798630162443927171 97884350697945243665890757)
                ·
                  refine ⟨18353315755864733187354517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97884350697945243665890757 18353315755864733187354517)
                  ·
                    refine ⟨860311676056159368157243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18353315755864733187354517 860311676056159368157243)
                    ·
                      rfl

theorem cell23_5026353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 6].length) (baseStart_5026353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026353 prefixEnd_5026353 := by exact prefixLift 5026353
  have htrace : WordTrace (prefixWord ++ tailWord_5026353) baseStart_5026353 baseEnd_5026353 := by
    simpa [prefixWord, tailWord_5026353, baseEnd_5026353] using wordTrace_append hprefix tailTrace_5026353
  have hstable : (prefixWord ++ tailWord_5026353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026353).length < 2 ^ (prefixWord ++ tailWord_5026353).sum := by decide
  have hdescent : baseEnd_5026353 < baseStart_5026353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026381 : List Nat := [1, 6, 1, 1, 2, 1, 3, 2, 1, 3, 2]
def baseStart_5026381 : Nat := 118140960795 + 5026381 * 2 ^ 59
def prefixEnd_5026381 : Nat := 4983230072969 + 3 ^ 40 * 5026381 * 2
def baseEnd_5026381 : Nat := 2580949405626803994921601

theorem tailTrace_5026381 : CollatzResearch.WordTrace tailWord_5026381 prefixEnd_5026381 2580949405626803994921601 := by
  unfold tailWord_5026381
  simp only [CollatzResearch.WordTrace]
  refine ⟨183327176003287549376206997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122218117335525032917471331 183327176003287549376206997)
  ·
    refine ⟨8593461375154103877009703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 183327176003287549376206997 8593461375154103877009703)
    ·
      refine ⟨12890192062731155815514555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8593461375154103877009703 12890192062731155815514555)
      ·
        refine ⟨19335288094096733723271833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12890192062731155815514555 19335288094096733723271833)
        ·
          refine ⟨14501466070572550292453875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19335288094096733723271833 14501466070572550292453875)
          ·
            refine ⟨21752199105858825438680813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14501466070572550292453875 21752199105858825438680813)
            ·
              refine ⟨8157074664697059539505305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21752199105858825438680813 8157074664697059539505305)
              ·
                refine ⟨6117805998522794654628979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8157074664697059539505305 6117805998522794654628979)
                ·
                  refine ⟨9176708997784191981943469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6117805998522794654628979 9176708997784191981943469)
                  ·
                    refine ⟨3441265874169071993228801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9176708997784191981943469 3441265874169071993228801)
                    ·
                      refine ⟨2580949405626803994921601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3441265874169071993228801 2580949405626803994921601)
                      ·
                        rfl

theorem cell23_5026381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_5026381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026381 prefixEnd_5026381 := by exact prefixLift 5026381
  have htrace : WordTrace (prefixWord ++ tailWord_5026381) baseStart_5026381 baseEnd_5026381 := by
    simpa [prefixWord, tailWord_5026381, baseEnd_5026381] using wordTrace_append hprefix tailTrace_5026381
  have hstable : (prefixWord ++ tailWord_5026381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026381).length < 2 ^ (prefixWord ++ tailWord_5026381).sum := by decide
  have hdescent : baseEnd_5026381 < baseStart_5026381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026383 : List Nat := [1, 1, 2, 1, 1, 2, 4, 4, 7]
def baseStart_5026383 : Nat := 118140960795 + 5026383 * 2 ^ 59
def prefixEnd_5026383 : Nat := 4983230072969 + 3 ^ 40 * 5026383 * 2
def baseEnd_5026383 : Nat := 286772270287568109677399

theorem tailTrace_5026383 : CollatzResearch.WordTrace tailWord_5026383 prefixEnd_5026383 286772270287568109677399 := by
  unfold tailWord_5026383
  simp only [CollatzResearch.WordTrace]
  refine ⟨183327248949280303717779803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122218165966186869145186535 183327248949280303717779803)
  ·
    refine ⟨274990873423920455576669705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183327248949280303717779803 274990873423920455576669705)
    ·
      refine ⟨206243155067940341682502279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274990873423920455576669705 206243155067940341682502279)
      ·
        refine ⟨309364732601910512523753419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206243155067940341682502279 309364732601910512523753419)
        ·
          refine ⟨464047098902865768785630129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309364732601910512523753419 464047098902865768785630129)
          ·
            refine ⟨348035324177149326589222597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 464047098902865768785630129 348035324177149326589222597)
            ·
              refine ⟨65256623283215498735479237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 348035324177149326589222597 65256623283215498735479237)
              ·
                refine ⟨12235616865602906012902357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65256623283215498735479237 12235616865602906012902357)
                ·
                  refine ⟨286772270287568109677399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12235616865602906012902357 286772270287568109677399)
                  ·
                    rfl

theorem cell23_5026383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 7].length) (baseStart_5026383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026383 prefixEnd_5026383 := by exact prefixLift 5026383
  have htrace : WordTrace (prefixWord ++ tailWord_5026383) baseStart_5026383 baseEnd_5026383 := by
    simpa [prefixWord, tailWord_5026383, baseEnd_5026383] using wordTrace_append hprefix tailTrace_5026383
  have hstable : (prefixWord ++ tailWord_5026383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026383).length < 2 ^ (prefixWord ++ tailWord_5026383).sum := by decide
  have hdescent : baseEnd_5026383 < baseStart_5026383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026443 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 1, 10]
def baseStart_5026443 : Nat := 118140960795 + 5026443 * 2 ^ 59
def prefixEnd_5026443 : Nat := 4983230072969 + 3 ^ 40 * 5026443 * 2
def baseEnd_5026443 : Nat := 860327080475794250782105

theorem tailTrace_5026443 : CollatzResearch.WordTrace tailWord_5026443 prefixEnd_5026443 860327080475794250782105 := by
  unfold tailWord_5026443
  simp only [CollatzResearch.WordTrace]
  refine ⟨183329437329062933964963983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122219624886041955976642655 183329437329062933964963983)
  ·
    refine ⟨274994155993594400947445975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183329437329062933964963983 274994155993594400947445975)
    ·
      refine ⟨412491233990391601421168963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274994155993594400947445975 412491233990391601421168963)
      ·
        refine ⟨618736850985587402131753445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412491233990391601421168963 618736850985587402131753445)
        ·
          refine ⟨116013159559797637899703771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 618736850985587402131753445 116013159559797637899703771)
          ·
            refine ⟨174019739339696456849555657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116013159559797637899703771 174019739339696456849555657)
            ·
              refine ⟨130514804504772342637166743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174019739339696456849555657 130514804504772342637166743)
              ·
                refine ⟨195772206757158513955750115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130514804504772342637166743 195772206757158513955750115)
                ·
                  refine ⟨293658310135737770933625173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 195772206757158513955750115 293658310135737770933625173)
                  ·
                    refine ⟨860327080475794250782105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 293658310135737770933625173 860327080475794250782105)
                    ·
                      rfl

theorem cell23_5026443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 10].length) (baseStart_5026443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026443 prefixEnd_5026443 := by exact prefixLift 5026443
  have htrace : WordTrace (prefixWord ++ tailWord_5026443) baseStart_5026443 baseEnd_5026443 := by
    simpa [prefixWord, tailWord_5026443, baseEnd_5026443] using wordTrace_append hprefix tailTrace_5026443
  have hstable : (prefixWord ++ tailWord_5026443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026443).length < 2 ^ (prefixWord ++ tailWord_5026443).sum := by decide
  have hdescent : baseEnd_5026443 < baseStart_5026443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026540 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 4]
def baseStart_5026540 : Nat := 118140960795 + 5026540 * 2 ^ 59
def prefixEnd_5026540 : Nat := 4983230072969 + 3 ^ 40 * 5026540 * 2
def baseEnd_5026540 : Nat := 2581031049050868872833369

theorem tailTrace_5026540 : CollatzResearch.WordTrace tailWord_5026540 prefixEnd_5026540 2581031049050868872833369 := by
  unfold tailWord_5026540
  simp only [CollatzResearch.WordTrace]
  refine ⟨91666487604855759765622537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122221983473141013020830049 91666487604855759765622537)
  ·
    refine ⟨68749865703641819824216903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91666487604855759765622537 68749865703641819824216903)
    ·
      refine ⟨103124798555462729736325355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68749865703641819824216903 103124798555462729736325355)
      ·
        refine ⟨154687197833194094604488033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103124798555462729736325355 154687197833194094604488033)
        ·
          refine ⟨116015398374895570953366025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154687197833194094604488033 116015398374895570953366025)
          ·
            refine ⟨87011548781171678215024519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116015398374895570953366025 87011548781171678215024519)
            ·
              refine ⟨130517323171757517322536779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87011548781171678215024519 130517323171757517322536779)
              ·
                refine ⟨195775984757636275983805169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130517323171757517322536779 195775984757636275983805169)
                ·
                  refine ⟨146831988568227206987853877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195775984757636275983805169 146831988568227206987853877)
                  ·
                    refine ⟨13765498928271300655111301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 146831988568227206987853877 13765498928271300655111301)
                    ·
                      refine ⟨2581031049050868872833369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13765498928271300655111301 2581031049050868872833369)
                      ·
                        rfl

theorem cell23_5026540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_5026540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026540 prefixEnd_5026540 := by exact prefixLift 5026540
  have htrace : WordTrace (prefixWord ++ tailWord_5026540) baseStart_5026540 baseEnd_5026540 := by
    simpa [prefixWord, tailWord_5026540, baseEnd_5026540] using wordTrace_append hprefix tailTrace_5026540
  have hstable : (prefixWord ++ tailWord_5026540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026540).length < 2 ^ (prefixWord ++ tailWord_5026540).sum := by decide
  have hdescent : baseEnd_5026540 < baseStart_5026540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026557 : List Nat := [1, 4, 1, 1, 1, 1, 5, 1, 3, 1, 4]
def baseStart_5026557 : Nat := 118140960795 + 5026557 * 2 ^ 59
def prefixEnd_5026557 : Nat := 4983230072969 + 3 ^ 40 * 5026557 * 2
def baseEnd_5026557 : Nat := 2581039778221995306320791

theorem tailTrace_5026557 : CollatzResearch.WordTrace tailWord_5026557 prefixEnd_5026557 2581039778221995306320791 := by
  unfold tailWord_5026557
  simp only [CollatzResearch.WordTrace]
  refine ⟨183333595250649931434613925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122222396833766620956409283 183333595250649931434613925)
  ·
    refine ⟨34375049109496862143990111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183333595250649931434613925 34375049109496862143990111)
    ·
      refine ⟨51562573664245293215985167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34375049109496862143990111 51562573664245293215985167)
      ·
        refine ⟨77343860496367939823977751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51562573664245293215985167 77343860496367939823977751)
        ·
          refine ⟨116015790744551909735966627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77343860496367939823977751 116015790744551909735966627)
          ·
            refine ⟨174023686116827864603949941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116015790744551909735966627 174023686116827864603949941)
            ·
              refine ⟨16314720573452612306620307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 174023686116827864603949941 16314720573452612306620307)
              ·
                refine ⟨24472080860178918459930461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16314720573452612306620307 24472080860178918459930461)
                ·
                  refine ⟨9177030322567094422473923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24472080860178918459930461 9177030322567094422473923)
                  ·
                    refine ⟨13765545483850641633710885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9177030322567094422473923 13765545483850641633710885)
                    ·
                      refine ⟨2581039778221995306320791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13765545483850641633710885 2581039778221995306320791)
                      ·
                        rfl

theorem cell23_5026557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_5026557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026557 prefixEnd_5026557 := by exact prefixLift 5026557
  have htrace : WordTrace (prefixWord ++ tailWord_5026557) baseStart_5026557 baseEnd_5026557 := by
    simpa [prefixWord, tailWord_5026557, baseEnd_5026557] using wordTrace_append hprefix tailTrace_5026557
  have hstable : (prefixWord ++ tailWord_5026557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026557).length < 2 ^ (prefixWord ++ tailWord_5026557).sum := by decide
  have hdescent : baseEnd_5026557 < baseStart_5026557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026567 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 3, 6]
def baseStart_5026567 : Nat := 118140960795 + 5026567 * 2 ^ 59
def prefixEnd_5026567 : Nat := 4983230072969 + 3 ^ 40 * 5026567 * 2
def baseEnd_5026567 : Nat := 860348304342846755731915

theorem tailTrace_5026567 : CollatzResearch.WordTrace tailWord_5026567 prefixEnd_5026567 860348304342846755731915 := by
  unfold tailWord_5026567
  simp only [CollatzResearch.WordTrace]
  refine ⟨183333959980613703142477955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122222639987075802094985303 183333959980613703142477955)
  ·
    refine ⟨275000939970920554713716933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183333959980613703142477955 275000939970920554713716933)
    ·
      refine ⟨51562676244547604008821925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 275000939970920554713716933 51562676244547604008821925)
      ·
        refine ⟨9668001795852675751654111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51562676244547604008821925 9668001795852675751654111)
        ·
          refine ⟨14502002693779013627481167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9668001795852675751654111 14502002693779013627481167)
          ·
            refine ⟨21753004040668520441221751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14502002693779013627481167 21753004040668520441221751)
            ·
              refine ⟨32629506061002780661832627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21753004040668520441221751 32629506061002780661832627)
              ·
                refine ⟨48944259091504170992748941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32629506061002780661832627 48944259091504170992748941)
                ·
                  refine ⟨18354097159314064122280853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48944259091504170992748941 18354097159314064122280853)
                  ·
                    refine ⟨860348304342846755731915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18354097159314064122280853 860348304342846755731915)
                    ·
                      rfl

theorem cell23_5026567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_5026567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026567 prefixEnd_5026567 := by exact prefixLift 5026567
  have htrace : WordTrace (prefixWord ++ tailWord_5026567) baseStart_5026567 baseEnd_5026567 := by
    simpa [prefixWord, tailWord_5026567, baseEnd_5026567] using wordTrace_append hprefix tailTrace_5026567
  have hstable : (prefixWord ++ tailWord_5026567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026567).length < 2 ^ (prefixWord ++ tailWord_5026567).sum := by decide
  have hdescent : baseEnd_5026567 < baseStart_5026567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026577 : List Nat := [1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 5]
def baseStart_5026577 : Nat := 118140960795 + 5026577 * 2 ^ 59
def prefixEnd_5026577 : Nat := 4983230072969 + 3 ^ 40 * 5026577 * 2
def baseEnd_5026577 : Nat := 2581050047835085228070699

theorem tailTrace_5026577 : CollatzResearch.WordTrace tailWord_5026577 prefixEnd_5026577 2581050047835085228070699 := by
  unfold tailWord_5026577
  simp only [CollatzResearch.WordTrace]
  refine ⟨183334324710577474850341985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122222883140384983233561323 183334324710577474850341985)
  ·
    refine ⟨137500743532933106137756489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183334324710577474850341985 137500743532933106137756489)
    ·
      refine ⟨103125557649699829603317367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137500743532933106137756489 103125557649699829603317367)
      ·
        refine ⟨154688336474549744404976051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103125557649699829603317367 154688336474549744404976051)
        ·
          refine ⟨232032504711824616607464077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154688336474549744404976051 232032504711824616607464077)
          ·
            refine ⟨87012189266934231227799029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232032504711824616607464077 87012189266934231227799029)
            ·
              refine ⟨8157392743775084177606159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 87012189266934231227799029 8157392743775084177606159)
              ·
                refine ⟨12236089115662626266409239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8157392743775084177606159 12236089115662626266409239)
                ·
                  refine ⟨18354133673493939399613859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12236089115662626266409239 18354133673493939399613859)
                  ·
                    refine ⟨27531200510240909099420789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18354133673493939399613859 27531200510240909099420789)
                    ·
                      refine ⟨2581050047835085228070699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27531200510240909099420789 2581050047835085228070699)
                      ·
                        rfl

theorem cell23_5026577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 5].length) (baseStart_5026577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026577 prefixEnd_5026577 := by exact prefixLift 5026577
  have htrace : WordTrace (prefixWord ++ tailWord_5026577) baseStart_5026577 baseEnd_5026577 := by
    simpa [prefixWord, tailWord_5026577, baseEnd_5026577] using wordTrace_append hprefix tailTrace_5026577
  have hstable : (prefixWord ++ tailWord_5026577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026577).length < 2 ^ (prefixWord ++ tailWord_5026577).sum := by decide
  have hdescent : baseEnd_5026577 < baseStart_5026577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026594 : List Nat := [3, 3, 1, 1, 2, 2, 1, 2, 3, 2, 3]
def baseStart_5026594 : Nat := 118140960795 + 5026594 * 2 ^ 59
def prefixEnd_5026594 : Nat := 4983230072969 + 3 ^ 40 * 5026594 * 2
def baseEnd_5026594 : Nat := 2581058777006211661558121

theorem tailTrace_5026594 : CollatzResearch.WordTrace tailWord_5026594 prefixEnd_5026594 2581058777006211661558121 := by
  unfold tailWord_5026594
  simp only [CollatzResearch.WordTrace]
  refine ⟨45833736187878971688427709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122223296501010591169140557 45833736187878971688427709)
  ·
    refine ⟨17187651070454614383160391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45833736187878971688427709 17187651070454614383160391)
    ·
      refine ⟨25781476605681921574740587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17187651070454614383160391 25781476605681921574740587)
      ·
        refine ⟨38672214908522882362110881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25781476605681921574740587 38672214908522882362110881)
        ·
          refine ⟨29004161181392161771583161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38672214908522882362110881 29004161181392161771583161)
          ·
            refine ⟨21753120886044121328687371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29004161181392161771583161 21753120886044121328687371)
            ·
              refine ⟨32629681329066181993031057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21753120886044121328687371 32629681329066181993031057)
              ·
                refine ⟨24472260996799636494773293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32629681329066181993031057 24472260996799636494773293)
                ·
                  refine ⟨9177097873799863685539985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24472260996799636494773293 9177097873799863685539985)
                  ·
                    refine ⟨6882823405349897764154989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9177097873799863685539985 6882823405349897764154989)
                    ·
                      refine ⟨2581058777006211661558121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6882823405349897764154989 2581058777006211661558121)
                      ·
                        rfl

theorem cell23_5026594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_5026594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026594 prefixEnd_5026594 := by exact prefixLift 5026594
  have htrace : WordTrace (prefixWord ++ tailWord_5026594) baseStart_5026594 baseEnd_5026594 := by
    simpa [prefixWord, tailWord_5026594, baseEnd_5026594] using wordTrace_append hprefix tailTrace_5026594
  have hstable : (prefixWord ++ tailWord_5026594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026594).length < 2 ^ (prefixWord ++ tailWord_5026594).sum := by decide
  have hdescent : baseEnd_5026594 < baseStart_5026594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026625 : List Nat := [1, 2, 5, 3, 1, 2, 2, 1, 1, 1, 4]
def baseStart_5026625 : Nat := 118140960795 + 5026625 * 2 ^ 59
def prefixEnd_5026625 : Nat := 4983230072969 + 3 ^ 40 * 5026625 * 2
def baseEnd_5026625 : Nat := 2581074694906501040270479

theorem tailTrace_5026625 : CollatzResearch.WordTrace tailWord_5026625 prefixEnd_5026625 2581074694906501040270479 := by
  unfold tailWord_5026625
  simp only [CollatzResearch.WordTrace]
  refine ⟨183336075414403579048089329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122224050276269052698726219 183336075414403579048089329)
  ·
    refine ⟨137502056560802684286066997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183336075414403579048089329 137502056560802684286066997)
    ·
      refine ⟨12890817802575251651818781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 137502056560802684286066997 12890817802575251651818781)
      ·
        refine ⟨4834056675965719369432043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12890817802575251651818781 4834056675965719369432043)
        ·
          refine ⟨7251085013948579054148065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4834056675965719369432043 7251085013948579054148065)
          ·
            refine ⟨5438313760461434290611049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7251085013948579054148065 5438313760461434290611049)
            ·
              refine ⟨4078735320346075717958287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5438313760461434290611049 4078735320346075717958287)
              ·
                refine ⟨6118102980519113576937431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4078735320346075717958287 6118102980519113576937431)
                ·
                  refine ⟨9177154470778670365406147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6118102980519113576937431 9177154470778670365406147)
                  ·
                    refine ⟨13765731706168005548109221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9177154470778670365406147 13765731706168005548109221)
                    ·
                      refine ⟨2581074694906501040270479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13765731706168005548109221 2581074694906501040270479)
                      ·
                        rfl

theorem cell23_5026625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_5026625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026625 prefixEnd_5026625 := by exact prefixLift 5026625
  have htrace : WordTrace (prefixWord ++ tailWord_5026625) baseStart_5026625 baseEnd_5026625 := by
    simpa [prefixWord, tailWord_5026625, baseEnd_5026625] using wordTrace_append hprefix tailTrace_5026625
  have hstable : (prefixWord ++ tailWord_5026625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026625).length < 2 ^ (prefixWord ++ tailWord_5026625).sum := by decide
  have hdescent : baseEnd_5026625 < baseStart_5026625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026634 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 5, 3, 2]
def baseStart_5026634 : Nat := 118140960795 + 5026634 * 2 ^ 59
def prefixEnd_5026634 : Nat := 4983230072969 + 3 ^ 40 * 5026634 * 2
def baseEnd_5026634 : Nat := 2581079316232391505057937

theorem tailTrace_5026634 : CollatzResearch.WordTrace tailWord_5026634 prefixEnd_5026634 2581079316232391505057937 := by
  unfold tailWord_5026634
  simp only [CollatzResearch.WordTrace]
  refine ⟨45834100917842743396291739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122224269114247315723444637 45834100917842743396291739)
  ·
    refine ⟨68751151376764115094437609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45834100917842743396291739 68751151376764115094437609)
    ·
      refine ⟨51563363532573086320828207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68751151376764115094437609 51563363532573086320828207)
      ·
        refine ⟨77345045298859629481242311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51563363532573086320828207 77345045298859629481242311)
        ·
          refine ⟨116017567948289444221863467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77345045298859629481242311 116017567948289444221863467)
          ·
            refine ⟨174026351922434166332795201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116017567948289444221863467 174026351922434166332795201)
            ·
              refine ⟨130519763941825624749596401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174026351922434166332795201 130519763941825624749596401)
              ·
                refine ⟨97889822956369218562197301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130519763941825624749596401 97889822956369218562197301)
                ·
                  refine ⟨9177170902159614240205997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97889822956369218562197301 9177170902159614240205997)
                  ·
                    refine ⟨3441439088309855340077249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9177170902159614240205997 3441439088309855340077249)
                    ·
                      refine ⟨2581079316232391505057937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3441439088309855340077249 2581079316232391505057937)
                      ·
                        rfl

theorem cell23_5026634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 5, 3, 2].length) (baseStart_5026634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026634 prefixEnd_5026634 := by exact prefixLift 5026634
  have htrace : WordTrace (prefixWord ++ tailWord_5026634) baseStart_5026634 baseEnd_5026634 := by
    simpa [prefixWord, tailWord_5026634, baseEnd_5026634] using wordTrace_append hprefix tailTrace_5026634
  have hstable : (prefixWord ++ tailWord_5026634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026634).length < 2 ^ (prefixWord ++ tailWord_5026634).sum := by decide
  have hdescent : baseEnd_5026634 < baseStart_5026634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026641 : List Nat := [1, 2, 2, 1, 6, 1, 1, 1, 4, 1, 3]
def baseStart_5026641 : Nat := 118140960795 + 5026641 * 2 ^ 59
def prefixEnd_5026641 : Nat := 4983230072969 + 3 ^ 40 * 5026641 * 2
def baseEnd_5026641 : Nat := 2581082910596972977670405

theorem tailTrace_5026641 : CollatzResearch.WordTrace tailWord_5026641 prefixEnd_5026641 2581082910596972977670405 := by
  unfold tailWord_5026641
  simp only [CollatzResearch.WordTrace]
  refine ⟨183336658982345613780671777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122224439321563742520447851 183336658982345613780671777)
  ·
    refine ⟨137502494236759210335503833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183336658982345613780671777 137502494236759210335503833)
    ·
      refine ⟨103126870677569407751627875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137502494236759210335503833 103126870677569407751627875)
      ·
        refine ⟨154690306016354111627441813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103126870677569407751627875 154690306016354111627441813)
        ·
          refine ⟨7251108094516598982536335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 154690306016354111627441813 7251108094516598982536335)
          ·
            refine ⟨10876662141774898473804503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7251108094516598982536335 10876662141774898473804503)
            ·
              refine ⟨16314993212662347710706755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10876662141774898473804503 16314993212662347710706755)
              ·
                refine ⟨24472489818993521566060133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16314993212662347710706755 24472489818993521566060133)
                ·
                  refine ⟨4588591841061285293636275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24472489818993521566060133 4588591841061285293636275)
                  ·
                    refine ⟨6882887761591927940454413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4588591841061285293636275 6882887761591927940454413)
                    ·
                      refine ⟨2581082910596972977670405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6882887761591927940454413 2581082910596972977670405)
                      ·
                        rfl

theorem cell23_5026641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 4, 1, 3].length) (baseStart_5026641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026641 prefixEnd_5026641 := by exact prefixLift 5026641
  have htrace : WordTrace (prefixWord ++ tailWord_5026641) baseStart_5026641 baseEnd_5026641 := by
    simpa [prefixWord, tailWord_5026641, baseEnd_5026641] using wordTrace_append hprefix tailTrace_5026641
  have hstable : (prefixWord ++ tailWord_5026641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026641).length < 2 ^ (prefixWord ++ tailWord_5026641).sum := by decide
  have hdescent : baseEnd_5026641 < baseStart_5026641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026658 : List Nat := [3, 3, 2, 1, 3, 2, 1, 1, 1, 3, 3]
def baseStart_5026658 : Nat := 118140960795 + 5026658 * 2 ^ 59
def prefixEnd_5026658 : Nat := 4983230072969 + 3 ^ 40 * 5026658 * 2
def baseEnd_5026658 : Nat := 2581091639768099411157827

theorem tailTrace_5026658 : CollatzResearch.WordTrace tailWord_5026658 prefixEnd_5026658 2581091639768099411157827 := by
  unfold tailWord_5026658
  simp only [CollatzResearch.WordTrace]
  refine ⟨45834319755821006421010157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122224852682189350456027085 45834319755821006421010157)
  ·
    refine ⟨17187869908432877407878809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45834319755821006421010157 17187869908432877407878809)
    ·
      refine ⟨12890902431324658055909107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17187869908432877407878809 12890902431324658055909107)
      ·
        refine ⟨19336353646986987083863661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12890902431324658055909107 19336353646986987083863661)
        ·
          refine ⟨7251132617620120156448873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19336353646986987083863661 7251132617620120156448873)
          ·
            refine ⟨5438349463215090117336655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7251132617620120156448873 5438349463215090117336655)
            ·
              refine ⟨8157524194822635176004983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5438349463215090117336655 8157524194822635176004983)
              ·
                refine ⟨12236286292233952764007475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8157524194822635176004983 12236286292233952764007475)
                ·
                  refine ⟨18354429438350929146011213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12236286292233952764007475 18354429438350929146011213)
                  ·
                    refine ⟨6882911039381598429754205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18354429438350929146011213 6882911039381598429754205)
                    ·
                      refine ⟨2581091639768099411157827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6882911039381598429754205 2581091639768099411157827)
                      ·
                        rfl

theorem cell23_5026658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_5026658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026658 prefixEnd_5026658 := by exact prefixLift 5026658
  have htrace : WordTrace (prefixWord ++ tailWord_5026658) baseStart_5026658 baseEnd_5026658 := by
    simpa [prefixWord, tailWord_5026658, baseEnd_5026658] using wordTrace_append hprefix tailTrace_5026658
  have hstable : (prefixWord ++ tailWord_5026658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026658).length < 2 ^ (prefixWord ++ tailWord_5026658).sum := by decide
  have hdescent : baseEnd_5026658 < baseStart_5026658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026667 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 2, 4, 3]
def baseStart_5026667 : Nat := 118140960795 + 5026667 * 2 ^ 59
def prefixEnd_5026667 : Nat := 4983230072969 + 3 ^ 40 * 5026667 * 2
def baseEnd_5026667 : Nat := 2581096261093989875945285

theorem tailTrace_5026667 : CollatzResearch.WordTrace tailWord_5026667 prefixEnd_5026667 2581096261093989875945285 := by
  unfold tailWord_5026667
  simp only [CollatzResearch.WordTrace]
  refine ⟨183337607280251420221118255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122225071520167613480745503 183337607280251420221118255)
  ·
    refine ⟨275006410920377130331677383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183337607280251420221118255 275006410920377130331677383)
    ·
      refine ⟨412509616380565695497516075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275006410920377130331677383 412509616380565695497516075)
      ·
        refine ⟨618764424570848543246274113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412509616380565695497516075 618764424570848543246274113)
        ·
          refine ⟨464073318428136407434705585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 618764424570848543246274113 464073318428136407434705585)
          ·
            refine ⟨348054988821102305576029189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 464073318428136407434705585 348054988821102305576029189)
            ·
              refine ⟨65260310403956682295505473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 348054988821102305576029189 65260310403956682295505473)
              ·
                refine ⟨48945232802967511721629105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65260310403956682295505473 48945232802967511721629105)
                ·
                  refine ⟨36708924602225633791221829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48945232802967511721629105 36708924602225633791221829)
                  ·
                    refine ⟨6882923362917306335854093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36708924602225633791221829 6882923362917306335854093)
                    ·
                      refine ⟨2581096261093989875945285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6882923362917306335854093 2581096261093989875945285)
                      ·
                        rfl

theorem cell23_5026667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 4, 3].length) (baseStart_5026667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026667 prefixEnd_5026667 := by exact prefixLift 5026667
  have htrace : WordTrace (prefixWord ++ tailWord_5026667) baseStart_5026667 baseEnd_5026667 := by
    simpa [prefixWord, tailWord_5026667, baseEnd_5026667] using wordTrace_append hprefix tailTrace_5026667
  have hstable : (prefixWord ++ tailWord_5026667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026667).length < 2 ^ (prefixWord ++ tailWord_5026667).sum := by decide
  have hdescent : baseEnd_5026667 < baseStart_5026667 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026681 : List Nat := [1, 2, 1, 3, 2, 3, 1, 2, 4, 2, 2]
def baseStart_5026681 : Nat := 118140960795 + 5026681 * 2 ^ 59
def prefixEnd_5026681 : Nat := 4983230072969 + 3 ^ 40 * 5026681 * 2
def baseEnd_5026681 : Nat := 2581103449823152821170221

theorem tailTrace_5026681 : CollatzResearch.WordTrace tailWord_5026681 prefixEnd_5026681 2581103449823152821170221 := by
  unfold tailWord_5026681
  simp only [CollatzResearch.WordTrace]
  refine ⟨183338117902200700612127897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122225411934800467074751931 183338117902200700612127897)
  ·
    refine ⟨137503588426650525459095923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183338117902200700612127897 137503588426650525459095923)
    ·
      refine ⟨206255382639975788188643885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137503588426650525459095923 206255382639975788188643885)
      ·
        refine ⟨77345768489990920570741457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206255382639975788188643885 77345768489990920570741457)
        ·
          refine ⟨58009326367493190428056093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77345768489990920570741457 58009326367493190428056093)
          ·
            refine ⟨21753497387809946410521035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58009326367493190428056093 21753497387809946410521035)
            ·
              refine ⟨32630246081714919615781553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21753497387809946410521035 32630246081714919615781553)
              ·
                refine ⟨24472684561286189711836165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32630246081714919615781553 24472684561286189711836165)
                ·
                  refine ⟨4588628355241160570969281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24472684561286189711836165 4588628355241160570969281)
                  ·
                    refine ⟨3441471266430870428226961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4588628355241160570969281 3441471266430870428226961)
                    ·
                      refine ⟨2581103449823152821170221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3441471266430870428226961 2581103449823152821170221)
                      ·
                        rfl

theorem cell23_5026681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 4, 2, 2].length) (baseStart_5026681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026681 prefixEnd_5026681 := by exact prefixLift 5026681
  have htrace : WordTrace (prefixWord ++ tailWord_5026681) baseStart_5026681 baseEnd_5026681 := by
    simpa [prefixWord, tailWord_5026681, baseEnd_5026681] using wordTrace_append hprefix tailTrace_5026681
  have hstable : (prefixWord ++ tailWord_5026681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026681).length < 2 ^ (prefixWord ++ tailWord_5026681).sum := by decide
  have hdescent : baseEnd_5026681 < baseStart_5026681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026698 : List Nat := [3, 1, 2, 4, 1, 1, 2, 1, 4, 2, 2]
def baseStart_5026698 : Nat := 118140960795 + 5026698 * 2 ^ 59
def prefixEnd_5026698 : Nat := 4983230072969 + 3 ^ 40 * 5026698 * 2
def baseEnd_5026698 : Nat := 2581112178994279254657643

theorem tailTrace_5026698 : CollatzResearch.WordTrace tailWord_5026698 prefixEnd_5026698 2581112178994279254657643 := by
  unfold tailWord_5026698
  simp only [CollatzResearch.WordTrace]
  refine ⟨45834684485784778128874187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122225825295426075010331165 45834684485784778128874187)
  ·
    refine ⟨68752026728677167193311281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45834684485784778128874187 68752026728677167193311281)
    ·
      refine ⟨51564020046507875394983461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68752026728677167193311281 51564020046507875394983461)
      ·
        refine ⟨9668253758720226636559399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51564020046507875394983461 9668253758720226636559399)
        ·
          refine ⟨14502380638080339954839099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9668253758720226636559399 14502380638080339954839099)
          ·
            refine ⟨21753570957120509932258649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14502380638080339954839099 21753570957120509932258649)
            ·
              refine ⟨16315178217840382449193987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21753570957120509932258649 16315178217840382449193987)
              ·
                refine ⟨24472767326760573673790981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16315178217840382449193987 24472767326760573673790981)
                ·
                  refine ⟨4588643873767607563835809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24472767326760573673790981 4588643873767607563835809)
                  ·
                    refine ⟨3441482905325705672876857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4588643873767607563835809 3441482905325705672876857)
                    ·
                      refine ⟨2581112178994279254657643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3441482905325705672876857 2581112178994279254657643)
                      ·
                        rfl

theorem cell23_5026698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_5026698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026698 prefixEnd_5026698 := by exact prefixLift 5026698
  have htrace : WordTrace (prefixWord ++ tailWord_5026698) baseStart_5026698 baseEnd_5026698 := by
    simpa [prefixWord, tailWord_5026698, baseEnd_5026698] using wordTrace_append hprefix tailTrace_5026698
  have hstable : (prefixWord ++ tailWord_5026698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026698).length < 2 ^ (prefixWord ++ tailWord_5026698).sum := by decide
  have hdescent : baseEnd_5026698 < baseStart_5026698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026781 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 5, 4]
def baseStart_5026781 : Nat := 118140960795 + 5026781 * 2 ^ 59
def prefixEnd_5026781 : Nat := 4983230072969 + 3 ^ 40 * 5026781 * 2
def baseEnd_5026781 : Nat := 860384932629534143306587

theorem tailTrace_5026781 : CollatzResearch.WordTrace tailWord_5026781 prefixEnd_5026781 860384932629534143306587 := by
  unfold tailWord_5026781
  simp only [CollatzResearch.WordTrace]
  refine ⟨183341765201838417690768197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122227843467892278460512131 183341765201838417690768197)
  ·
    refine ⟨34376580975344703317019037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183341765201838417690768197 34376580975344703317019037)
    ·
      refine ⟨12891217865754263743882139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34376580975344703317019037 12891217865754263743882139)
      ·
        refine ⟨19336826798631395615823209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12891217865754263743882139 19336826798631395615823209)
        ·
          refine ⟨14502620098973546711867407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19336826798631395615823209 14502620098973546711867407)
          ·
            refine ⟨21753930148460320067801111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14502620098973546711867407 21753930148460320067801111)
            ·
              refine ⟨32630895222690480101701667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21753930148460320067801111 32630895222690480101701667)
              ·
                refine ⟨48946342834035720152552501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32630895222690480101701667 48946342834035720152552501)
                ·
                  refine ⟨4588719640690848764301797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48946342834035720152552501 4588719640690848764301797)
                  ·
                    refine ⟨860384932629534143306587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4588719640690848764301797 860384932629534143306587)
                    ·
                      rfl

theorem cell23_5026781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_5026781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026781 prefixEnd_5026781 := by exact prefixLift 5026781
  have htrace : WordTrace (prefixWord ++ tailWord_5026781) baseStart_5026781 baseEnd_5026781 := by
    simpa [prefixWord, tailWord_5026781, baseEnd_5026781] using wordTrace_append hprefix tailTrace_5026781
  have hstable : (prefixWord ++ tailWord_5026781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026781).length < 2 ^ (prefixWord ++ tailWord_5026781).sum := by decide
  have hdescent : baseEnd_5026781 < baseStart_5026781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026791 : List Nat := [1, 1, 5, 2, 2, 2, 1, 1, 1, 4, 3]
def baseStart_5026791 : Nat := 118140960795 + 5026791 * 2 ^ 59
def prefixEnd_5026791 : Nat := 4983230072969 + 3 ^ 40 * 5026791 * 2
def baseEnd_5026791 : Nat := 2581159932695147390794715

theorem tailTrace_5026791 : CollatzResearch.WordTrace tailWord_5026791 prefixEnd_5026791 2581159932695147390794715 := by
  unfold tailWord_5026791
  simp only [CollatzResearch.WordTrace]
  refine ⟨183342129931802189398632227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122228086621201459599088151 183342129931802189398632227)
  ·
    refine ⟨275013194897703284097948341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183342129931802189398632227 275013194897703284097948341)
    ·
      refine ⟨25782487021659682884182657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 275013194897703284097948341 25782487021659682884182657)
      ·
        refine ⟨19336865266244762163136993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25782487021659682884182657 19336865266244762163136993)
        ·
          refine ⟨14502648949683571622352745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19336865266244762163136993 14502648949683571622352745)
          ·
            refine ⟨10876986712262678716764559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14502648949683571622352745 10876986712262678716764559)
            ·
              refine ⟨16315480068394018075146839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10876986712262678716764559 16315480068394018075146839)
              ·
                refine ⟨24473220102591027112720259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16315480068394018075146839 24473220102591027112720259)
                ·
                  refine ⟨36709830153886540669080389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24473220102591027112720259 36709830153886540669080389)
                  ·
                    refine ⟨6883093153853726375452573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36709830153886540669080389 6883093153853726375452573)
                    ·
                      refine ⟨2581159932695147390794715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6883093153853726375452573 2581159932695147390794715)
                      ·
                        rfl

theorem cell23_5026791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_5026791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026791 prefixEnd_5026791 := by exact prefixLift 5026791
  have htrace : WordTrace (prefixWord ++ tailWord_5026791) baseStart_5026791 baseEnd_5026791 := by
    simpa [prefixWord, tailWord_5026791, baseEnd_5026791] using wordTrace_append hprefix tailTrace_5026791
  have hstable : (prefixWord ++ tailWord_5026791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026791).length < 2 ^ (prefixWord ++ tailWord_5026791).sum := by decide
  have hdescent : baseEnd_5026791 < baseStart_5026791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026871 : List Nat := [1, 1, 3, 1, 2, 2, 1, 6, 2, 4]
def baseStart_5026871 : Nat := 118140960795 + 5026871 * 2 ^ 59
def prefixEnd_5026871 : Nat := 4983230072969 + 3 ^ 40 * 5026871 * 2
def baseEnd_5026871 : Nat := 860400337049169025931449

theorem tailTrace_5026871 : CollatzResearch.WordTrace tailWord_5026871 prefixEnd_5026871 860400337049169025931449 := by
  unfold tailWord_5026871
  simp only [CollatzResearch.WordTrace]
  refine ⟨183345047771512363061544467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122230031847674908707696311 183345047771512363061544467)
  ·
    refine ⟨275017571657268544592316701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183345047771512363061544467 275017571657268544592316701)
    ·
      refine ⟨103131589371475704222118763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275017571657268544592316701 103131589371475704222118763)
      ·
        refine ⟨154697384057213556333178145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103131589371475704222118763 154697384057213556333178145)
        ·
          refine ⟨116023038042910167249883609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154697384057213556333178145 116023038042910167249883609)
          ·
            refine ⟨87017278532182625437412707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116023038042910167249883609 87017278532182625437412707)
            ·
              refine ⟨130525917798273938156119061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87017278532182625437412707 130525917798273938156119061)
              ·
                refine ⟨6118402396794090851068081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 130525917798273938156119061 6118402396794090851068081)
                ·
                  refine ⟨4588801797595568138301061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6118402396794090851068081 4588801797595568138301061)
                  ·
                    refine ⟨860400337049169025931449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4588801797595568138301061 860400337049169025931449)
                    ·
                      rfl

theorem cell23_5026871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 2, 4].length) (baseStart_5026871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026871 prefixEnd_5026871 := by exact prefixLift 5026871
  have htrace : WordTrace (prefixWord ++ tailWord_5026871) baseStart_5026871 baseEnd_5026871 := by
    simpa [prefixWord, tailWord_5026871, baseEnd_5026871] using wordTrace_append hprefix tailTrace_5026871
  have hstable : (prefixWord ++ tailWord_5026871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026871).length < 2 ^ (prefixWord ++ tailWord_5026871).sum := by decide
  have hdescent : baseEnd_5026871 < baseStart_5026871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026872 : List Nat := [2, 1, 2, 1, 5, 2, 3, 2, 1, 1, 3]
def baseStart_5026872 : Nat := 118140960795 + 5026872 * 2 ^ 59
def prefixEnd_5026872 : Nat := 4983230072969 + 3 ^ 40 * 5026872 * 2
def baseEnd_5026872 : Nat := 2581201524628161573881843

theorem tailTrace_5026872 : CollatzResearch.WordTrace tailWord_5026872 prefixEnd_5026872 2581201524628161573881843 := by
  unfold tailWord_5026872
  simp only [CollatzResearch.WordTrace]
  refine ⟨91672542122254370116165435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122230056163005826821553913 91672542122254370116165435)
  ·
    refine ⟨137508813183381555174248153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91672542122254370116165435 137508813183381555174248153)
    ·
      refine ⟨103131609887536166380686115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137508813183381555174248153 103131609887536166380686115)
      ·
        refine ⟨154697414831304249571029173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103131609887536166380686115 154697414831304249571029173)
        ·
          refine ⟨14502882640434773397283985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 154697414831304249571029173 14502882640434773397283985)
          ·
            refine ⟨10877161980326080047962989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14502882640434773397283985 10877161980326080047962989)
            ·
              refine ⟨4078935742622280017986121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10877161980326080047962989 4078935742622280017986121)
              ·
                refine ⟨3059201806966710013489591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4078935742622280017986121 3059201806966710013489591)
                ·
                  refine ⟨4588802710450065020234387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3059201806966710013489591 4588802710450065020234387)
                  ·
                    refine ⟨6883204065675097530351581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4588802710450065020234387 6883204065675097530351581)
                    ·
                      refine ⟨2581201524628161573881843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6883204065675097530351581 2581201524628161573881843)
                      ·
                        rfl

theorem cell23_5026872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 2, 1, 1, 3].length) (baseStart_5026872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026872 prefixEnd_5026872 := by exact prefixLift 5026872
  have htrace : WordTrace (prefixWord ++ tailWord_5026872) baseStart_5026872 baseEnd_5026872 := by
    simpa [prefixWord, tailWord_5026872, baseEnd_5026872] using wordTrace_append hprefix tailTrace_5026872
  have hstable : (prefixWord ++ tailWord_5026872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026872).length < 2 ^ (prefixWord ++ tailWord_5026872).sum := by decide
  have hdescent : baseEnd_5026872 < baseStart_5026872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026874 : List Nat := [3, 1, 1, 1, 3, 1, 3, 2, 1, 1, 6]
def baseStart_5026874 : Nat := 118140960795 + 5026874 * 2 ^ 59
def prefixEnd_5026874 : Nat := 4983230072969 + 3 ^ 40 * 5026874 * 2
def baseEnd_5026874 : Nat := 2581202551589470566056833

theorem tailTrace_5026874 : CollatzResearch.WordTrace tailWord_5026874 prefixEnd_5026874 2581202551589470566056833 := by
  unfold tailWord_5026874
  simp only [CollatzResearch.WordTrace]
  refine ⟨45836289297625373643475919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122230104793667663049269117 45836289297625373643475919)
  ·
    refine ⟨68754433946438060465213879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45836289297625373643475919 68754433946438060465213879)
    ·
      refine ⟨103131650919657090697820819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68754433946438060465213879 103131650919657090697820819)
      ·
        refine ⟨154697476379485636046731229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103131650919657090697820819 154697476379485636046731229)
        ·
          refine ⟨58011553642307113517524211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154697476379485636046731229 58011553642307113517524211)
          ·
            refine ⟨87017330463460670276286317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58011553642307113517524211 87017330463460670276286317)
            ·
              refine ⟨32631498923797751353607369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87017330463460670276286317 32631498923797751353607369)
              ·
                refine ⟨24473624192848313515205527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32631498923797751353607369 24473624192848313515205527)
                ·
                  refine ⟨36710436289272470272808291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24473624192848313515205527 36710436289272470272808291)
                  ·
                    refine ⟨55065654433908705409212437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36710436289272470272808291 55065654433908705409212437)
                    ·
                      refine ⟨2581202551589470566056833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55065654433908705409212437 2581202551589470566056833)
                      ·
                        rfl

theorem cell23_5026874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_5026874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026874 prefixEnd_5026874 := by exact prefixLift 5026874
  have htrace : WordTrace (prefixWord ++ tailWord_5026874) baseStart_5026874 baseEnd_5026874 := by
    simpa [prefixWord, tailWord_5026874, baseEnd_5026874] using wordTrace_append hprefix tailTrace_5026874
  have hstable : (prefixWord ++ tailWord_5026874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026874).length < 2 ^ (prefixWord ++ tailWord_5026874).sum := by decide
  have hdescent : baseEnd_5026874 < baseStart_5026874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026898 : List Nat := [3, 2, 2, 1, 3, 2, 1, 1, 3, 2, 3]
def baseStart_5026898 : Nat := 118140960795 + 5026898 * 2 ^ 59
def prefixEnd_5026898 : Nat := 4983230072969 + 3 ^ 40 * 5026898 * 2
def baseEnd_5026898 : Nat := 2581214875125178472156723

theorem tailTrace_5026898 : CollatzResearch.WordTrace tailWord_5026898 prefixEnd_5026898 2581214875125178472156723 := by
  unfold tailWord_5026898
  simp only [CollatzResearch.WordTrace]
  refine ⟨45836508135603636668194337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122230688361609697781851565 45836508135603636668194337)
  ·
    refine ⟨34377381101702727501145753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45836508135603636668194337 34377381101702727501145753)
    ·
      refine ⟨25783035826277045625859315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34377381101702727501145753 25783035826277045625859315)
      ·
        refine ⟨38674553739415568438788973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25783035826277045625859315 38674553739415568438788973)
        ·
          refine ⟨14502957652280838164545865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38674553739415568438788973 14502957652280838164545865)
          ·
            refine ⟨10877218239210628623409399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14502957652280838164545865 10877218239210628623409399)
            ·
              refine ⟨16315827358815942935114099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10877218239210628623409399 16315827358815942935114099)
              ·
                refine ⟨24473741038223914402671149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16315827358815942935114099 24473741038223914402671149)
                ·
                  refine ⟨9177652889333967901001681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24473741038223914402671149 9177652889333967901001681)
                  ·
                    refine ⟨6883239667000475925751261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9177652889333967901001681 6883239667000475925751261)
                    ·
                      refine ⟨2581214875125178472156723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6883239667000475925751261 2581214875125178472156723)
                      ·
                        rfl

theorem cell23_5026898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_5026898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026898 prefixEnd_5026898 := by exact prefixLift 5026898
  have htrace : WordTrace (prefixWord ++ tailWord_5026898) baseStart_5026898 baseEnd_5026898 := by
    simpa [prefixWord, tailWord_5026898, baseEnd_5026898] using wordTrace_append hprefix tailTrace_5026898
  have hstable : (prefixWord ++ tailWord_5026898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026898).length < 2 ^ (prefixWord ++ tailWord_5026898).sum := by decide
  have hdescent : baseEnd_5026898 < baseStart_5026898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026911 : List Nat := [1, 1, 2, 3, 1, 1, 5, 2, 1, 3, 3]
def baseStart_5026911 : Nat := 118140960795 + 5026911 * 2 ^ 59
def prefixEnd_5026911 : Nat := 4983230072969 + 3 ^ 40 * 5026911 * 2
def baseEnd_5026911 : Nat := 2581221550373686921294163

theorem tailTrace_5026911 : CollatzResearch.WordTrace tailWord_5026911 prefixEnd_5026911 2581221550373686921294163 := by
  unfold tailWord_5026911
  simp only [CollatzResearch.WordTrace]
  refine ⟨183346506691367449893000587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122231004460911633262000391 183346506691367449893000587)
  ·
    refine ⟨275019760037051174839500881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183346506691367449893000587 275019760037051174839500881)
    ·
      refine ⟨206264820027788381129625661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275019760037051174839500881 206264820027788381129625661)
      ·
        refine ⟨77349307510420642923609623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206264820027788381129625661 77349307510420642923609623)
        ·
          refine ⟨116023961265630964385414435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77349307510420642923609623 116023961265630964385414435)
          ·
            refine ⟨174035941898446446578121653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116023961265630964385414435 174035941898446446578121653)
            ·
              refine ⟨16315869552979354366698905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 174035941898446446578121653 16315869552979354366698905)
              ·
                refine ⟨12236902164734515775024179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16315869552979354366698905 12236902164734515775024179)
                ·
                  refine ⟨18355353247101773662536269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12236902164734515775024179 18355353247101773662536269)
                  ·
                    refine ⟨6883257467663165123451101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18355353247101773662536269 6883257467663165123451101)
                    ·
                      refine ⟨2581221550373686921294163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6883257467663165123451101 2581221550373686921294163)
                      ·
                        rfl

theorem cell23_5026911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_5026911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026911 prefixEnd_5026911 := by exact prefixLift 5026911
  have htrace : WordTrace (prefixWord ++ tailWord_5026911) baseStart_5026911 baseEnd_5026911 := by
    simpa [prefixWord, tailWord_5026911, baseEnd_5026911] using wordTrace_append hprefix tailTrace_5026911
  have hstable : (prefixWord ++ tailWord_5026911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026911).length < 2 ^ (prefixWord ++ tailWord_5026911).sum := by decide
  have hdescent : baseEnd_5026911 < baseStart_5026911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026944 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 1, 8]
def baseStart_5026944 : Nat := 118140960795 + 5026944 * 2 ^ 59
def prefixEnd_5026944 : Nat := 4983230072969 + 3 ^ 40 * 5026944 * 2
def baseEnd_5026944 : Nat := 860412831745095097393837

theorem tailTrace_5026944 : CollatzResearch.WordTrace tailWord_5026944 prefixEnd_5026944 860412831745095097393837 := by
  unfold tailWord_5026944
  simp only [CollatzResearch.WordTrace]
  refine ⟨91673855150123948264475943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122231806866831931019301257 91673855150123948264475943)
  ·
    refine ⟨137510782725185922396713915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91673855150123948264475943 137510782725185922396713915)
    ·
      refine ⟨206266174087778883595070873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137510782725185922396713915 206266174087778883595070873)
      ·
        refine ⟨154699630565834162696303155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206266174087778883595070873 154699630565834162696303155)
        ·
          refine ⟨232049445848751244044454733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154699630565834162696303155 232049445848751244044454733)
          ·
            refine ⟨87018542193281716516670525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232049445848751244044454733 87018542193281716516670525)
            ·
              refine ⟨32631953322480643693751447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87018542193281716516670525 32631953322480643693751447)
              ·
                refine ⟨48947929983720965540627171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32631953322480643693751447 48947929983720965540627171)
                ·
                  refine ⟨73421894975581448310940757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48947929983720965540627171 73421894975581448310940757)
                  ·
                    refine ⟨860412831745095097393837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73421894975581448310940757 860412831745095097393837)
                    ·
                      rfl

theorem cell23_5026944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 1, 8].length) (baseStart_5026944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026944 prefixEnd_5026944 := by exact prefixLift 5026944
  have htrace : WordTrace (prefixWord ++ tailWord_5026944) baseStart_5026944 baseEnd_5026944 := by
    simpa [prefixWord, tailWord_5026944, baseEnd_5026944] using wordTrace_append hprefix tailTrace_5026944
  have hstable : (prefixWord ++ tailWord_5026944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026944).length < 2 ^ (prefixWord ++ tailWord_5026944).sum := by decide
  have hdescent : baseEnd_5026944 < baseStart_5026944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026945 : List Nat := [1, 2, 4, 2, 2, 1, 2, 3, 2, 1, 3]
def baseStart_5026945 : Nat := 118140960795 + 5026945 * 2 ^ 59
def prefixEnd_5026945 : Nat := 4983230072969 + 3 ^ 40 * 5026945 * 2
def baseEnd_5026945 : Nat := 2581239008715939788269007

theorem tailTrace_5026945 : CollatzResearch.WordTrace tailWord_5026945 prefixEnd_5026945 2581239008715939788269007 := by
  unfold tailWord_5026945
  simp only [CollatzResearch.WordTrace]
  refine ⟨183347746773244273699738289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122231831182162849133158859 183347746773244273699738289)
  ·
    refine ⟨137510810079933205274803717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183347746773244273699738289 137510810079933205274803717)
    ·
      refine ⟨25783276889987475989025697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137510810079933205274803717 25783276889987475989025697)
      ·
        refine ⟨19337457667490606991769273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25783276889987475989025697 19337457667490606991769273)
        ·
          refine ⟨14503093250617955243826955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19337457667490606991769273 14503093250617955243826955)
          ·
            refine ⟨21754639875926932865740433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14503093250617955243826955 21754639875926932865740433)
            ·
              refine ⟨16315979906945199649305325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21754639875926932865740433 16315979906945199649305325)
              ·
                refine ⟨6118492465104449868489497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16315979906945199649305325 6118492465104449868489497)
                ·
                  refine ⟨4588869348828337401367123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6118492465104449868489497 4588869348828337401367123)
                  ·
                    refine ⟨6883304023242506102050685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4588869348828337401367123 6883304023242506102050685)
                    ·
                      refine ⟨2581239008715939788269007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6883304023242506102050685 2581239008715939788269007)
                      ·
                        rfl

theorem cell23_5026945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_5026945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026945 prefixEnd_5026945 := by exact prefixLift 5026945
  have htrace : WordTrace (prefixWord ++ tailWord_5026945) baseStart_5026945 baseEnd_5026945 := by
    simpa [prefixWord, tailWord_5026945, baseEnd_5026945] using wordTrace_append hprefix tailTrace_5026945
  have hstable : (prefixWord ++ tailWord_5026945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026945).length < 2 ^ (prefixWord ++ tailWord_5026945).sum := by decide
  have hdescent : baseEnd_5026945 < baseStart_5026945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026972 : List Nat := [2, 2, 3, 2, 1, 2, 4, 1, 1, 3, 2]
def baseStart_5026972 : Nat := 118140960795 + 5026972 * 2 ^ 59
def prefixEnd_5026972 : Nat := 4983230072969 + 3 ^ 40 * 5026972 * 2
def baseEnd_5026972 : Nat := 2581252872693611182631383

theorem tailTrace_5026972 : CollatzResearch.WordTrace tailWord_5026972 prefixEnd_5026972 2581252872693611182631383 := by
  unfold tailWord_5026972
  simp only [CollatzResearch.WordTrace]
  refine ⟨91674365772073228655485585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122232487696097638207314113 91674365772073228655485585)
  ·
    refine ⟨68755774329054921491614189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91674365772073228655485585 68755774329054921491614189)
    ·
      refine ⟨25783415373395595559355321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68755774329054921491614189 25783415373395595559355321)
      ·
        refine ⟨19337561530046696669516491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25783415373395595559355321 19337561530046696669516491)
        ·
          refine ⟨29006342295070045004274737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19337561530046696669516491 29006342295070045004274737)
          ·
            refine ⟨21754756721302533753206053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29006342295070045004274737 21754756721302533753206053)
            ·
              refine ⟨4079016885244225078726135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21754756721302533753206053 4079016885244225078726135)
              ·
                refine ⟨6118525327866337618089203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4079016885244225078726135 6118525327866337618089203)
                ·
                  refine ⟨9177787991799506427133805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6118525327866337618089203 9177787991799506427133805)
                  ·
                    refine ⟨3441670496924814910175177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9177787991799506427133805 3441670496924814910175177)
                    ·
                      refine ⟨2581252872693611182631383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3441670496924814910175177 2581252872693611182631383)
                      ·
                        rfl

theorem cell23_5026972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_5026972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026972 prefixEnd_5026972 := by exact prefixLift 5026972
  have htrace : WordTrace (prefixWord ++ tailWord_5026972) baseStart_5026972 baseEnd_5026972 := by
    simpa [prefixWord, tailWord_5026972, baseEnd_5026972] using wordTrace_append hprefix tailTrace_5026972
  have hstable : (prefixWord ++ tailWord_5026972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026972).length < 2 ^ (prefixWord ++ tailWord_5026972).sum := by decide
  have hdescent : baseEnd_5026972 < baseStart_5026972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5026981 : List Nat := [1, 3, 1, 2, 1, 4, 1, 2, 2, 2, 4]
def baseStart_5026981 : Nat := 118140960795 + 5026981 * 2 ^ 59
def prefixEnd_5026981 : Nat := 4983230072969 + 3 ^ 40 * 5026981 * 2
def baseEnd_5026981 : Nat := 2581257494019501647418841

theorem tailTrace_5026981 : CollatzResearch.WordTrace tailWord_5026981 prefixEnd_5026981 2581257494019501647418841 := by
  unfold tailWord_5026981
  simp only [CollatzResearch.WordTrace]
  refine ⟨183349059801113851848048797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122232706534075901232032531 183349059801113851848048797)
  ·
    refine ⟨68755897425417694443018299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183349059801113851848048797 68755897425417694443018299)
    ·
      refine ⟨103133846138126541664527449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68755897425417694443018299 103133846138126541664527449)
      ·
        refine ⟨77350384603594906248395587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103133846138126541664527449 77350384603594906248395587)
        ·
          refine ⟨116025576905392359372593381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77350384603594906248395587 116025576905392359372593381)
          ·
            refine ⟨21754795669761067382361259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116025576905392359372593381 21754795669761067382361259)
            ·
              refine ⟨32632193504641601073541889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21754795669761067382361259 32632193504641601073541889)
              ·
                refine ⟨24474145128481200805156417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32632193504641601073541889 24474145128481200805156417)
                ·
                  refine ⟨18355608846360900603867313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24474145128481200805156417 18355608846360900603867313)
                  ·
                    refine ⟨13766706634770675452900485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18355608846360900603867313 13766706634770675452900485)
                    ·
                      refine ⟨2581257494019501647418841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13766706634770675452900485 2581257494019501647418841)
                      ·
                        rfl

theorem cell23_5026981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_5026981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5026981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5026981 prefixEnd_5026981 := by exact prefixLift 5026981
  have htrace : WordTrace (prefixWord ++ tailWord_5026981) baseStart_5026981 baseEnd_5026981 := by
    simpa [prefixWord, tailWord_5026981, baseEnd_5026981] using wordTrace_append hprefix tailTrace_5026981
  have hstable : (prefixWord ++ tailWord_5026981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5026981).length < 2 ^ (prefixWord ++ tailWord_5026981).sum := by decide
  have hdescent : baseEnd_5026981 < baseStart_5026981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5026981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027098 : List Nat := [3, 1, 1, 3, 3, 1, 1, 4, 6]
def baseStart_5027098 : Nat := 118140960795 + 5027098 * 2 ^ 59
def prefixEnd_5027098 : Nat := 4983230072969 + 3 ^ 40 * 5027098 * 2
def baseEnd_5027098 : Nat := 286813063472897521072867

theorem tailTrace_5027098 : CollatzResearch.WordTrace tailWord_5027098 prefixEnd_5027098 286813063472897521072867 := by
  unfold tailWord_5027098
  simp only [CollatzResearch.WordTrace]
  refine ⟨45838331785422495207514487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122235551427793320553371965 45838331785422495207514487)
  ·
    refine ⟨68757497678133742811271731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45838331785422495207514487 68757497678133742811271731)
    ·
      refine ⟨103136246517200614216907597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68757497678133742811271731 103136246517200614216907597)
      ·
        refine ⟨38676092443950230331340349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103136246517200614216907597 38676092443950230331340349)
        ·
          refine ⟨14503534666481336374252631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38676092443950230331340349 14503534666481336374252631)
          ·
            refine ⟨21755301999722004561378947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14503534666481336374252631 21755301999722004561378947)
            ·
              refine ⟨32632952999583006842068421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21755301999722004561378947 32632952999583006842068421)
              ·
                refine ⟨6118678687421813782887829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32632952999583006842068421 6118678687421813782887829)
                ·
                  refine ⟨286813063472897521072867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6118678687421813782887829 286813063472897521072867)
                  ·
                    rfl

theorem cell23_5027098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 6].length) (baseStart_5027098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027098 prefixEnd_5027098 := by exact prefixLift 5027098
  have htrace : WordTrace (prefixWord ++ tailWord_5027098) baseStart_5027098 baseEnd_5027098 := by
    simpa [prefixWord, tailWord_5027098, baseEnd_5027098] using wordTrace_append hprefix tailTrace_5027098
  have hstable : (prefixWord ++ tailWord_5027098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027098).length < 2 ^ (prefixWord ++ tailWord_5027098).sum := by decide
  have hdescent : baseEnd_5027098 < baseStart_5027098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027125 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 5, 1, 3]
def baseStart_5027125 : Nat := 118140960795 + 5027125 * 2 ^ 59
def prefixEnd_5027125 : Nat := 4983230072969 + 3 ^ 40 * 5027125 * 2
def baseEnd_5027125 : Nat := 2581331435233749084018179

theorem tailTrace_5027125 : CollatzResearch.WordTrace tailWord_5027125 prefixEnd_5027125 2581331435233749084018179 := by
  unfold tailWord_5027125
  simp only [CollatzResearch.WordTrace]
  refine ⟨183354311912592164441290829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122236207941728109627527219 183354311912592164441290829)
  ·
    refine ⟨68757866967222061665484061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183354311912592164441290829 68757866967222061665484061)
    ·
      refine ⟨25784200112708273124556523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68757866967222061665484061 25784200112708273124556523)
      ·
        refine ⟨38676300169062409686834785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25784200112708273124556523 38676300169062409686834785)
        ·
          refine ⟨29007225126796807265126089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38676300169062409686834785 29007225126796807265126089)
          ·
            refine ⟨21755418845097605448844567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29007225126796807265126089 21755418845097605448844567)
            ·
              refine ⟨32633128267646408173266851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21755418845097605448844567 32633128267646408173266851)
              ·
                refine ⟨48949692401469612259900277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32633128267646408173266851 48949692401469612259900277)
                ·
                  refine ⟨4589033662637776149365651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48949692401469612259900277 4589033662637776149365651)
                  ·
                    refine ⟨6883550493956664224048477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4589033662637776149365651 6883550493956664224048477)
                    ·
                      refine ⟨2581331435233749084018179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6883550493956664224048477 2581331435233749084018179)
                      ·
                        rfl

theorem cell23_5027125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_5027125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027125 prefixEnd_5027125 := by exact prefixLift 5027125
  have htrace : WordTrace (prefixWord ++ tailWord_5027125) baseStart_5027125 baseEnd_5027125 := by
    simpa [prefixWord, tailWord_5027125, baseEnd_5027125] using wordTrace_append hprefix tailTrace_5027125
  have hstable : (prefixWord ++ tailWord_5027125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027125).length < 2 ^ (prefixWord ++ tailWord_5027125).sum := by decide
  have hdescent : baseEnd_5027125 < baseStart_5027125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027126 : List Nat := [5, 1, 2, 3, 2, 1, 1, 1, 2, 1, 4]
def baseStart_5027126 : Nat := 118140960795 + 5027126 * 2 ^ 59
def prefixEnd_5027126 : Nat := 4983230072969 + 3 ^ 40 * 5027126 * 2
def baseEnd_5027126 : Nat := 2581331948714403580105675

theorem tailTrace_5027126 : CollatzResearch.WordTrace tailWord_5027126 prefixEnd_5027126 2581331948714403580105675 := by
  unfold tailWord_5027126
  simp only [CollatzResearch.WordTrace]
  refine ⟨11459646774099283850754827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122236232257059027741384821 11459646774099283850754827)
  ·
    refine ⟨17189470161148925776132241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11459646774099283850754827 17189470161148925776132241)
    ·
      refine ⟨12892102620861694332099181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17189470161148925776132241 12892102620861694332099181)
      ·
        refine ⟨4834538482823135374537193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12892102620861694332099181 4834538482823135374537193)
        ·
          refine ⟨3625903862117351530902895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4834538482823135374537193 3625903862117351530902895)
          ·
            refine ⟨5438855793176027296354343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3625903862117351530902895 5438855793176027296354343)
            ·
              refine ⟨8158283689764040944531515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5438855793176027296354343 8158283689764040944531515)
              ·
                refine ⟨12237425534646061416797273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8158283689764040944531515 12237425534646061416797273)
                ·
                  refine ⟨9178069150984546062597955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12237425534646061416797273 9178069150984546062597955)
                  ·
                    refine ⟨13767103726476819093896933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9178069150984546062597955 13767103726476819093896933)
                    ·
                      refine ⟨2581331948714403580105675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13767103726476819093896933 2581331948714403580105675)
                      ·
                        rfl

theorem cell23_5027126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_5027126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027126 prefixEnd_5027126 := by exact prefixLift 5027126
  have htrace : WordTrace (prefixWord ++ tailWord_5027126) baseStart_5027126 baseEnd_5027126 := by
    simpa [prefixWord, tailWord_5027126, baseEnd_5027126] using wordTrace_append hprefix tailTrace_5027126
  have hstable : (prefixWord ++ tailWord_5027126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027126).length < 2 ^ (prefixWord ++ tailWord_5027126).sum := by decide
  have hdescent : baseEnd_5027126 < baseStart_5027126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027128 : List Nat := [2, 1, 2, 1, 3, 1, 1, 6, 1, 5]
def baseStart_5027128 : Nat := 118140960795 + 5027128 * 2 ^ 59
def prefixEnd_5027128 : Nat := 4983230072969 + 3 ^ 40 * 5027128 * 2
def baseEnd_5027128 : Nat := 860444325225237524093555

theorem tailTrace_5027128 : CollatzResearch.WordTrace tailWord_5027128 prefixEnd_5027128 860444325225237524093555 := by
  unfold tailWord_5027128
  simp only [CollatzResearch.WordTrace]
  refine ⟨91677210665790647976825019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122236280887720863969100025 91677210665790647976825019)
  ·
    refine ⟨137515815998685971965237529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91677210665790647976825019 137515815998685971965237529)
    ·
      refine ⟨103136861999014478973928147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137515815998685971965237529 103136861999014478973928147)
      ·
        refine ⟨154705292998521718460892221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103136861999014478973928147 154705292998521718460892221)
        ·
          refine ⟨58014484874445644422834583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154705292998521718460892221 58014484874445644422834583)
          ·
            refine ⟨87021727311668466634251875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58014484874445644422834583 87021727311668466634251875)
            ·
              refine ⟨130532590967502699951377813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87021727311668466634251875 130532590967502699951377813)
              ·
                refine ⟨6118715201601689060220835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 130532590967502699951377813 6118715201601689060220835)
                ·
                  refine ⟨9178072802402533590331253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6118715201601689060220835 9178072802402533590331253)
                  ·
                    refine ⟨860444325225237524093555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9178072802402533590331253 860444325225237524093555)
                    ·
                      rfl

theorem cell23_5027128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 1, 5].length) (baseStart_5027128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027128 prefixEnd_5027128 := by exact prefixLift 5027128
  have htrace : WordTrace (prefixWord ++ tailWord_5027128) baseStart_5027128 baseEnd_5027128 := by
    simpa [prefixWord, tailWord_5027128, baseEnd_5027128] using wordTrace_append hprefix tailTrace_5027128
  have hstable : (prefixWord ++ tailWord_5027128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027128).length < 2 ^ (prefixWord ++ tailWord_5027128).sum := by decide
  have hdescent : baseEnd_5027128 < baseStart_5027128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027129 : List Nat := [1, 2, 1, 6, 3, 1, 1, 1, 2, 2, 3]
def baseStart_5027129 : Nat := 118140960795 + 5027129 * 2 ^ 59
def prefixEnd_5027129 : Nat := 4983230072969 + 3 ^ 40 * 5027129 * 2
def baseEnd_5027129 : Nat := 2581333489156367068368161

theorem tailTrace_5027129 : CollatzResearch.WordTrace tailWord_5027129 prefixEnd_5027129 2581333489156367068368161 := by
  unfold tailWord_5027129
  simp only [CollatzResearch.WordTrace]
  refine ⟨183354457804577673124436441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122236305203051782082957627 183354457804577673124436441)
  ·
    refine ⟨137515843353433254843327331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183354457804577673124436441 137515843353433254843327331)
    ·
      refine ⟨206273765030149882264990997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137515843353433254843327331 206273765030149882264990997)
      ·
        refine ⟨9669082735788275731171453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 206273765030149882264990997 9669082735788275731171453)
        ·
          refine ⟨3625906025920603399189295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9669082735788275731171453 3625906025920603399189295)
          ·
            refine ⟨5438859038880905098783943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3625906025920603399189295 5438859038880905098783943)
            ·
              refine ⟨8158288558321357648175915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5438859038880905098783943 8158288558321357648175915)
              ·
                refine ⟨12237432837482036472263873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8158288558321357648175915 12237432837482036472263873)
                ·
                  refine ⟨9178074628111527354197905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12237432837482036472263873 9178074628111527354197905)
                  ·
                    refine ⟨6883555971083645515648429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9178074628111527354197905 6883555971083645515648429)
                    ·
                      refine ⟨2581333489156367068368161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6883555971083645515648429 2581333489156367068368161)
                      ·
                        rfl

theorem cell23_5027129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_5027129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027129 prefixEnd_5027129 := by exact prefixLift 5027129
  have htrace : WordTrace (prefixWord ++ tailWord_5027129) baseStart_5027129 baseEnd_5027129 := by
    simpa [prefixWord, tailWord_5027129, baseEnd_5027129] using wordTrace_append hprefix tailTrace_5027129
  have hstable : (prefixWord ++ tailWord_5027129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027129).length < 2 ^ (prefixWord ++ tailWord_5027129).sum := by decide
  have hdescent : baseEnd_5027129 < baseStart_5027129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027135 : List Nat := [1, 1, 2, 2, 4, 3, 1, 1, 1, 5, 2]
def baseStart_5027135 : Nat := 118140960795 + 5027135 * 2 ^ 59
def prefixEnd_5027135 : Nat := 4983230072969 + 3 ^ 40 * 5027135 * 2
def baseEnd_5027135 : Nat := 2581336570040294044893133

theorem tailTrace_5027135 : CollatzResearch.WordTrace tailWord_5027135 prefixEnd_5027135 2581336570040294044893133 := by
  unfold tailWord_5027135
  simp only [CollatzResearch.WordTrace]
  refine ⟨183354676642555936149154859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122236451095037290766103239 183354676642555936149154859)
  ·
    refine ⟨275032014963833904223732289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183354676642555936149154859 275032014963833904223732289)
    ·
      refine ⟨206274011222875428167799217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275032014963833904223732289 206274011222875428167799217)
      ·
        refine ⟨154705508417156571125849413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206274011222875428167799217 154705508417156571125849413)
        ·
          refine ⟨29007282828216857086096765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154705508417156571125849413 29007282828216857086096765)
          ·
            refine ⟨10877731060581321407286287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29007282828216857086096765 10877731060581321407286287)
            ·
              refine ⟨16316596590871982110929431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10877731060581321407286287 16316596590871982110929431)
              ·
                refine ⟨24474894886307973166394147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16316596590871982110929431 24474894886307973166394147)
                ·
                  refine ⟨36712342329461959749591221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24474894886307973166394147 36712342329461959749591221)
                  ·
                    refine ⟨3441782093387058726524177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36712342329461959749591221 3441782093387058726524177)
                    ·
                      refine ⟨2581336570040294044893133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3441782093387058726524177 2581336570040294044893133)
                      ·
                        rfl

theorem cell23_5027135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 5, 2].length) (baseStart_5027135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027135 prefixEnd_5027135 := by exact prefixLift 5027135
  have htrace : WordTrace (prefixWord ++ tailWord_5027135) baseStart_5027135 baseEnd_5027135 := by
    simpa [prefixWord, tailWord_5027135, baseEnd_5027135] using wordTrace_append hprefix tailTrace_5027135
  have hstable : (prefixWord ++ tailWord_5027135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027135).length < 2 ^ (prefixWord ++ tailWord_5027135).sum := by decide
  have hdescent : baseEnd_5027135 < baseStart_5027135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027145 : List Nat := [1, 2, 1, 1, 2, 3, 6, 1, 1, 5]
def baseStart_5027145 : Nat := 118140960795 + 5027145 * 2 ^ 59
def prefixEnd_5027145 : Nat := 4983230072969 + 3 ^ 40 * 5027145 * 2
def baseEnd_5027145 : Nat := 860447234948946335256029

theorem tailTrace_5027145 : CollatzResearch.WordTrace tailWord_5027145 prefixEnd_5027145 860447234948946335256029 := by
  unfold tailWord_5027145
  simp only [CollatzResearch.WordTrace]
  refine ⟨183355041372519707857018889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122236694248346471904679259 183355041372519707857018889)
  ·
    refine ⟨137516281029389780892764167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183355041372519707857018889 137516281029389780892764167)
    ·
      refine ⟨206274421544084671339146251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137516281029389780892764167 206274421544084671339146251)
      ·
        refine ⟨309411632316127007008719377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206274421544084671339146251 309411632316127007008719377)
        ·
          refine ⟨232058724237095255256539533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309411632316127007008719377 232058724237095255256539533)
          ·
            refine ⟨87022021588910720721202325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232058724237095255256539533 87022021588910720721202325)
            ·
              refine ⟨4079157261980190033806359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 87022021588910720721202325 4079157261980190033806359)
              ·
                refine ⟨6118735892970285050709539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4079157261980190033806359 6118735892970285050709539)
                ·
                  refine ⟨9178103839455427576064309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6118735892970285050709539 9178103839455427576064309)
                  ·
                    refine ⟨860447234948946335256029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9178103839455427576064309 860447234948946335256029)
                    ·
                      rfl

theorem cell23_5027145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 1, 1, 5].length) (baseStart_5027145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027145 prefixEnd_5027145 := by exact prefixLift 5027145
  have htrace : WordTrace (prefixWord ++ tailWord_5027145) baseStart_5027145 baseEnd_5027145 := by
    simpa [prefixWord, tailWord_5027145, baseEnd_5027145] using wordTrace_append hprefix tailTrace_5027145
  have hstable : (prefixWord ++ tailWord_5027145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027145).length < 2 ^ (prefixWord ++ tailWord_5027145).sum := by decide
  have hdescent : baseEnd_5027145 < baseStart_5027145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027149 : List Nat := [1, 6, 1, 3, 1, 2, 1, 2, 6]
def baseStart_5027149 : Nat := 118140960795 + 5027149 * 2 ^ 59
def prefixEnd_5027149 : Nat := 4983230072969 + 3 ^ 40 * 5027149 * 2
def baseEnd_5027149 : Nat := 286815973196606332235341

theorem tailTrace_5027149 : CollatzResearch.WordTrace tailWord_5027149 prefixEnd_5027149 286815973196606332235341 := by
  unfold tailWord_5027149
  simp only [CollatzResearch.WordTrace]
  refine ⟨183355187264505216540164501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122236791509670144360109667 183355187264505216540164501)
  ·
    refine ⟨8594774403023682025320211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 183355187264505216540164501 8594774403023682025320211)
    ·
      refine ⟨12892161604535523037980317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8594774403023682025320211 12892161604535523037980317)
      ·
        refine ⟨4834560601700821139242619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12892161604535523037980317 4834560601700821139242619)
        ·
          refine ⟨7251840902551231708863929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4834560601700821139242619 7251840902551231708863929)
          ·
            refine ⟨5438880676913423781647947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7251840902551231708863929 5438880676913423781647947)
            ·
              refine ⟨8158321015370135672471921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5438880676913423781647947 8158321015370135672471921)
              ·
                refine ⟨6118740761527601754353941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8158321015370135672471921 6118740761527601754353941)
                ·
                  refine ⟨286815973196606332235341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6118740761527601754353941 286815973196606332235341)
                  ·
                    rfl

theorem cell23_5027149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_5027149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027149 prefixEnd_5027149 := by exact prefixLift 5027149
  have htrace : WordTrace (prefixWord ++ tailWord_5027149) baseStart_5027149 baseEnd_5027149 := by
    simpa [prefixWord, tailWord_5027149, baseEnd_5027149] using wordTrace_append hprefix tailTrace_5027149
  have hstable : (prefixWord ++ tailWord_5027149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027149).length < 2 ^ (prefixWord ++ tailWord_5027149).sum := by decide
  have hdescent : baseEnd_5027149 < baseStart_5027149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027168 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 5]
def baseStart_5027168 : Nat := 118140960795 + 5027168 * 2 ^ 59
def prefixEnd_5027168 : Nat := 4983230072969 + 3 ^ 40 * 5027168 * 2
def baseEnd_5027168 : Nat := 2581353514901892415780481

theorem tailTrace_5027168 : CollatzResearch.WordTrace tailWord_5027168 prefixEnd_5027168 2581353514901892415780481 := by
  unfold tailWord_5027168
  simp only [CollatzResearch.WordTrace]
  refine ⟨91677940125718191392553079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122237253500957588523404105 91677940125718191392553079)
  ·
    refine ⟨137516910188577287088829619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91677940125718191392553079 137516910188577287088829619)
    ·
      refine ⟨206275365282865930633244429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137516910188577287088829619 206275365282865930633244429)
      ·
        refine ⟨77353261981074723987466661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206275365282865930633244429 77353261981074723987466661)
        ·
          refine ⟨14503736621451510747649999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77353261981074723987466661 14503736621451510747649999)
          ·
            refine ⟨21755604932177266121474999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14503736621451510747649999 21755604932177266121474999)
            ·
              refine ⟨32633407398265899182212499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21755604932177266121474999 32633407398265899182212499)
              ·
                refine ⟨48950111097398848773318749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32633407398265899182212499 48950111097398848773318749)
                ·
                  refine ⟨18356291661524568289994531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48950111097398848773318749 18356291661524568289994531)
                  ·
                    refine ⟨27534437492286852434991797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18356291661524568289994531 27534437492286852434991797)
                    ·
                      refine ⟨2581353514901892415780481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27534437492286852434991797 2581353514901892415780481)
                      ·
                        rfl

theorem cell23_5027168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_5027168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027168 prefixEnd_5027168 := by exact prefixLift 5027168
  have htrace : WordTrace (prefixWord ++ tailWord_5027168) baseStart_5027168 baseEnd_5027168 := by
    simpa [prefixWord, tailWord_5027168, baseEnd_5027168] using wordTrace_append hprefix tailTrace_5027168
  have hstable : (prefixWord ++ tailWord_5027168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027168).length < 2 ^ (prefixWord ++ tailWord_5027168).sum := by decide
  have hdescent : baseEnd_5027168 < baseStart_5027168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027185 : List Nat := [1, 2, 2, 2, 1, 2, 3, 4, 1, 2, 3]
def baseStart_5027185 : Nat := 118140960795 + 5027185 * 2 ^ 59
def prefixEnd_5027185 : Nat := 4983230072969 + 3 ^ 40 * 5027185 * 2
def baseEnd_5027185 : Nat := 2581362244073018849267903

theorem tailTrace_5027185 : CollatzResearch.WordTrace tailWord_5027185 prefixEnd_5027185 2581362244073018849267903 := by
  unfold tailWord_5027185
  simp only [CollatzResearch.WordTrace]
  refine ⟨183356500292374794688475009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122237666861583196458983339 183356500292374794688475009)
  ·
    refine ⟨137517375219281096016356257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183356500292374794688475009 137517375219281096016356257)
    ·
      refine ⟨103138031414460822012267193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137517375219281096016356257 103138031414460822012267193)
      ·
        refine ⟨77353523560845616509200395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103138031414460822012267193 77353523560845616509200395)
        ·
          refine ⟨116030285341268424763800593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77353523560845616509200395 116030285341268424763800593)
          ·
            refine ⟨87022714005951318572850445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116030285341268424763800593 87022714005951318572850445)
            ·
              refine ⟨32633517752231744464818917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87022714005951318572850445 32633517752231744464818917)
              ·
                refine ⟨6118784578543452087153547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32633517752231744464818917 6118784578543452087153547)
                ·
                  refine ⟨9178176867815178130730321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6118784578543452087153547 9178176867815178130730321)
                  ·
                    refine ⟨6883632650861383598047741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9178176867815178130730321 6883632650861383598047741)
                    ·
                      refine ⟨2581362244073018849267903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6883632650861383598047741 2581362244073018849267903)
                      ·
                        rfl

theorem cell23_5027185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_5027185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027185 prefixEnd_5027185 := by exact prefixLift 5027185
  have htrace : WordTrace (prefixWord ++ tailWord_5027185) baseStart_5027185 baseEnd_5027185 := by
    simpa [prefixWord, tailWord_5027185, baseEnd_5027185] using wordTrace_append hprefix tailTrace_5027185
  have hstable : (prefixWord ++ tailWord_5027185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027185).length < 2 ^ (prefixWord ++ tailWord_5027185).sum := by decide
  have hdescent : baseEnd_5027185 < baseStart_5027185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027202 : List Nat := [3, 4, 2, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_5027202 : Nat := 118140960795 + 5027202 * 2 ^ 59
def prefixEnd_5027202 : Nat := 4983230072969 + 3 ^ 40 * 5027202 * 2
def baseEnd_5027202 : Nat := 2581370973244145282755325

theorem tailTrace_5027202 : CollatzResearch.WordTrace tailWord_5027202 prefixEnd_5027202 2581370973244145282755325 := by
  unfold tailWord_5027202
  simp only [CollatzResearch.WordTrace]
  refine ⟨45839280083328301647960965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122238080222208804394562573 45839280083328301647960965)
  ·
    refine ⟨8594865015624056558992681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45839280083328301647960965 8594865015624056558992681)
    ·
      refine ⟨6446148761718042419244511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8594865015624056558992681 6446148761718042419244511)
      ·
        refine ⟨9669223142577063628866767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6446148761718042419244511 9669223142577063628866767)
        ·
          refine ⟨14503834713865595443300151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9669223142577063628866767 14503834713865595443300151)
          ·
            refine ⟨21755752070798393164950227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14503834713865595443300151 21755752070798393164950227)
            ·
              refine ⟨32633628106197589747425341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21755752070798393164950227 32633628106197589747425341)
              ·
                refine ⟨12237610539824096155284503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32633628106197589747425341 12237610539824096155284503)
                ·
                  refine ⟨18356415809736144232926755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12237610539824096155284503 18356415809736144232926755)
                  ·
                    refine ⟨27534623714604216349390133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18356415809736144232926755 27534623714604216349390133)
                    ·
                      refine ⟨2581370973244145282755325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27534623714604216349390133 2581370973244145282755325)
                      ·
                        rfl

theorem cell23_5027202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_5027202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027202 prefixEnd_5027202 := by exact prefixLift 5027202
  have htrace : WordTrace (prefixWord ++ tailWord_5027202) baseStart_5027202 baseEnd_5027202 := by
    simpa [prefixWord, tailWord_5027202, baseEnd_5027202] using wordTrace_append hprefix tailTrace_5027202
  have hstable : (prefixWord ++ tailWord_5027202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027202).length < 2 ^ (prefixWord ++ tailWord_5027202).sum := by decide
  have hdescent : baseEnd_5027202 < baseStart_5027202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027232 : List Nat := [2, 1, 1, 4, 1, 2, 3, 3, 2, 1, 3]
def baseStart_5027232 : Nat := 118140960795 + 5027232 * 2 ^ 59
def prefixEnd_5027232 : Nat := 4983230072969 + 3 ^ 40 * 5027232 * 2
def baseEnd_5027232 : Nat := 2581386377663780165380187

theorem tailTrace_5027232 : CollatzResearch.WordTrace tailWord_5027232 prefixEnd_5027232 2581386377663780165380187 := by
  unfold tailWord_5027232
  simp only [CollatzResearch.WordTrace]
  refine ⟨91679107261602260857717975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122238809682136347810290633 91679107261602260857717975)
  ·
    refine ⟨137518660892403391286576963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91679107261602260857717975 137518660892403391286576963)
    ·
      refine ⟨206277991338605086929865445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137518660892403391286576963 206277991338605086929865445)
      ·
        refine ⟨38677123375988453799349771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 206277991338605086929865445 38677123375988453799349771)
        ·
          refine ⟨58015685063982680699024657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38677123375988453799349771 58015685063982680699024657)
          ·
            refine ⟨43511763797987010524268493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58015685063982680699024657 43511763797987010524268493)
            ·
              refine ⟨16316911424245128946600685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43511763797987010524268493 16316911424245128946600685)
              ·
                refine ⟨6118841784091923354975257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16316911424245128946600685 6118841784091923354975257)
                ·
                  refine ⟨4589131338068942516231443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6118841784091923354975257 4589131338068942516231443)
                  ·
                    refine ⟨6883697007103413774347165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4589131338068942516231443 6883697007103413774347165)
                    ·
                      refine ⟨2581386377663780165380187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6883697007103413774347165 2581386377663780165380187)
                      ·
                        rfl

theorem cell23_5027232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_5027232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027232 prefixEnd_5027232 := by exact prefixLift 5027232
  have htrace : WordTrace (prefixWord ++ tailWord_5027232) baseStart_5027232 baseEnd_5027232 := by
    simpa [prefixWord, tailWord_5027232, baseEnd_5027232] using wordTrace_append hprefix tailTrace_5027232
  have hstable : (prefixWord ++ tailWord_5027232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027232).length < 2 ^ (prefixWord ++ tailWord_5027232).sum := by decide
  have hdescent : baseEnd_5027232 < baseStart_5027232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027285 : List Nat := [1, 3, 2, 3, 1, 1, 3, 1, 2, 2, 4]
def baseStart_5027285 : Nat := 118140960795 + 5027285 * 2 ^ 59
def prefixEnd_5027285 : Nat := 4983230072969 + 3 ^ 40 * 5027285 * 2
def baseEnd_5027285 : Nat := 2581413592138468458017443

theorem tailTrace_5027285 : CollatzResearch.WordTrace tailWord_5027285 prefixEnd_5027285 2581413592138468458017443 := by
  unfold tailWord_5027285
  simp only [CollatzResearch.WordTrace]
  refine ⟨183360147592012511767115309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122240098394675007844743539 183360147592012511767115309)
  ·
    refine ⟨68760055347004691912668241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183360147592012511767115309 68760055347004691912668241)
    ·
      refine ⟨51570041510253518934501181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68760055347004691912668241 51570041510253518934501181)
      ·
        refine ⟨19338765566345069600437943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51570041510253518934501181 19338765566345069600437943)
        ·
          refine ⟨29008148349517604400656915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19338765566345069600437943 29008148349517604400656915)
          ·
            refine ⟨43512222524276406600985373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29008148349517604400656915 43512222524276406600985373)
            ·
              refine ⟨16317083446603652475369515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43512222524276406600985373 16317083446603652475369515)
              ·
                refine ⟨24475625169905478713054273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16317083446603652475369515 24475625169905478713054273)
                ·
                  refine ⟨18356718877429109034790705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24475625169905478713054273 18356718877429109034790705)
                  ·
                    refine ⟨13767539158071831776093029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18356718877429109034790705 13767539158071831776093029)
                    ·
                      refine ⟨2581413592138468458017443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13767539158071831776093029 2581413592138468458017443)
                      ·
                        rfl

theorem cell23_5027285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_5027285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027285 prefixEnd_5027285 := by exact prefixLift 5027285
  have htrace : WordTrace (prefixWord ++ tailWord_5027285) baseStart_5027285 baseEnd_5027285 := by
    simpa [prefixWord, tailWord_5027285, baseEnd_5027285] using wordTrace_append hprefix tailTrace_5027285
  have hstable : (prefixWord ++ tailWord_5027285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027285).length < 2 ^ (prefixWord ++ tailWord_5027285).sum := by decide
  have hdescent : baseEnd_5027285 < baseStart_5027285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027289 : List Nat := [1, 2, 1, 2, 4, 2, 2, 3, 2, 2, 2]
def baseStart_5027289 : Nat := 118140960795 + 5027289 * 2 ^ 59
def prefixEnd_5027289 : Nat := 4983230072969 + 3 ^ 40 * 5027289 * 2
def baseEnd_5027289 : Nat := 2581415646061086442367425

theorem tailTrace_5027289 : CollatzResearch.WordTrace tailWord_5027289 prefixEnd_5027289 2581415646061086442367425 := by
  unfold tailWord_5027289
  simp only [CollatzResearch.WordTrace]
  refine ⟨183360293483998020450260921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122240195655998680300173947 183360293483998020450260921)
  ·
    refine ⟨137520220112998515337695691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183360293483998020450260921 137520220112998515337695691)
    ·
      refine ⟨206280330169497773006543537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137520220112998515337695691 206280330169497773006543537)
      ·
        refine ⟨154710247627123329754907653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206280330169497773006543537 154710247627123329754907653)
        ·
          refine ⟨29008171430085624329045185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154710247627123329754907653 29008171430085624329045185)
          ·
            refine ⟨21756128572564218246783889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29008171430085624329045185 21756128572564218246783889)
            ·
              refine ⟨16317096429423163685087917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21756128572564218246783889 16317096429423163685087917)
              ·
                refine ⟨6118911161033686381907969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16317096429423163685087917 6118911161033686381907969)
                ·
                  refine ⟨4589183370775264786430977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6118911161033686381907969 4589183370775264786430977)
                  ·
                    refine ⟨3441887528081448589823233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4589183370775264786430977 3441887528081448589823233)
                    ·
                      refine ⟨2581415646061086442367425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3441887528081448589823233 2581415646061086442367425)
                      ·
                        rfl

theorem cell23_5027289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 2, 2, 2].length) (baseStart_5027289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027289 prefixEnd_5027289 := by exact prefixLift 5027289
  have htrace : WordTrace (prefixWord ++ tailWord_5027289) baseStart_5027289 baseEnd_5027289 := by
    simpa [prefixWord, tailWord_5027289, baseEnd_5027289] using wordTrace_append hprefix tailTrace_5027289
  have hstable : (prefixWord ++ tailWord_5027289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027289).length < 2 ^ (prefixWord ++ tailWord_5027289).sum := by decide
  have hdescent : baseEnd_5027289 < baseStart_5027289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027312 : List Nat := [2, 1, 1, 1, 3, 5, 2, 3, 5]
def baseStart_5027312 : Nat := 118140960795 + 5027312 * 2 ^ 59
def prefixEnd_5027312 : Nat := 4983230072969 + 3 ^ 40 * 5027312 * 2
def baseEnd_5027312 : Nat := 286825272901793316931091

theorem tailTrace_5027312 : CollatzResearch.WordTrace tailWord_5027312 prefixEnd_5027312 286825272901793316931091 := by
  unfold tailWord_5027312
  simp only [CollatzResearch.WordTrace]
  refine ⟨91680566181457347689174095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122240754908609796918898793 91680566181457347689174095)
  ·
    refine ⟨137520849272186021533761143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91680566181457347689174095 137520849272186021533761143)
    ·
      refine ⟨206281273908279032300641715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137520849272186021533761143 206281273908279032300641715)
      ·
        refine ⟨309421910862418548450962573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206281273908279032300641715 309421910862418548450962573)
        ·
          refine ⟨116033216573406955669110965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 309421910862418548450962573 116033216573406955669110965)
          ·
            refine ⟨10878114053756902093979153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 116033216573406955669110965 10878114053756902093979153)
            ·
              refine ⟨8158585540317676570484365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10878114053756902093979153 8158585540317676570484365)
              ·
                refine ⟨3059469577619128713931637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8158585540317676570484365 3059469577619128713931637)
                ·
                  refine ⟨286825272901793316931091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3059469577619128713931637 286825272901793316931091)
                  ·
                    rfl

theorem cell23_5027312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 3, 5].length) (baseStart_5027312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027312 prefixEnd_5027312 := by exact prefixLift 5027312
  have htrace : WordTrace (prefixWord ++ tailWord_5027312) baseStart_5027312 baseEnd_5027312 := by
    simpa [prefixWord, tailWord_5027312, baseEnd_5027312] using wordTrace_append hprefix tailTrace_5027312
  have hstable : (prefixWord ++ tailWord_5027312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027312).length < 2 ^ (prefixWord ++ tailWord_5027312).sum := by decide
  have hdescent : baseEnd_5027312 < baseStart_5027312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027315 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 1, 7, 2]
def baseStart_5027315 : Nat := 118140960795 + 5027315 * 2 ^ 59
def prefixEnd_5027315 : Nat := 4983230072969 + 3 ^ 40 * 5027315 * 2
def baseEnd_5027315 : Nat := 2581428996558103340642305

theorem tailTrace_5027315 : CollatzResearch.WordTrace tailWord_5027315 prefixEnd_5027315 2581428996558103340642305 := by
  unfold tailWord_5027315
  simp only [CollatzResearch.WordTrace]
  refine ⟨183361241781903826890707399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122240827854602551260471599 183361241781903826890707399)
  ·
    refine ⟨275041862672855740336061099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183361241781903826890707399 275041862672855740336061099)
    ·
      refine ⟨412562794009283610504091649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275041862672855740336061099 412562794009283610504091649)
      ·
        refine ⟨309422095506962707878068737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412562794009283610504091649 309422095506962707878068737)
        ·
          refine ⟨232066571630222030908551553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309422095506962707878068737 232066571630222030908551553)
          ·
            refine ⟨174049928722666523181413665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232066571630222030908551553 174049928722666523181413665)
            ·
              refine ⟨130537446541999892386060249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174049928722666523181413665 130537446541999892386060249)
              ·
                refine ⟨97903084906499919289545187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130537446541999892386060249 97903084906499919289545187)
                ·
                  refine ⟨146854627359749878934317781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97903084906499919289545187 146854627359749878934317781)
                  ·
                    refine ⟨3441905328744137787523073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 146854627359749878934317781 3441905328744137787523073)
                    ·
                      refine ⟨2581428996558103340642305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3441905328744137787523073 2581428996558103340642305)
                      ·
                        rfl

theorem cell23_5027315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 7, 2].length) (baseStart_5027315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027315 prefixEnd_5027315 := by exact prefixLift 5027315
  have htrace : WordTrace (prefixWord ++ tailWord_5027315) baseStart_5027315 baseEnd_5027315 := by
    simpa [prefixWord, tailWord_5027315, baseEnd_5027315] using wordTrace_append hprefix tailTrace_5027315
  have hstable : (prefixWord ++ tailWord_5027315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027315).length < 2 ^ (prefixWord ++ tailWord_5027315).sum := by decide
  have hdescent : baseEnd_5027315 < baseStart_5027315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027362 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 1, 6, 2]
def baseStart_5027362 : Nat := 118140960795 + 5027362 * 2 ^ 59
def prefixEnd_5027362 : Nat := 4983230072969 + 3 ^ 40 * 5027362 * 2
def baseEnd_5027362 : Nat := 2581453130148864656754589

theorem tailTrace_5027362 : CollatzResearch.WordTrace tailWord_5027362 prefixEnd_5027362 2581453130148864656754589 := by
  unfold tailWord_5027362
  simp only [CollatzResearch.WordTrace]
  refine ⟨45840739003183388479417085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122241970675155702611778893 45840739003183388479417085)
  ·
    refine ⟨17190277126193770679781407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45840739003183388479417085 17190277126193770679781407)
    ·
      refine ⟨25785415689290656019672111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17190277126193770679781407 25785415689290656019672111)
      ·
        refine ⟨38678123533935984029508167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25785415689290656019672111 38678123533935984029508167)
        ·
          refine ⟨58017185300903976044262251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38678123533935984029508167 58017185300903976044262251)
          ·
            refine ⟨87025777951355964066393377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58017185300903976044262251 87025777951355964066393377)
            ·
              refine ⟨65269333463516973049795033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87025777951355964066393377 65269333463516973049795033)
              ·
                refine ⟨48952000097637729787346275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65269333463516973049795033 48952000097637729787346275)
                ·
                  refine ⟨73428000146456594681019413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48952000097637729787346275 73428000146456594681019413)
                  ·
                    refine ⟨3441937506865152875672785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73428000146456594681019413 3441937506865152875672785)
                    ·
                      refine ⟨2581453130148864656754589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3441937506865152875672785 2581453130148864656754589)
                      ·
                        rfl

theorem cell23_5027362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_5027362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027362 prefixEnd_5027362 := by exact prefixLift 5027362
  have htrace : WordTrace (prefixWord ++ tailWord_5027362) baseStart_5027362 baseEnd_5027362 := by
    simpa [prefixWord, tailWord_5027362, baseEnd_5027362] using wordTrace_append hprefix tailTrace_5027362
  have hstable : (prefixWord ++ tailWord_5027362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027362).length < 2 ^ (prefixWord ++ tailWord_5027362).sum := by decide
  have hdescent : baseEnd_5027362 < baseStart_5027362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027385 : List Nat := [1, 2, 1, 5, 1, 2, 2, 1, 8]
def baseStart_5027385 : Nat := 118140960795 + 5027385 * 2 ^ 59
def prefixEnd_5027385 : Nat := 4983230072969 + 3 ^ 40 * 5027385 * 2
def baseEnd_5027385 : Nat := 286829437800435340751887

theorem tailTrace_5027385 : CollatzResearch.WordTrace tailWord_5027385 prefixEnd_5027385 286829437800435340751887 := by
  unfold tailWord_5027385
  simp only [CollatzResearch.WordTrace]
  refine ⟨183363794891650228845755609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122242529927766819230503739 183363794891650228845755609)
  ·
    refine ⟨137522846168737671634316707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183363794891650228845755609 137522846168737671634316707)
    ·
      refine ⟨206284269253106507451475061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137522846168737671634316707 206284269253106507451475061)
      ·
        refine ⟨19339150242478735073575787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 206284269253106507451475061 19339150242478735073575787)
        ·
          refine ⟨29008725363718102610363681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19339150242478735073575787 29008725363718102610363681)
          ·
            refine ⟨21756544022788576957772761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29008725363718102610363681 21756544022788576957772761)
            ·
              refine ⟨16317408017091432718329571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21756544022788576957772761 16317408017091432718329571)
              ·
                refine ⟨24476112025637149077494357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16317408017091432718329571 24476112025637149077494357)
                ·
                  refine ⟨286829437800435340751887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24476112025637149077494357 286829437800435340751887)
                  ·
                    rfl

theorem cell23_5027385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 8].length) (baseStart_5027385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027385 prefixEnd_5027385 := by exact prefixLift 5027385
  have htrace : WordTrace (prefixWord ++ tailWord_5027385) baseStart_5027385 baseEnd_5027385 := by
    simpa [prefixWord, tailWord_5027385, baseEnd_5027385] using wordTrace_append hprefix tailTrace_5027385
  have hstable : (prefixWord ++ tailWord_5027385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027385).length < 2 ^ (prefixWord ++ tailWord_5027385).sum := by decide
  have hdescent : baseEnd_5027385 < baseStart_5027385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027452 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 2, 6, 2]
def baseStart_5027452 : Nat := 118140960795 + 5027452 * 2 ^ 59
def prefixEnd_5027452 : Nat := 4983230072969 + 3 ^ 40 * 5027452 * 2
def baseEnd_5027452 : Nat := 2581499343407769304629175

theorem tailTrace_5027452 : CollatzResearch.WordTrace tailWord_5027452 prefixEnd_5027452 2581499343407769304629175 := by
  unfold tailWord_5027452
  simp only [CollatzResearch.WordTrace]
  refine ⟨91683119291203749644222305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122244159054938332858963073 91683119291203749644222305)
  ·
    refine ⟨68762339468402812233166729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91683119291203749644222305 68762339468402812233166729)
    ·
      refine ⟨51571754601302109174875047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68762339468402812233166729 51571754601302109174875047)
      ·
        refine ⟨77357631901953163762312571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51571754601302109174875047 77357631901953163762312571)
        ·
          refine ⟨116036447852929745643468857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77357631901953163762312571 116036447852929745643468857)
          ·
            refine ⟨87027335889697309232601643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116036447852929745643468857 87027335889697309232601643)
            ·
              refine ⟨130541003834545963848902465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87027335889697309232601643 130541003834545963848902465)
              ·
                refine ⟨97905752875909472886676849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130541003834545963848902465 97905752875909472886676849)
                ·
                  refine ⟨73429314656932104665007637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97905752875909472886676849 73429314656932104665007637)
                  ·
                    refine ⟨3441999124543692406172233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73429314656932104665007637 3441999124543692406172233)
                    ·
                      refine ⟨2581499343407769304629175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3441999124543692406172233 2581499343407769304629175)
                      ·
                        rfl

theorem cell23_5027452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 2, 6, 2].length) (baseStart_5027452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027452 prefixEnd_5027452 := by exact prefixLift 5027452
  have htrace : WordTrace (prefixWord ++ tailWord_5027452) baseStart_5027452 baseEnd_5027452 := by
    simpa [prefixWord, tailWord_5027452, baseEnd_5027452] using wordTrace_append hprefix tailTrace_5027452
  have hstable : (prefixWord ++ tailWord_5027452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027452).length < 2 ^ (prefixWord ++ tailWord_5027452).sum := by decide
  have hdescent : baseEnd_5027452 < baseStart_5027452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027465 : List Nat := [1, 2, 1, 1, 4, 1, 2, 3, 1, 1, 6]
def baseStart_5027465 : Nat := 118140960795 + 5027465 * 2 ^ 59
def prefixEnd_5027465 : Nat := 4983230072969 + 3 ^ 40 * 5027465 * 2
def baseEnd_5027465 : Nat := 2581506018656277753766615

theorem tailTrace_5027465 : CollatzResearch.WordTrace tailWord_5027465 prefixEnd_5027465 2581506018656277753766615 := by
  unfold tailWord_5027465
  simp only [CollatzResearch.WordTrace]
  refine ⟨183366712731360402508667849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122244475154240268339111899 183366712731360402508667849)
  ·
    refine ⟨137525034548520301881500887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183366712731360402508667849 137525034548520301881500887)
    ·
      refine ⟨206287551822780452822251331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137525034548520301881500887 206287551822780452822251331)
      ·
        refine ⟨309431327734170679233376997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206287551822780452822251331 309431327734170679233376997)
        ·
          refine ⟨58018373950157002356258187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 309431327734170679233376997 58018373950157002356258187)
          ·
            refine ⟨87027560925235503534387281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58018373950157002356258187 87027560925235503534387281)
            ·
              refine ⟨65270670693926627650790461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87027560925235503534387281 65270670693926627650790461)
              ·
                refine ⟨24476501510222485369046423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65270670693926627650790461 24476501510222485369046423)
                ·
                  refine ⟨36714752265333728053569635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24476501510222485369046423 36714752265333728053569635)
                  ·
                    refine ⟨55072128398000592080354453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36714752265333728053569635 55072128398000592080354453)
                    ·
                      refine ⟨2581506018656277753766615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55072128398000592080354453 2581506018656277753766615)
                      ·
                        rfl

theorem cell23_5027465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 1, 1, 6].length) (baseStart_5027465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027465 prefixEnd_5027465 := by exact prefixLift 5027465
  have htrace : WordTrace (prefixWord ++ tailWord_5027465) baseStart_5027465 baseEnd_5027465 := by
    simpa [prefixWord, tailWord_5027465, baseEnd_5027465] using wordTrace_append hprefix tailTrace_5027465
  have hstable : (prefixWord ++ tailWord_5027465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027465).length < 2 ^ (prefixWord ++ tailWord_5027465).sum := by decide
  have hdescent : baseEnd_5027465 < baseStart_5027465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027486 : List Nat := [4, 3, 1, 1, 1, 3, 1, 3, 1, 1, 4]
def baseStart_5027486 : Nat := 118140960795 + 5027486 * 2 ^ 59
def prefixEnd_5027486 : Nat := 4983230072969 + 3 ^ 40 * 5027486 * 2
def baseEnd_5027486 : Nat := 2581516801750022171604019

theorem tailTrace_5027486 : CollatzResearch.WordTrace tailWord_5027486 prefixEnd_5027486 2581516801750022171604019 := by
  unfold tailWord_5027486
  simp only [CollatzResearch.WordTrace]
  refine ⟨22920934833035540386897789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122244985776189548730121541 22920934833035540386897789)
  ·
    refine ⟨8595350562388327645086671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22920934833035540386897789 8595350562388327645086671)
    ·
      refine ⟨12893025843582491467630007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8595350562388327645086671 12893025843582491467630007)
      ·
        refine ⟨19339538765373737201445011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12893025843582491467630007 19339538765373737201445011)
        ·
          refine ⟨29009308148060605802167517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19339538765373737201445011 29009308148060605802167517)
          ·
            refine ⟨10878490555522727175812819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29009308148060605802167517 10878490555522727175812819)
            ·
              refine ⟨16317735833284090763719229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10878490555522727175812819 16317735833284090763719229)
              ·
                refine ⟨6119150937481534036394711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16317735833284090763719229 6119150937481534036394711)
                ·
                  refine ⟨9178726406222301054592067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6119150937481534036394711 9178726406222301054592067)
                  ·
                    refine ⟨13768089609333451581888101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9178726406222301054592067 13768089609333451581888101)
                    ·
                      refine ⟨2581516801750022171604019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13768089609333451581888101 2581516801750022171604019)
                      ·
                        rfl

theorem cell23_5027486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_5027486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027486 prefixEnd_5027486 := by exact prefixLift 5027486
  have htrace : WordTrace (prefixWord ++ tailWord_5027486) baseStart_5027486 baseEnd_5027486 := by
    simpa [prefixWord, tailWord_5027486, baseEnd_5027486] using wordTrace_append hprefix tailTrace_5027486
  have hstable : (prefixWord ++ tailWord_5027486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027486).length < 2 ^ (prefixWord ++ tailWord_5027486).sum := by decide
  have hdescent : baseEnd_5027486 < baseStart_5027486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027515 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 5]
def baseStart_5027515 : Nat := 118140960795 + 5027515 * 2 ^ 59
def prefixEnd_5027515 : Nat := 4983230072969 + 3 ^ 40 * 5027515 * 2
def baseEnd_5027515 : Nat := 2581531692689002558141385

theorem tailTrace_5027515 : CollatzResearch.WordTrace tailWord_5027515 prefixEnd_5027515 2581531692689002558141385 := by
  unfold tailWord_5027515
  simp only [CollatzResearch.WordTrace]
  refine ⟨183368536381179261047987999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122245690920786174031991999 183368536381179261047987999)
  ·
    refine ⟨275052804571768891571981999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183368536381179261047987999 275052804571768891571981999)
    ·
      refine ⟨412579206857653337357972999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275052804571768891571981999 412579206857653337357972999)
      ·
        refine ⟨618868810286480006036959499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412579206857653337357972999 618868810286480006036959499)
        ·
          refine ⟨928303215429720009055439249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 618868810286480006036959499 928303215429720009055439249)
          ·
            refine ⟨696227411572290006791579437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 928303215429720009055439249 696227411572290006791579437)
            ·
              refine ⟨261085279339608752546842289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 696227411572290006791579437 261085279339608752546842289)
              ·
                refine ⟨195813959504706564410131717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 261085279339608752546842289 195813959504706564410131717)
                ·
                  refine ⟨36715117407132480826899697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 195813959504706564410131717 36715117407132480826899697)
                  ·
                    refine ⟨27536338055349360620174773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36715117407132480826899697 27536338055349360620174773)
                    ·
                      refine ⟨2581531692689002558141385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27536338055349360620174773 2581531692689002558141385)
                      ·
                        rfl

theorem cell23_5027515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 5].length) (baseStart_5027515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027515 prefixEnd_5027515 := by exact prefixLift 5027515
  have htrace : WordTrace (prefixWord ++ tailWord_5027515) baseStart_5027515 baseEnd_5027515 := by
    simpa [prefixWord, tailWord_5027515, baseEnd_5027515] using wordTrace_append hprefix tailTrace_5027515
  have hstable : (prefixWord ++ tailWord_5027515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027515).length < 2 ^ (prefixWord ++ tailWord_5027515).sum := by decide
  have hdescent : baseEnd_5027515 < baseStart_5027515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027526 : List Nat := [6, 1, 2, 1, 1, 2, 1, 9]
def baseStart_5027526 : Nat := 118140960795 + 5027526 * 2 ^ 59
def prefixEnd_5027526 : Nat := 4983230072969 + 3 ^ 40 * 5027526 * 2
def baseEnd_5027526 : Nat := 95612494110229704263105

theorem tailTrace_5027526 : CollatzResearch.WordTrace tailWord_5027526 prefixEnd_5027526 95612494110229704263105 := by
  unfold tailWord_5027526
  simp only [CollatzResearch.WordTrace]
  refine ⟨5730279299504356560207451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 122245958389426273284425621 5730279299504356560207451)
  ·
    refine ⟨8595418949256534840311177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5730279299504356560207451 8595418949256534840311177)
    ·
      refine ⟨6446564211942401130233383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8595418949256534840311177 6446564211942401130233383)
      ·
        refine ⟨9669846317913601695350075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6446564211942401130233383 9669846317913601695350075)
        ·
          refine ⟨14504769476870402543025113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9669846317913601695350075 14504769476870402543025113)
          ·
            refine ⟨10878577107652801907268835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14504769476870402543025113 10878577107652801907268835)
            ·
              refine ⟨16317865661479202860903253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10878577107652801907268835 16317865661479202860903253)
              ·
                refine ⟨95612494110229704263105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16317865661479202860903253 95612494110229704263105)
                ·
                  rfl

theorem cell23_5027526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_5027526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027526 prefixEnd_5027526 := by exact prefixLift 5027526
  have htrace : WordTrace (prefixWord ++ tailWord_5027526) baseStart_5027526 baseEnd_5027526 := by
    simpa [prefixWord, tailWord_5027526, baseEnd_5027526] using wordTrace_append hprefix tailTrace_5027526
  have hstable : (prefixWord ++ tailWord_5027526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027526).length < 2 ^ (prefixWord ++ tailWord_5027526).sum := by decide
  have hdescent : baseEnd_5027526 < baseStart_5027526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027535 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 1, 8]
def baseStart_5027535 : Nat := 118140960795 + 5027535 * 2 ^ 59
def prefixEnd_5027535 : Nat := 4983230072969 + 3 ^ 40 * 5027535 * 2
def baseEnd_5027535 : Nat := 860513987434030826630431

theorem tailTrace_5027535 : CollatzResearch.WordTrace tailWord_5027535 prefixEnd_5027535 860513987434030826630431 := by
  unfold tailWord_5027535
  simp only [CollatzResearch.WordTrace]
  refine ⟨183369265841106804463716059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122246177227404536309144039 183369265841106804463716059)
  ·
    refine ⟨275053898761660206695574089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183369265841106804463716059 275053898761660206695574089)
    ·
      refine ⟨206290424071245155021680567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275053898761660206695574089 206290424071245155021680567)
      ·
        refine ⟨309435636106867732532520851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206290424071245155021680567 309435636106867732532520851)
        ·
          refine ⟨464153454160301598798781277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309435636106867732532520851 464153454160301598798781277)
          ·
            refine ⟨174057545310113099549542979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 464153454160301598798781277 174057545310113099549542979)
            ·
              refine ⟨261086317965169649324314469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174057545310113099549542979 261086317965169649324314469)
              ·
                refine ⟨48953684618469309248308963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 261086317965169649324314469 48953684618469309248308963)
                ·
                  refine ⟨73430526927703963872463445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48953684618469309248308963 73430526927703963872463445)
                  ·
                    refine ⟨860513987434030826630431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73430526927703963872463445 860513987434030826630431)
                    ·
                      rfl

theorem cell23_5027535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 8].length) (baseStart_5027535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027535 prefixEnd_5027535 := by exact prefixLift 5027535
  have htrace : WordTrace (prefixWord ++ tailWord_5027535) baseStart_5027535 baseEnd_5027535 := by
    simpa [prefixWord, tailWord_5027535, baseEnd_5027535] using wordTrace_append hprefix tailTrace_5027535
  have hstable : (prefixWord ++ tailWord_5027535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027535).length < 2 ^ (prefixWord ++ tailWord_5027535).sum := by decide
  have hdescent : baseEnd_5027535 < baseStart_5027535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027546 : List Nat := [3, 1, 1, 2, 2, 3, 2, 3, 1, 3, 2]
def baseStart_5027546 : Nat := 118140960795 + 5027546 * 2 ^ 59
def prefixEnd_5027546 : Nat := 4983230072969 + 3 ^ 40 * 5027546 * 2
def baseEnd_5027546 : Nat := 2581547610589291936853743

theorem tailTrace_5027546 : CollatzResearch.WordTrace tailWord_5027546 prefixEnd_5027546 2581547610589291936853743 := by
  unfold tailWord_5027546
  simp only [CollatzResearch.WordTrace]
  refine ⟨45842416761016738335591623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122246444696044635561577661 45842416761016738335591623)
  ·
    refine ⟨68763625141525107503387435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45842416761016738335591623 68763625141525107503387435)
    ·
      refine ⟨103145437712287661255081153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68763625141525107503387435 103145437712287661255081153)
      ·
        refine ⟨77359078284215745941310865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103145437712287661255081153 77359078284215745941310865)
        ·
          refine ⟨58019308713161809455983149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77359078284215745941310865 58019308713161809455983149)
          ·
            refine ⟨21757240767435678545993681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58019308713161809455983149 21757240767435678545993681)
            ·
              refine ⟨16317930575576758909495261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21757240767435678545993681 16317930575576758909495261)
              ·
                refine ⟨6119223965841284591060723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16317930575576758909495261 6119223965841284591060723)
                ·
                  refine ⟨9178835948761926886591085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6119223965841284591060723 9178835948761926886591085)
                  ·
                    refine ⟨3442063480785722582471657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9178835948761926886591085 3442063480785722582471657)
                    ·
                      refine ⟨2581547610589291936853743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3442063480785722582471657 2581547610589291936853743)
                      ·
                        rfl

theorem cell23_5027546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 1, 3, 2].length) (baseStart_5027546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027546 prefixEnd_5027546 := by exact prefixLift 5027546
  have htrace : WordTrace (prefixWord ++ tailWord_5027546) baseStart_5027546 baseEnd_5027546 := by
    simpa [prefixWord, tailWord_5027546, baseEnd_5027546] using wordTrace_append hprefix tailTrace_5027546
  have hstable : (prefixWord ++ tailWord_5027546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027546).length < 2 ^ (prefixWord ++ tailWord_5027546).sum := by decide
  have hdescent : baseEnd_5027546 < baseStart_5027546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027619 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 2, 5, 2]
def baseStart_5027619 : Nat := 118140960795 + 5027619 * 2 ^ 59
def prefixEnd_5027619 : Nat := 4983230072969 + 3 ^ 40 * 5027619 * 2
def baseEnd_5027619 : Nat := 2581585094677070151240907

theorem tailTrace_5027619 : CollatzResearch.WordTrace tailWord_5027619 prefixEnd_5027619 2581585094677070151240907 := by
  unfold tailWord_5027619
  simp only [CollatzResearch.WordTrace]
  refine ⟨183372329572802486809773911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122248219715201657873182607 183372329572802486809773911)
  ·
    refine ⟨275058494359203730214660867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183372329572802486809773911 275058494359203730214660867)
    ·
      refine ⟨412587741538805595321991301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275058494359203730214660867 412587741538805595321991301)
      ·
        refine ⟨77360201538526049122873369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 412587741538805595321991301 77360201538526049122873369)
        ·
          refine ⟨58020151153894536842155027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77360201538526049122873369 58020151153894536842155027)
          ·
            refine ⟨87030226730841805263232541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58020151153894536842155027 87030226730841805263232541)
            ·
              refine ⟨32636335024065676973712203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87030226730841805263232541 32636335024065676973712203)
              ·
                refine ⟨48954502536098515460568305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32636335024065676973712203 48954502536098515460568305)
                ·
                  refine ⟨36715876902073886595426229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48954502536098515460568305 36715876902073886595426229)
                  ·
                    refine ⟨3442113459569426868321209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36715876902073886595426229 3442113459569426868321209)
                    ·
                      refine ⟨2581585094677070151240907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3442113459569426868321209 2581585094677070151240907)
                      ·
                        rfl

theorem cell23_5027619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 5, 2].length) (baseStart_5027619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027619 prefixEnd_5027619 := by exact prefixLift 5027619
  have htrace : WordTrace (prefixWord ++ tailWord_5027619) baseStart_5027619 baseEnd_5027619 := by
    simpa [prefixWord, tailWord_5027619, baseEnd_5027619] using wordTrace_append hprefix tailTrace_5027619
  have hstable : (prefixWord ++ tailWord_5027619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027619).length < 2 ^ (prefixWord ++ tailWord_5027619).sum := by decide
  have hdescent : baseEnd_5027619 < baseStart_5027619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027646 : List Nat := [4, 2, 1, 2, 2, 1, 3, 1, 2, 5]
def baseStart_5027646 : Nat := 118140960795 + 5027646 * 2 ^ 59
def prefixEnd_5027646 : Nat := 4983230072969 + 3 ^ 40 * 5027646 * 2
def baseEnd_5027646 : Nat := 860532986218247181867761

theorem tailTrace_5027646 : CollatzResearch.WordTrace tailWord_5027646 prefixEnd_5027646 860532986218247181867761 := by
  unfold tailWord_5027646
  simp only [CollatzResearch.WordTrace]
  refine ⟨22921664292963083802625849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122248876229136446947337861 22921664292963083802625849)
  ·
    refine ⟨17191248219722312851969387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22921664292963083802625849 17191248219722312851969387)
    ·
      refine ⟨25786872329583469277954081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17191248219722312851969387 25786872329583469277954081)
      ·
        refine ⟨19340154247187601958465561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25786872329583469277954081 19340154247187601958465561)
        ·
          refine ⟨14505115685390701468849171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19340154247187601958465561 14505115685390701468849171)
          ·
            refine ⟨21757673528086052203273757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14505115685390701468849171 21757673528086052203273757)
            ·
              refine ⟨8159127573032269576227659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21757673528086052203273757 8159127573032269576227659)
              ·
                refine ⟨12238691359548404364341489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8159127573032269576227659 12238691359548404364341489)
                ·
                  refine ⟨9179018519661303273256117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12238691359548404364341489 9179018519661303273256117)
                  ·
                    refine ⟨860532986218247181867761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9179018519661303273256117 860532986218247181867761)
                    ·
                      rfl

theorem cell23_5027646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_5027646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027646 prefixEnd_5027646 := by exact prefixLift 5027646
  have htrace : WordTrace (prefixWord ++ tailWord_5027646) baseStart_5027646 baseEnd_5027646 := by
    simpa [prefixWord, tailWord_5027646, baseEnd_5027646] using wordTrace_append hprefix tailTrace_5027646
  have hstable : (prefixWord ++ tailWord_5027646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027646).length < 2 ^ (prefixWord ++ tailWord_5027646).sum := by decide
  have hdescent : baseEnd_5027646 < baseStart_5027646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027666 : List Nat := [3, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2]
def baseStart_5027666 : Nat := 118140960795 + 5027666 * 2 ^ 59
def prefixEnd_5027666 : Nat := 4983230072969 + 3 ^ 40 * 5027666 * 2
def baseEnd_5027666 : Nat := 2581609228267831467353191

theorem tailTrace_5027666 : CollatzResearch.WordTrace tailWord_5027666 prefixEnd_5027666 2581609228267831467353191 := by
  unfold tailWord_5027666
  simp only [CollatzResearch.WordTrace]
  refine ⟨45843510950908053459183713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122249362535754809224489901 45843510950908053459183713)
  ·
    refine ⟨34382633213181040094387785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45843510950908053459183713 34382633213181040094387785)
    ·
      refine ⟨25786974909885780070790839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34382633213181040094387785 25786974909885780070790839)
      ·
        refine ⟨38680462364828670106186259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25786974909885780070790839 38680462364828670106186259)
        ·
          refine ⟨58020693547243005159279389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38680462364828670106186259 58020693547243005159279389)
          ·
            refine ⟨21757760080216126934729771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58020693547243005159279389 21757760080216126934729771)
            ·
              refine ⟨32636640120324190402094657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21757760080216126934729771 32636640120324190402094657)
              ·
                refine ⟨24477480090243142801570993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32636640120324190402094657 24477480090243142801570993)
                ·
                  refine ⟨18358110067682357101178245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24477480090243142801570993 18358110067682357101178245)
                  ·
                    refine ⟨3442145637690441956470921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18358110067682357101178245 3442145637690441956470921)
                    ·
                      refine ⟨2581609228267831467353191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3442145637690441956470921 2581609228267831467353191)
                      ·
                        rfl

theorem cell23_5027666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_5027666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027666 prefixEnd_5027666 := by exact prefixLift 5027666
  have htrace : WordTrace (prefixWord ++ tailWord_5027666) baseStart_5027666 baseEnd_5027666 := by
    simpa [prefixWord, tailWord_5027666, baseEnd_5027666] using wordTrace_append hprefix tailTrace_5027666
  have hstable : (prefixWord ++ tailWord_5027666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027666).length < 2 ^ (prefixWord ++ tailWord_5027666).sum := by decide
  have hdescent : baseEnd_5027666 < baseStart_5027666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027716 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 5, 1, 3]
def baseStart_5027716 : Nat := 118140960795 + 5027716 * 2 ^ 59
def prefixEnd_5027716 : Nat := 4983230072969 + 3 ^ 40 * 5027716 * 2
def baseEnd_5027716 : Nat := 2581634902300556271727961

theorem tailTrace_5027716 : CollatzResearch.WordTrace tailWord_5027716 prefixEnd_5027716 2581634902300556271727961 := by
  unfold tailWord_5027716
  simp only [CollatzResearch.WordTrace]
  refine ⟨91687933726725536188027501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122250578302300714917370001 91687933726725536188027501)
  ·
    refine ⟨34382975147522076070510313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91687933726725536188027501 34382975147522076070510313)
    ·
      refine ⟨25787231360641557052882735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34382975147522076070510313 25787231360641557052882735)
      ·
        refine ⟨38680847040962335579324103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25787231360641557052882735 38680847040962335579324103)
        ·
          refine ⟨58021270561443503368986155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38680847040962335579324103 58021270561443503368986155)
          ·
            refine ⟨87031905842165255053479233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58021270561443503368986155 87031905842165255053479233)
            ·
              refine ⟨65273929381623941290109425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87031905842165255053479233 65273929381623941290109425)
              ·
                refine ⟨48955447036217955967582069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65273929381623941290109425 48955447036217955967582069)
                ·
                  refine ⟨4589573159645433371960819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48955447036217955967582069 4589573159645433371960819)
                  ·
                    refine ⟨6884359739468150057941229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4589573159645433371960819 6884359739468150057941229)
                    ·
                      refine ⟨2581634902300556271727961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6884359739468150057941229 2581634902300556271727961)
                      ·
                        rfl

theorem cell23_5027716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_5027716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027716 prefixEnd_5027716 := by exact prefixLift 5027716
  have htrace : WordTrace (prefixWord ++ tailWord_5027716) baseStart_5027716 baseEnd_5027716 := by
    simpa [prefixWord, tailWord_5027716, baseEnd_5027716] using wordTrace_append hprefix tailTrace_5027716
  have hstable : (prefixWord ++ tailWord_5027716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027716).length < 2 ^ (prefixWord ++ tailWord_5027716).sum := by decide
  have hdescent : baseEnd_5027716 < baseStart_5027716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027849 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 6, 1, 5]
def baseStart_5027849 : Nat := 118140960795 + 5027849 * 2 ^ 59
def prefixEnd_5027849 : Nat := 4983230072969 + 3 ^ 40 * 5027849 * 2
def baseEnd_5027849 : Nat := 2581703195227604251364849

theorem tailTrace_5027849 : CollatzResearch.WordTrace tailWord_5027849 prefixEnd_5027849 2581703195227604251364849 := by
  unfold tailWord_5027849
  simp only [CollatzResearch.WordTrace]
  refine ⟨183380718361969236090646601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122253812241312824060431067 183380718361969236090646601)
  ·
    refine ⟨137535538771476927067984951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183380718361969236090646601 137535538771476927067984951)
    ·
      refine ⟨206303308157215390601977427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137535538771476927067984951 206303308157215390601977427)
      ·
        refine ⟨309454962235823085902966141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206303308157215390601977427 309454962235823085902966141)
        ·
          refine ⟨116045610838433657213612303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 309454962235823085902966141 116045610838433657213612303)
          ·
            refine ⟨174068416257650485820418455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116045610838433657213612303 174068416257650485820418455)
            ·
              refine ⟨261102624386475728730627683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174068416257650485820418455 261102624386475728730627683)
              ·
                refine ⟨391653936579713593095941525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261102624386475728730627683 391653936579713593095941525)
                ·
                  refine ⟨18358778277174074676372259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 391653936579713593095941525 18358778277174074676372259)
                  ·
                    refine ⟨27538167415761112014558389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18358778277174074676372259 27538167415761112014558389)
                    ·
                      refine ⟨2581703195227604251364849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27538167415761112014558389 2581703195227604251364849)
                      ·
                        rfl

theorem cell23_5027849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 1, 5].length) (baseStart_5027849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027849 prefixEnd_5027849 := by exact prefixLift 5027849
  have htrace : WordTrace (prefixWord ++ tailWord_5027849) baseStart_5027849 baseEnd_5027849 := by
    simpa [prefixWord, tailWord_5027849, baseEnd_5027849] using wordTrace_append hprefix tailTrace_5027849
  have hstable : (prefixWord ++ tailWord_5027849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027849).length < 2 ^ (prefixWord ++ tailWord_5027849).sum := by decide
  have hdescent : baseEnd_5027849 < baseStart_5027849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027953 : List Nat := [1, 2, 2, 2, 1, 1, 4, 2, 2, 4, 2]
def baseStart_5027953 : Nat := 118140960795 + 5027953 * 2 ^ 59
def prefixEnd_5027953 : Nat := 4983230072969 + 3 ^ 40 * 5027953 * 2
def baseEnd_5027953 : Nat := 2581756597215671844464371

theorem tailTrace_5027953 : CollatzResearch.WordTrace tailWord_5027953 prefixEnd_5027953 2581756597215671844464371 := by
  unfold tailWord_5027953
  simp only [CollatzResearch.WordTrace]
  refine ⟨183384511553592461852432513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122256341035728307901621675 183384511553592461852432513)
  ·
    refine ⟨137538383665194346389324385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183384511553592461852432513 137538383665194346389324385)
    ·
      refine ⟨103153787748895759791993289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137538383665194346389324385 103153787748895759791993289)
      ·
        refine ⟨77365340811671819843994967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103153787748895759791993289 77365340811671819843994967)
        ·
          refine ⟨116048011217507729765992451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77365340811671819843994967 116048011217507729765992451)
          ·
            refine ⟨174072016826261594648988677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116048011217507729765992451 174072016826261594648988677)
            ·
              refine ⟨32638503154924048996685377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 174072016826261594648988677 32638503154924048996685377)
              ·
                refine ⟨24478877366193036747514033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32638503154924048996685377 24478877366193036747514033)
                ·
                  refine ⟨18359158024644777560635525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24478877366193036747514033 18359158024644777560635525)
                  ·
                    refine ⟨3442342129620895792619161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18359158024644777560635525 3442342129620895792619161)
                    ·
                      refine ⟨2581756597215671844464371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3442342129620895792619161 2581756597215671844464371)
                      ·
                        rfl

theorem cell23_5027953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 4, 2].length) (baseStart_5027953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027953 prefixEnd_5027953 := by exact prefixLift 5027953
  have htrace : WordTrace (prefixWord ++ tailWord_5027953) baseStart_5027953 baseEnd_5027953 := by
    simpa [prefixWord, tailWord_5027953, baseEnd_5027953] using wordTrace_append hprefix tailTrace_5027953
  have hstable : (prefixWord ++ tailWord_5027953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027953).length < 2 ^ (prefixWord ++ tailWord_5027953).sum := by decide
  have hdescent : baseEnd_5027953 < baseStart_5027953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5027997 : List Nat := [1, 4, 2, 1, 1, 4, 2, 3, 1, 4]
def baseStart_5027997 : Nat := 118140960795 + 5027997 * 2 ^ 59
def prefixEnd_5027997 : Nat := 4983230072969 + 3 ^ 40 * 5027997 * 2
def baseEnd_5027997 : Nat := 860593063454823224104723

theorem tailTrace_5027997 : CollatzResearch.WordTrace tailWord_5027997 prefixEnd_5027997 860593063454823224104723 := by
  unfold tailWord_5027997
  simp only [CollatzResearch.WordTrace]
  refine ⟨183386116365433057367034245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122257410910288704911356163 183386116365433057367034245)
  ·
    refine ⟨34384896818518698256318921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183386116365433057367034245 34384896818518698256318921)
    ·
      refine ⟨25788672613889023692239191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34384896818518698256318921 25788672613889023692239191)
      ·
        refine ⟨38683008920833535538358787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25788672613889023692239191 38683008920833535538358787)
        ·
          refine ⟨58024513381250303307538181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38683008920833535538358787 58024513381250303307538181)
          ·
            refine ⟨10879596258984431870163409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58024513381250303307538181 10879596258984431870163409)
            ·
              refine ⟨8159697194238323902622557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10879596258984431870163409 8159697194238323902622557)
              ·
                refine ⟨3059886447839371463483459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8159697194238323902622557 3059886447839371463483459)
                ·
                  refine ⟨4589829671759057195225189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3059886447839371463483459 4589829671759057195225189)
                  ·
                    refine ⟨860593063454823224104723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4589829671759057195225189 860593063454823224104723)
                    ·
                      rfl

theorem cell23_5027997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_5027997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5027997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5027997 prefixEnd_5027997 := by exact prefixLift 5027997
  have htrace : WordTrace (prefixWord ++ tailWord_5027997) baseStart_5027997 baseEnd_5027997 := by
    simpa [prefixWord, tailWord_5027997, baseEnd_5027997] using wordTrace_append hprefix tailTrace_5027997
  have hstable : (prefixWord ++ tailWord_5027997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5027997).length < 2 ^ (prefixWord ++ tailWord_5027997).sum := by decide
  have hdescent : baseEnd_5027997 < baseStart_5027997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5027997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028010 : List Nat := [3, 1, 5, 1, 2, 1, 1, 1, 8]
def baseStart_5028010 : Nat := 118140960795 + 5028010 * 2 ^ 59
def prefixEnd_5028010 : Nat := 4983230072969 + 3 ^ 40 * 5028010 * 2
def baseEnd_5028010 : Nat := 286865096179219791272401

theorem tailTrace_5028010 : CollatzResearch.WordTrace tailWord_5028010 prefixEnd_5028010 286865096179219791272401 := by
  unfold tailWord_5028010
  simp only [CollatzResearch.WordTrace]
  refine ⟨45846647628596490146814371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122257727009590640391504989 45846647628596490146814371)
  ·
    refine ⟨68769971442894735220221557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45846647628596490146814371 68769971442894735220221557)
    ·
      refine ⟨6447184822771381426895771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68769971442894735220221557 6447184822771381426895771)
      ·
        refine ⟨9670777234157072140343657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6447184822771381426895771 9670777234157072140343657)
        ·
          refine ⟨7253082925617804105257743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9670777234157072140343657 7253082925617804105257743)
          ·
            refine ⟨10879624388426706157886615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7253082925617804105257743 10879624388426706157886615)
            ·
              refine ⟨16319436582640059236829923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10879624388426706157886615 16319436582640059236829923)
              ·
                refine ⟨24479154873960088855244885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16319436582640059236829923 24479154873960088855244885)
                ·
                  refine ⟨286865096179219791272401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24479154873960088855244885 286865096179219791272401)
                  ·
                    rfl

theorem cell23_5028010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 8].length) (baseStart_5028010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028010 prefixEnd_5028010 := by exact prefixLift 5028010
  have htrace : WordTrace (prefixWord ++ tailWord_5028010) baseStart_5028010 baseEnd_5028010 := by
    simpa [prefixWord, tailWord_5028010, baseEnd_5028010] using wordTrace_append hprefix tailTrace_5028010
  have hstable : (prefixWord ++ tailWord_5028010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028010).length < 2 ^ (prefixWord ++ tailWord_5028010).sum := by decide
  have hdescent : baseEnd_5028010 < baseStart_5028010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028013 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_5028013 : Nat := 118140960795 + 5028013 * 2 ^ 59
def prefixEnd_5028013 : Nat := 4983230072969 + 3 ^ 40 * 5028013 * 2
def baseEnd_5028013 : Nat := 2581787406054941609714095

theorem tailTrace_5028013 : CollatzResearch.WordTrace tailWord_5028013 prefixEnd_5028013 2581787406054941609714095 := by
  unfold tailWord_5028013
  simp only [CollatzResearch.WordTrace]
  refine ⟨183386699933375092099616693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122257799955583394733077795 183386699933375092099616693)
  ·
    refine ⟨17192503118753914884339065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 183386699933375092099616693 17192503118753914884339065)
    ·
      refine ⟨12894377339065436163254299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17192503118753914884339065 12894377339065436163254299)
      ·
        refine ⟨19341566008598154244881449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12894377339065436163254299 19341566008598154244881449)
        ·
          refine ⟨14506174506448615683661087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19341566008598154244881449 14506174506448615683661087)
          ·
            refine ⟨21759261759672923525491631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14506174506448615683661087 21759261759672923525491631)
            ·
              refine ⟨32638892639509385288237447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21759261759672923525491631 32638892639509385288237447)
              ·
                refine ⟨48958338959264077932356171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32638892639509385288237447 48958338959264077932356171)
                ·
                  refine ⟨73437508438896116898534257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48958338959264077932356171 73437508438896116898534257)
                  ·
                    refine ⟨55078131329172087673900693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73437508438896116898534257 55078131329172087673900693)
                    ·
                      refine ⟨2581787406054941609714095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55078131329172087673900693 2581787406054941609714095)
                      ·
                        rfl

theorem cell23_5028013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_5028013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028013 prefixEnd_5028013 := by exact prefixLift 5028013
  have htrace : WordTrace (prefixWord ++ tailWord_5028013) baseStart_5028013 baseEnd_5028013 := by
    simpa [prefixWord, tailWord_5028013, baseEnd_5028013] using wordTrace_append hprefix tailTrace_5028013
  have hstable : (prefixWord ++ tailWord_5028013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028013).length < 2 ^ (prefixWord ++ tailWord_5028013).sum := by decide
  have hdescent : baseEnd_5028013 < baseStart_5028013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028014 : List Nat := [4, 1, 4, 2, 1, 1, 2, 1, 3, 4]
def baseStart_5028014 : Nat := 118140960795 + 5028014 * 2 ^ 59
def prefixEnd_5028014 : Nat := 4983230072969 + 3 ^ 40 * 5028014 * 2
def baseEnd_5028014 : Nat := 860595973178532035267197

theorem tailTrace_5028014 : CollatzResearch.WordTrace tailWord_5028014 prefixEnd_5028014 860595973178532035267197 := by
  unfold tailWord_5028014
  simp only [CollatzResearch.WordTrace]
  refine ⟨22923342050796433658800387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122257824270914312846935397 22923342050796433658800387)
  ·
    refine ⟨34385013076194650488200581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22923342050796433658800387 34385013076194650488200581)
    ·
      refine ⟨6447189951786496966537609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34385013076194650488200581 6447189951786496966537609)
      ·
        refine ⟨4835392463839872724903207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6447189951786496966537609 4835392463839872724903207)
        ·
          refine ⟨7253088695759809087354811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4835392463839872724903207 7253088695759809087354811)
          ·
            refine ⟨10879633043639713631032217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7253088695759809087354811 10879633043639713631032217)
            ·
              refine ⟨8159724782729785223274163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10879633043639713631032217 8159724782729785223274163)
              ·
                refine ⟨12239587174094677834911245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8159724782729785223274163 12239587174094677834911245)
                ·
                  refine ⟨4589845190285504188091717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12239587174094677834911245 4589845190285504188091717)
                  ·
                    refine ⟨860595973178532035267197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4589845190285504188091717 860595973178532035267197)
                    ·
                      rfl

theorem cell23_5028014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_5028014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028014 prefixEnd_5028014 := by exact prefixLift 5028014
  have htrace : WordTrace (prefixWord ++ tailWord_5028014) baseStart_5028014 baseEnd_5028014 := by
    simpa [prefixWord, tailWord_5028014, baseEnd_5028014] using wordTrace_append hprefix tailTrace_5028014
  have hstable : (prefixWord ++ tailWord_5028014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028014).length < 2 ^ (prefixWord ++ tailWord_5028014).sum := by decide
  have hdescent : baseEnd_5028014 < baseStart_5028014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028043 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 2, 6, 2]
def baseStart_5028043 : Nat := 118140960795 + 5028043 * 2 ^ 59
def prefixEnd_5028043 : Nat := 4983230072969 + 3 ^ 40 * 5028043 * 2
def baseEnd_5028043 : Nat := 2581802810474576492338957

theorem tailTrace_5028043 : CollatzResearch.WordTrace tailWord_5028043 prefixEnd_5028043 2581802810474576492338957 := by
  unfold tailWord_5028043
  simp only [CollatzResearch.WordTrace]
  refine ⟨183387794123266407223208783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122258529415510938148805855 183387794123266407223208783)
  ·
    refine ⟨275081691184899610834813175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183387794123266407223208783 275081691184899610834813175)
    ·
      refine ⟨412622536777349416252219763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275081691184899610834813175 412622536777349416252219763)
      ·
        refine ⟨618933805166024124378329645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412622536777349416252219763 618933805166024124378329645)
        ·
          refine ⟨232100176937259046641873617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 618933805166024124378329645 232100176937259046641873617)
          ·
            refine ⟨174075132702944284981405213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232100176937259046641873617 174075132702944284981405213)
            ·
              refine ⟨65278174763604106868026955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174075132702944284981405213 65278174763604106868026955)
              ·
                refine ⟨97917262145406160302040433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65278174763604106868026955 97917262145406160302040433)
                ·
                  refine ⟨73437946609054620226530325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97917262145406160302040433 73437946609054620226530325)
                  ·
                    refine ⟨3442403747299435323118609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73437946609054620226530325 3442403747299435323118609)
                    ·
                      refine ⟨2581802810474576492338957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3442403747299435323118609 2581802810474576492338957)
                      ·
                        rfl

theorem cell23_5028043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 6, 2].length) (baseStart_5028043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028043 prefixEnd_5028043 := by exact prefixLift 5028043
  have htrace : WordTrace (prefixWord ++ tailWord_5028043) baseStart_5028043 baseEnd_5028043 := by
    simpa [prefixWord, tailWord_5028043, baseEnd_5028043] using wordTrace_append hprefix tailTrace_5028043
  have hstable : (prefixWord ++ tailWord_5028043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028043).length < 2 ^ (prefixWord ++ tailWord_5028043).sum := by decide
  have hdescent : baseEnd_5028043 < baseStart_5028043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028063 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 5, 2, 3]
def baseStart_5028063 : Nat := 118140960795 + 5028063 * 2 ^ 59
def prefixEnd_5028063 : Nat := 4983230072969 + 3 ^ 40 * 5028063 * 2
def baseEnd_5028063 : Nat := 2581813080087666414088865

theorem tailTrace_5028063 : CollatzResearch.WordTrace tailWord_5028063 prefixEnd_5028063 2581813080087666414088865 := by
  unfold tailWord_5028063
  simp only [CollatzResearch.WordTrace]
  refine ⟨183388523583193950638936843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122259015722129300425957895 183388523583193950638936843)
  ·
    refine ⟨275082785374790925958405265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183388523583193950638936843 275082785374790925958405265)
    ·
      refine ⟨206312089031093194468803949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275082785374790925958405265 206312089031093194468803949)
      ·
        refine ⟨77367033386659947925801481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206312089031093194468803949 77367033386659947925801481)
        ·
          refine ⟨58025275039994960944351111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77367033386659947925801481 58025275039994960944351111)
          ·
            refine ⟨87037912559992441416526667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58025275039994960944351111 87037912559992441416526667)
            ·
              refine ⟨130556868839988662124790001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87037912559992441416526667 130556868839988662124790001)
              ·
                refine ⟨97917651629991496593592501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130556868839988662124790001 97917651629991496593592501)
                ·
                  refine ⟨9179779840311702805649297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97917651629991496593592501 9179779840311702805649297)
                  ·
                    refine ⟨6884834880233777104236973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9179779840311702805649297 6884834880233777104236973)
                    ·
                      refine ⟨2581813080087666414088865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6884834880233777104236973 2581813080087666414088865)
                      ·
                        rfl

theorem cell23_5028063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_5028063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028063 prefixEnd_5028063 := by exact prefixLift 5028063
  have htrace : WordTrace (prefixWord ++ tailWord_5028063) baseStart_5028063 baseEnd_5028063 := by
    simpa [prefixWord, tailWord_5028063, baseEnd_5028063] using wordTrace_append hprefix tailTrace_5028063
  have hstable : (prefixWord ++ tailWord_5028063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028063).length < 2 ^ (prefixWord ++ tailWord_5028063).sum := by decide
  have hdescent : baseEnd_5028063 < baseStart_5028063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028071 : List Nat := [1, 1, 5, 3, 1, 2, 3, 2, 1, 1, 3]
def baseStart_5028071 : Nat := 118140960795 + 5028071 * 2 ^ 59
def prefixEnd_5028071 : Nat := 4983230072969 + 3 ^ 40 * 5028071 * 2
def baseEnd_5028071 : Nat := 2581817187932902382788829

theorem tailTrace_5028071 : CollatzResearch.WordTrace tailWord_5028071 prefixEnd_5028071 2581817187932902382788829 := by
  unfold tailWord_5028071
  simp only [CollatzResearch.WordTrace]
  refine ⟨183388815367164968005228067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122259210244776645336818711 183388815367164968005228067)
  ·
    refine ⟨275083223050747452007842101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183388815367164968005228067 275083223050747452007842101)
    ·
      refine ⟨25789052161007573625735197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 275083223050747452007842101 25789052161007573625735197)
      ·
        refine ⟨9670894560377840109650699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25789052161007573625735197 9670894560377840109650699)
        ·
          refine ⟨14506341840566760164476049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9670894560377840109650699 14506341840566760164476049)
          ·
            refine ⟨10879756380425070123357037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14506341840566760164476049 10879756380425070123357037)
            ·
              refine ⟨4079908642659401296258889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10879756380425070123357037 4079908642659401296258889)
              ·
                refine ⟨3059931481994550972194167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4079908642659401296258889 3059931481994550972194167)
                ·
                  refine ⟨4589897222991826458291251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3059931481994550972194167 4589897222991826458291251)
                  ·
                    refine ⟨6884845834487739687436877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4589897222991826458291251 6884845834487739687436877)
                    ·
                      refine ⟨2581817187932902382788829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6884845834487739687436877 2581817187932902382788829)
                      ·
                        rfl

theorem cell23_5028071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_5028071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028071 prefixEnd_5028071 := by exact prefixLift 5028071
  have htrace : WordTrace (prefixWord ++ tailWord_5028071) baseStart_5028071 baseEnd_5028071 := by
    simpa [prefixWord, tailWord_5028071, baseEnd_5028071] using wordTrace_append hprefix tailTrace_5028071
  have hstable : (prefixWord ++ tailWord_5028071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028071).length < 2 ^ (prefixWord ++ tailWord_5028071).sum := by decide
  have hdescent : baseEnd_5028071 < baseStart_5028071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028093 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 5, 3, 3]
def baseStart_5028093 : Nat := 118140960795 + 5028093 * 2 ^ 59
def prefixEnd_5028093 : Nat := 4983230072969 + 3 ^ 40 * 5028093 * 2
def baseEnd_5028093 : Nat := 2581828484507301296713727

theorem tailTrace_5028093 : CollatzResearch.WordTrace tailWord_5028093 prefixEnd_5028093 2581828484507301296713727 := by
  unfold tailWord_5028093
  simp only [CollatzResearch.WordTrace]
  refine ⟨183389617773085265762528933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122259745182056843841685955 183389617773085265762528933)
  ·
    refine ⟨34385553332453487330474175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183389617773085265762528933 34385553332453487330474175)
    ·
      refine ⟨51578329998680230995711263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34385553332453487330474175 51578329998680230995711263)
      ·
        refine ⟨77367494998020346493566895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51578329998680230995711263 77367494998020346493566895)
        ·
          refine ⟨116051242497030519740350343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77367494998020346493566895 116051242497030519740350343)
          ·
            refine ⟨174076863745545779610525515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116051242497030519740350343 174076863745545779610525515)
            ·
              refine ⟨261115295618318669415788273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174076863745545779610525515 261115295618318669415788273)
              ·
                refine ⟨195836471713739002061841205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 261115295618318669415788273 195836471713739002061841205)
                ·
                  refine ⟨18359669223163031443297613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 195836471713739002061841205 18359669223163031443297613)
                  ·
                    refine ⟨6884875958686136791236605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18359669223163031443297613 6884875958686136791236605)
                    ·
                      refine ⟨2581828484507301296713727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6884875958686136791236605 2581828484507301296713727)
                      ·
                        rfl

theorem cell23_5028093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_5028093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028093 prefixEnd_5028093 := by exact prefixLift 5028093
  have htrace : WordTrace (prefixWord ++ tailWord_5028093) baseStart_5028093 baseEnd_5028093 := by
    simpa [prefixWord, tailWord_5028093, baseEnd_5028093] using wordTrace_append hprefix tailTrace_5028093
  have hstable : (prefixWord ++ tailWord_5028093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028093).length < 2 ^ (prefixWord ++ tailWord_5028093).sum := by decide
  have hdescent : baseEnd_5028093 < baseStart_5028093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028110 : List Nat := [4, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3]
def baseStart_5028110 : Nat := 118140960795 + 5028110 * 2 ^ 59
def prefixEnd_5028110 : Nat := 4983230072969 + 3 ^ 40 * 5028110 * 2
def baseEnd_5028110 : Nat := 2581837213678427730201149

theorem tailTrace_5028110 : CollatzResearch.WordTrace tailWord_5028110 prefixEnd_5028110 2581837213678427730201149 := by
  unfold tailWord_5028110
  simp only [CollatzResearch.WordTrace]
  refine ⟨22923779726752959708237223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122260158542682451777265189 22923779726752959708237223)
  ·
    refine ⟨34385669590129439562355835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22923779726752959708237223 34385669590129439562355835)
    ·
      refine ⟨51578504385194159343533753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34385669590129439562355835 51578504385194159343533753)
      ·
        refine ⟨38683878288895619507650315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51578504385194159343533753 38683878288895619507650315)
        ·
          refine ⟨58025817433343429261475473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38683878288895619507650315 58025817433343429261475473)
          ·
            refine ⟨43519363075007571946106605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58025817433343429261475473 43519363075007571946106605)
            ·
              refine ⟨16319761153127839479789977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43519363075007571946106605 16319761153127839479789977)
              ·
                refine ⟨12239820864845879609842483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16319761153127839479789977 12239820864845879609842483)
                ·
                  refine ⟨18359731297268819414763725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12239820864845879609842483 18359731297268819414763725)
                  ·
                    refine ⟨6884899236475807280536397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18359731297268819414763725 6884899236475807280536397)
                    ·
                      refine ⟨2581837213678427730201149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6884899236475807280536397 2581837213678427730201149)
                      ·
                        rfl

theorem cell23_5028110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_5028110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028110 prefixEnd_5028110 := by exact prefixLift 5028110
  have htrace : WordTrace (prefixWord ++ tailWord_5028110) baseStart_5028110 baseEnd_5028110 := by
    simpa [prefixWord, tailWord_5028110, baseEnd_5028110] using wordTrace_append hprefix tailTrace_5028110
  have hstable : (prefixWord ++ tailWord_5028110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028110).length < 2 ^ (prefixWord ++ tailWord_5028110).sum := by decide
  have hdescent : baseEnd_5028110 < baseStart_5028110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028127 : List Nat := [1, 1, 2, 4, 3, 1, 1, 4, 2, 1, 3]
def baseStart_5028127 : Nat := 118140960795 + 5028127 * 2 ^ 59
def prefixEnd_5028127 : Nat := 4983230072969 + 3 ^ 40 * 5028127 * 2
def baseEnd_5028127 : Nat := 2581845942849554163688571

theorem tailTrace_5028127 : CollatzResearch.WordTrace tailWord_5028127 prefixEnd_5028127 2581845942849554163688571 := by
  unfold tailWord_5028127
  simp only [CollatzResearch.WordTrace]
  refine ⟨183390857854962089569266635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122260571903308059712844423 183390857854962089569266635)
  ·
    refine ⟨275086286782443134353899953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183390857854962089569266635 275086286782443134353899953)
    ·
      refine ⟨206314715086832350765424965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275086286782443134353899953 206314715086832350765424965)
      ·
        refine ⟨38684009078781065768517181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 206314715086832350765424965 38684009078781065768517181)
        ·
          refine ⟨14506503404542899663193943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38684009078781065768517181 14506503404542899663193943)
          ·
            refine ⟨21759755106814349494790915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14506503404542899663193943 21759755106814349494790915)
            ·
              refine ⟨32639632660221524242186373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21759755106814349494790915 32639632660221524242186373)
              ·
                refine ⟨6119931123791535795409945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32639632660221524242186373 6119931123791535795409945)
                ·
                  refine ⟨4589948342843651846557459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6119931123791535795409945 4589948342843651846557459)
                  ·
                    refine ⟨6884922514265477769836189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4589948342843651846557459 6884922514265477769836189)
                    ·
                      refine ⟨2581845942849554163688571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6884922514265477769836189 2581845942849554163688571)
                      ·
                        rfl

theorem cell23_5028127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_5028127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028127 prefixEnd_5028127 := by exact prefixLift 5028127
  have htrace : WordTrace (prefixWord ++ tailWord_5028127) baseStart_5028127 baseEnd_5028127 := by
    simpa [prefixWord, tailWord_5028127, baseEnd_5028127] using wordTrace_append hprefix tailTrace_5028127
  have hstable : (prefixWord ++ tailWord_5028127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028127).length < 2 ^ (prefixWord ++ tailWord_5028127).sum := by decide
  have hdescent : baseEnd_5028127 < baseStart_5028127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028128 : List Nat := [2, 1, 1, 5, 2, 3, 2, 2, 1, 2, 2]
def baseStart_5028128 : Nat := 118140960795 + 5028128 * 2 ^ 59
def prefixEnd_5028128 : Nat := 4983230072969 + 3 ^ 40 * 5028128 * 2
def baseEnd_5028128 : Nat := 2581846456330208659776067

theorem tailTrace_5028128 : CollatzResearch.WordTrace tailWord_5028128 prefixEnd_5028128 2581846456330208659776067 := by
  unfold tailWord_5028128
  simp only [CollatzResearch.WordTrace]
  refine ⟨91695447163979233370026519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122260596218638977826702025 91695447163979233370026519)
  ·
    refine ⟨137543170745968850055039779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91695447163979233370026519 137543170745968850055039779)
    ·
      refine ⟨206314756118953275082559669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137543170745968850055039779 206314756118953275082559669)
      ·
        refine ⟨19342008386151869538989969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 206314756118953275082559669 19342008386151869538989969)
        ·
          refine ⟨14506506289613902154242477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19342008386151869538989969 14506506289613902154242477)
          ·
            refine ⟨5439939858605213307840929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14506506289613902154242477 5439939858605213307840929)
            ·
              refine ⟨4079954893953909980880697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5439939858605213307840929 4079954893953909980880697)
              ·
                refine ⟨3059966170465432485660523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4079954893953909980880697 3059966170465432485660523)
                ·
                  refine ⟨4589949255698148728490785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3059966170465432485660523 4589949255698148728490785)
                  ·
                    refine ⟨3442461941773611546368089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4589949255698148728490785 3442461941773611546368089)
                    ·
                      refine ⟨2581846456330208659776067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3442461941773611546368089 2581846456330208659776067)
                      ·
                        rfl

theorem cell23_5028128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_5028128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028128 prefixEnd_5028128 := by exact prefixLift 5028128
  have htrace : WordTrace (prefixWord ++ tailWord_5028128) baseStart_5028128 baseEnd_5028128 := by
    simpa [prefixWord, tailWord_5028128, baseEnd_5028128] using wordTrace_append hprefix tailTrace_5028128
  have hstable : (prefixWord ++ tailWord_5028128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028128).length < 2 ^ (prefixWord ++ tailWord_5028128).sum := by decide
  have hdescent : baseEnd_5028128 < baseStart_5028128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028167 : List Nat := [1, 1, 4, 1, 2, 2, 2, 2, 4, 2, 2]
def baseStart_5028167 : Nat := 118140960795 + 5028167 * 2 ^ 59
def prefixEnd_5028167 : Nat := 4983230072969 + 3 ^ 40 * 5028167 * 2
def baseEnd_5028167 : Nat := 2581866482075734007188387

theorem tailTrace_5028167 : CollatzResearch.WordTrace tailWord_5028167 prefixEnd_5028167 2581866482075734007188387 := by
  unfold tailWord_5028167
  simp only [CollatzResearch.WordTrace]
  refine ⟨183392316774817176400722755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122261544516544784267148503 183392316774817176400722755)
  ·
    refine ⟨275088475162225764601084133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183392316774817176400722755 275088475162225764601084133)
    ·
      refine ⟨51579089092917330862703275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 275088475162225764601084133 51579089092917330862703275)
      ·
        refine ⟨77368633639375996294054913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51579089092917330862703275 77368633639375996294054913)
        ·
          refine ⟨58026475229531997220541185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77368633639375996294054913 58026475229531997220541185)
          ·
            refine ⟨43519856422148997915405889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58026475229531997220541185 43519856422148997915405889)
            ·
              refine ⟨32639892316611748436554417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43519856422148997915405889 32639892316611748436554417)
              ·
                refine ⟨24479919237458811327415813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32639892316611748436554417 24479919237458811327415813)
                ·
                  refine ⟨4589984857023527123890465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24479919237458811327415813 4589984857023527123890465)
                  ·
                    refine ⟨3442488642767645342917849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4589984857023527123890465 3442488642767645342917849)
                    ·
                      refine ⟨2581866482075734007188387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3442488642767645342917849 2581866482075734007188387)
                      ·
                        rfl

theorem cell23_5028167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 4, 2, 2].length) (baseStart_5028167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028167 prefixEnd_5028167 := by exact prefixLift 5028167
  have htrace : WordTrace (prefixWord ++ tailWord_5028167) baseStart_5028167 baseEnd_5028167 := by
    simpa [prefixWord, tailWord_5028167, baseEnd_5028167] using wordTrace_append hprefix tailTrace_5028167
  have hstable : (prefixWord ++ tailWord_5028167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028167).length < 2 ^ (prefixWord ++ tailWord_5028167).sum := by decide
  have hdescent : baseEnd_5028167 < baseStart_5028167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028180 : List Nat := [2, 4, 1, 1, 2, 2, 1, 2, 2, 2, 4]
def baseStart_5028180 : Nat := 118140960795 + 5028180 * 2 ^ 59
def prefixEnd_5028180 : Nat := 4983230072969 + 3 ^ 40 * 5028180 * 2
def baseEnd_5028180 : Nat := 2581873157324242456325827

theorem tailTrace_5028180 : CollatzResearch.WordTrace tailWord_5028180 prefixEnd_5028180 2581873157324242456325827 := by
  unfold tailWord_5028180
  simp only [CollatzResearch.WordTrace]
  refine ⟨91696395461885039810472997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122261860615846719747297329 91696395461885039810472997)
  ·
    refine ⟨17193074149103444964463687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91696395461885039810472997 17193074149103444964463687)
    ·
      refine ⟨25789611223655167446695531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17193074149103444964463687 25789611223655167446695531)
      ·
        refine ⟨38684416835482751170043297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25789611223655167446695531 38684416835482751170043297)
        ·
          refine ⟨29013312626612063377532473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38684416835482751170043297 29013312626612063377532473)
          ·
            refine ⟨21759984469959047533149355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29013312626612063377532473 21759984469959047533149355)
            ·
              refine ⟨32639976704938571299724033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21759984469959047533149355 32639976704938571299724033)
              ·
                refine ⟨24479982528703928474793025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32639976704938571299724033 24479982528703928474793025)
                ·
                  refine ⟨18359986896527946356094769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24479982528703928474793025 18359986896527946356094769)
                  ·
                    refine ⟨13769990172395959767071077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18359986896527946356094769 13769990172395959767071077)
                    ·
                      refine ⟨2581873157324242456325827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13769990172395959767071077 2581873157324242456325827)
                      ·
                        rfl

theorem cell23_5028180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_5028180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028180 prefixEnd_5028180 := by exact prefixLift 5028180
  have htrace : WordTrace (prefixWord ++ tailWord_5028180) baseStart_5028180 baseEnd_5028180 := by
    simpa [prefixWord, tailWord_5028180, baseEnd_5028180] using wordTrace_append hprefix tailTrace_5028180
  have hstable : (prefixWord ++ tailWord_5028180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028180).length < 2 ^ (prefixWord ++ tailWord_5028180).sum := by decide
  have hdescent : baseEnd_5028180 < baseStart_5028180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028203 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 4, 5]
def baseStart_5028203 : Nat := 118140960795 + 5028203 * 2 ^ 59
def prefixEnd_5028203 : Nat := 4983230072969 + 3 ^ 40 * 5028203 * 2
def baseEnd_5028203 : Nat := 860628322459765288779407

theorem tailTrace_5028203 : CollatzResearch.WordTrace tailWord_5028203 prefixEnd_5028203 860628322459765288779407 := by
  unfold tailWord_5028203
  simp only [CollatzResearch.WordTrace]
  refine ⟨183393629802686754549033263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122262419868457836366022175 183393629802686754549033263)
  ·
    refine ⟨275090444704030131823549895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183393629802686754549033263 275090444704030131823549895)
    ·
      refine ⟨412635667056045197735324843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275090444704030131823549895 412635667056045197735324843)
      ·
        refine ⟨618953500584067796602987265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412635667056045197735324843 618953500584067796602987265)
        ·
          refine ⟨464215125438050847452240449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 618953500584067796602987265 464215125438050847452240449)
          ·
            refine ⟨348161344078538135589180337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 464215125438050847452240449 348161344078538135589180337)
            ·
              refine ⟨261121008058903601691885253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 348161344078538135589180337 261121008058903601691885253)
              ·
                refine ⟨48960189011044425317228485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 261121008058903601691885253 48960189011044425317228485)
                ·
                  refine ⟨9180035439570829746980341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48960189011044425317228485 9180035439570829746980341)
                  ·
                    refine ⟨860628322459765288779407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9180035439570829746980341 860628322459765288779407)
                    ·
                      rfl

theorem cell23_5028203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 5].length) (baseStart_5028203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028203 prefixEnd_5028203 := by exact prefixLift 5028203
  have htrace : WordTrace (prefixWord ++ tailWord_5028203) baseStart_5028203 baseEnd_5028203 := by
    simpa [prefixWord, tailWord_5028203, baseEnd_5028203] using wordTrace_append hprefix tailTrace_5028203
  have hstable : (prefixWord ++ tailWord_5028203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028203).length < 2 ^ (prefixWord ++ tailWord_5028203).sum := by decide
  have hdescent : baseEnd_5028203 < baseStart_5028203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028240 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 5, 6, 2]
def baseStart_5028240 : Nat := 118140960795 + 5028240 * 2 ^ 59
def prefixEnd_5028240 : Nat := 4983230072969 + 3 ^ 40 * 5028240 * 2
def baseEnd_5028240 : Nat := 2581903966163512221575551

theorem tailTrace_5028240 : CollatzResearch.WordTrace tailWord_5028240 prefixEnd_5028240 2581903966163512221575551 := by
  unfold tailWord_5028240
  simp only [CollatzResearch.WordTrace]
  refine ⟨91697489651776354934065087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122263319535701806578753449 91697489651776354934065087)
  ·
    refine ⟨137546234477664532401097631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91697489651776354934065087 137546234477664532401097631)
    ·
      refine ⟨206319351716496798601646447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137546234477664532401097631 206319351716496798601646447)
      ·
        refine ⟨309479027574745197902469671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206319351716496798601646447 309479027574745197902469671)
        ·
          refine ⟨464218541362117796853704507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309479027574745197902469671 464218541362117796853704507)
          ·
            refine ⟨696327812043176695280556761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464218541362117796853704507 696327812043176695280556761)
            ·
              refine ⟨522245859032382521460417571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 696327812043176695280556761 522245859032382521460417571)
              ·
                refine ⟨783368788548573782190626357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 522245859032382521460417571 783368788548573782190626357)
                ·
                  refine ⟨73440823926428792080371221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 783368788548573782190626357 73440823926428792080371221)
                  ·
                    refine ⟨3442538621551349628767401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73440823926428792080371221 3442538621551349628767401)
                    ·
                      refine ⟨2581903966163512221575551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3442538621551349628767401 2581903966163512221575551)
                      ·
                        rfl

theorem cell23_5028240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 5, 6, 2].length) (baseStart_5028240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028240 prefixEnd_5028240 := by exact prefixLift 5028240
  have htrace : WordTrace (prefixWord ++ tailWord_5028240) baseStart_5028240 baseEnd_5028240 := by
    simpa [prefixWord, tailWord_5028240, baseEnd_5028240] using wordTrace_append hprefix tailTrace_5028240
  have hstable : (prefixWord ++ tailWord_5028240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028240).length < 2 ^ (prefixWord ++ tailWord_5028240).sum := by decide
  have hdescent : baseEnd_5028240 < baseStart_5028240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028260 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 3, 4, 3]
def baseStart_5028260 : Nat := 118140960795 + 5028260 * 2 ^ 59
def prefixEnd_5028260 : Nat := 4983230072969 + 3 ^ 40 * 5028260 * 2
def baseEnd_5028260 : Nat := 2581914235776602143325459

theorem tailTrace_5028260 : CollatzResearch.WordTrace tailWord_5028260 prefixEnd_5028260 2581914235776602143325459 := by
  unfold tailWord_5028260
  simp only [CollatzResearch.WordTrace]
  refine ⟨91697854381740126641929117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122263805842320168855905489 91697854381740126641929117)
  ·
    refine ⟨34386695393152547490723419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91697854381740126641929117 34386695393152547490723419)
    ·
      refine ⟨51580043089728821236085129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34386695393152547490723419 51580043089728821236085129)
      ·
        refine ⟨38685032317296615927063847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51580043089728821236085129 38685032317296615927063847)
        ·
          refine ⟨58027548475944923890595771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38685032317296615927063847 58027548475944923890595771)
          ·
            refine ⟨87041322713917385835893657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58027548475944923890595771 87041322713917385835893657)
            ·
              refine ⟨65280992035438039376920243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87041322713917385835893657 65280992035438039376920243)
              ·
                refine ⟨97921488053157059065380365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65280992035438039376920243 97921488053157059065380365)
                ·
                  refine ⟨36720558019933897149517637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97921488053157059065380365 36720558019933897149517637)
                  ·
                    refine ⟨6885104628737605715534557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36720558019933897149517637 6885104628737605715534557)
                    ·
                      refine ⟨2581914235776602143325459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6885104628737605715534557 2581914235776602143325459)
                      ·
                        rfl

theorem cell23_5028260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_5028260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028260 prefixEnd_5028260 := by exact prefixLift 5028260
  have htrace : WordTrace (prefixWord ++ tailWord_5028260) baseStart_5028260 baseEnd_5028260 := by
    simpa [prefixWord, tailWord_5028260, baseEnd_5028260] using wordTrace_append hprefix tailTrace_5028260
  have hstable : (prefixWord ++ tailWord_5028260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028260).length < 2 ^ (prefixWord ++ tailWord_5028260).sum := by decide
  have hdescent : baseEnd_5028260 < baseStart_5028260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028283 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 6]
def baseStart_5028283 : Nat := 118140960795 + 5028283 * 2 ^ 59
def prefixEnd_5028283 : Nat := 4983230072969 + 3 ^ 40 * 5028283 * 2
def baseEnd_5028283 : Nat := 2581926045831655553337853

theorem tailTrace_5028283 : CollatzResearch.WordTrace tailWord_5028283 prefixEnd_5028283 2581926045831655553337853 := by
  unfold tailWord_5028283
  simp only [CollatzResearch.WordTrace]
  refine ⟨183396547642396928211945503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122264365094931285474630335 183396547642396928211945503)
  ·
    refine ⟨275094821463595392317918255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183396547642396928211945503 275094821463595392317918255)
    ·
      refine ⟨412642232195393088476877383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275094821463595392317918255 412642232195393088476877383)
      ·
        refine ⟨618963348293089632715316075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412642232195393088476877383 618963348293089632715316075)
        ·
          refine ⟨928445022439634449072974113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 618963348293089632715316075 928445022439634449072974113)
          ·
            refine ⟨696333766829725836804730585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 928445022439634449072974113 696333766829725836804730585)
            ·
              refine ⟨522250325122294377603547939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 696333766829725836804730585 522250325122294377603547939)
              ·
                refine ⟨783375487683441566405321909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 522250325122294377603547939 783375487683441566405321909)
                ·
                  refine ⟨73441451970322646850498929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 783375487683441566405321909 73441451970322646850498929)
                  ·
                    refine ⟨55081088977741985137874197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73441451970322646850498929 55081088977741985137874197)
                    ·
                      refine ⟨2581926045831655553337853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55081088977741985137874197 2581926045831655553337853)
                      ·
                        rfl

theorem cell23_5028283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 6].length) (baseStart_5028283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028283 prefixEnd_5028283 := by exact prefixLift 5028283
  have htrace : WordTrace (prefixWord ++ tailWord_5028283) baseStart_5028283 baseEnd_5028283 := by
    simpa [prefixWord, tailWord_5028283, baseEnd_5028283] using wordTrace_append hprefix tailTrace_5028283
  have hstable : (prefixWord ++ tailWord_5028283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028283).length < 2 ^ (prefixWord ++ tailWord_5028283).sum := by decide
  have hdescent : baseEnd_5028283 < baseStart_5028283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028327 : List Nat := [1, 1, 5, 2, 1, 1, 2, 4, 1, 5]
def baseStart_5028327 : Nat := 118140960795 + 5028327 * 2 ^ 59
def prefixEnd_5028327 : Nat := 4983230072969 + 3 ^ 40 * 5028327 * 2
def baseEnd_5028327 : Nat := 860649546326817793729217

theorem tailTrace_5028327 : CollatzResearch.WordTrace tailWord_5028327 prefixEnd_5028327 860649546326817793729217 := by
  unfold tailWord_5028327
  simp only [CollatzResearch.WordTrace]
  refine ⟨183398152454237523726547235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122265434969491682484364823 183398152454237523726547235)
  ·
    refine ⟨275097228681356285589820853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183398152454237523726547235 275097228681356285589820853)
    ·
      refine ⟨25790365188877151774045705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 275097228681356285589820853 25790365188877151774045705)
      ·
        refine ⟨19342773891657863830534279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25790365188877151774045705 19342773891657863830534279)
        ·
          refine ⟨29014160837486795745801419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19342773891657863830534279 29014160837486795745801419)
          ·
            refine ⟨43521241256230193618702129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29014160837486795745801419 43521241256230193618702129)
            ·
              refine ⟨32640930942172645214026597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43521241256230193618702129 32640930942172645214026597)
              ·
                refine ⟨6120174551657370977629987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32640930942172645214026597 6120174551657370977629987)
                ·
                  refine ⟨9180261827486056466444981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6120174551657370977629987 9180261827486056466444981)
                  ·
                    refine ⟨860649546326817793729217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9180261827486056466444981 860649546326817793729217)
                    ·
                      rfl

theorem cell23_5028327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_5028327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028327 prefixEnd_5028327 := by exact prefixLift 5028327
  have htrace : WordTrace (prefixWord ++ tailWord_5028327) baseStart_5028327 baseEnd_5028327 := by
    simpa [prefixWord, tailWord_5028327, baseEnd_5028327] using wordTrace_append hprefix tailTrace_5028327
  have hstable : (prefixWord ++ tailWord_5028327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028327).length < 2 ^ (prefixWord ++ tailWord_5028327).sum := by decide
  have hdescent : baseEnd_5028327 < baseStart_5028327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028334 : List Nat := [4, 1, 2, 1, 2, 3, 1, 1, 1, 5, 2]
def baseStart_5028334 : Nat := 118140960795 + 5028334 * 2 ^ 59
def prefixEnd_5028334 : Nat := 4983230072969 + 3 ^ 40 * 5028334 * 2
def baseEnd_5028334 : Nat := 2581952233345034853800119

theorem tailTrace_5028334 : CollatzResearch.WordTrace tailWord_5028334 prefixEnd_5028334 2581952233345034853800119 := by
  unfold tailWord_5028334
  simp only [CollatzResearch.WordTrace]
  refine ⟨22924800970651520490256507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122265605176808109281368037 22924800970651520490256507)
  ·
    refine ⟨34387201455977280735384761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22924800970651520490256507 34387201455977280735384761)
    ·
      refine ⟨25790401091982960551538571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34387201455977280735384761 25790401091982960551538571)
      ·
        refine ⟨38685601637974440827307857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25790401091982960551538571 38685601637974440827307857)
        ·
          refine ⟨29014201228480830620480893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38685601637974440827307857 29014201228480830620480893)
          ·
            refine ⟨10880325460680311482680335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29014201228480830620480893 10880325460680311482680335)
            ·
              refine ⟨16320488191020467224020503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10880325460680311482680335 16320488191020467224020503)
              ·
                refine ⟨24480732286530700836030755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16320488191020467224020503 24480732286530700836030755)
                ·
                  refine ⟨36721098429796051254046133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24480732286530700836030755 36721098429796051254046133)
                  ·
                    refine ⟨3442602977793379805066825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36721098429796051254046133 3442602977793379805066825)
                    ·
                      refine ⟨2581952233345034853800119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3442602977793379805066825 2581952233345034853800119)
                      ·
                        rfl

theorem cell23_5028334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_5028334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028334 prefixEnd_5028334 := by exact prefixLift 5028334
  have htrace : WordTrace (prefixWord ++ tailWord_5028334) baseStart_5028334 baseEnd_5028334 := by
    simpa [prefixWord, tailWord_5028334, baseEnd_5028334] using wordTrace_append hprefix tailTrace_5028334
  have hstable : (prefixWord ++ tailWord_5028334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028334).length < 2 ^ (prefixWord ++ tailWord_5028334).sum := by decide
  have hdescent : baseEnd_5028334 < baseStart_5028334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028360 : List Nat := [2, 1, 3, 2, 1, 1, 1, 4, 1, 1, 6]
def baseStart_5028360 : Nat := 118140960795 + 5028360 * 2 ^ 59
def prefixEnd_5028360 : Nat := 4983230072969 + 3 ^ 40 * 5028360 * 2
def baseEnd_5028360 : Nat := 2581965583842051752074999

theorem tailTrace_5028360 : CollatzResearch.WordTrace tailWord_5028360 prefixEnd_5028360 2581965583842051752074999 := by
  unfold tailWord_5028360
  simp only [CollatzResearch.WordTrace]
  refine ⟨91699678031558985181249267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122266237375411980241665689 91699678031558985181249267)
  ·
    refine ⟨137549517047338477771873901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91699678031558985181249267 137549517047338477771873901)
    ·
      refine ⟨51581068892751929164452713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137549517047338477771873901 51581068892751929164452713)
      ·
        refine ⟨38685801669563946873339535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51581068892751929164452713 38685801669563946873339535)
        ·
          refine ⟨58028702504345920310009303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38685801669563946873339535 58028702504345920310009303)
          ·
            refine ⟨87043053756518880465013955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58028702504345920310009303 87043053756518880465013955)
            ·
              refine ⟨130564580634778320697520933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87043053756518880465013955 130564580634778320697520933)
              ·
                refine ⟨24480858869020935130785175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130564580634778320697520933 24480858869020935130785175)
                ·
                  refine ⟨36721288303531402696177763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24480858869020935130785175 36721288303531402696177763)
                  ·
                    refine ⟨55081932455297104044266645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36721288303531402696177763 55081932455297104044266645)
                    ·
                      refine ⟨2581965583842051752074999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55081932455297104044266645 2581965583842051752074999)
                      ·
                        rfl

theorem cell23_5028360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_5028360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028360 prefixEnd_5028360 := by exact prefixLift 5028360
  have htrace : WordTrace (prefixWord ++ tailWord_5028360) baseStart_5028360 baseEnd_5028360 := by
    simpa [prefixWord, tailWord_5028360, baseEnd_5028360] using wordTrace_append hprefix tailTrace_5028360
  have hstable : (prefixWord ++ tailWord_5028360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028360).length < 2 ^ (prefixWord ++ tailWord_5028360).sum := by decide
  have hdescent : baseEnd_5028360 < baseStart_5028360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028381 : List Nat := [1, 4, 2, 2, 1, 2, 2, 2, 3, 2, 2]
def baseStart_5028381 : Nat := 118140960795 + 5028381 * 2 ^ 59
def prefixEnd_5028381 : Nat := 4983230072969 + 3 ^ 40 * 5028381 * 2
def baseEnd_5028381 : Nat := 2581976366935796169912403

theorem tailTrace_5028381 : CollatzResearch.WordTrace tailWord_5028381 prefixEnd_5028381 2581976366935796169912403 := by
  unfold tailWord_5028381
  simp only [CollatzResearch.WordTrace]
  refine ⟨183400121996041890949012997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122266747997361260632675331 183400121996041890949012997)
  ·
    refine ⟨34387522874257854552939937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183400121996041890949012997 34387522874257854552939937)
    ·
      refine ⟨25790642155693390914704953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34387522874257854552939937 25790642155693390914704953)
      ·
        refine ⟨19342981616770043186028715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25790642155693390914704953 19342981616770043186028715)
        ·
          refine ⟨29014472425155064779043073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19342981616770043186028715 29014472425155064779043073)
          ·
            refine ⟨21760854318866298584282305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29014472425155064779043073 21760854318866298584282305)
            ·
              refine ⟨16320640739149723938211729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21760854318866298584282305 16320640739149723938211729)
              ·
                refine ⟨12240480554362292953658797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16320640739149723938211729 12240480554362292953658797)
                ·
                  refine ⟨4590180207885859857622049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12240480554362292953658797 4590180207885859857622049)
                  ·
                    refine ⟨3442635155914394893216537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4590180207885859857622049 3442635155914394893216537)
                    ·
                      refine ⟨2581976366935796169912403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3442635155914394893216537 2581976366935796169912403)
                      ·
                        rfl

theorem cell23_5028381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_5028381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028381 prefixEnd_5028381 := by exact prefixLift 5028381
  have htrace : WordTrace (prefixWord ++ tailWord_5028381) baseStart_5028381 baseEnd_5028381 := by
    simpa [prefixWord, tailWord_5028381, baseEnd_5028381] using wordTrace_append hprefix tailTrace_5028381
  have hstable : (prefixWord ++ tailWord_5028381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028381).length < 2 ^ (prefixWord ++ tailWord_5028381).sum := by decide
  have hdescent : baseEnd_5028381 < baseStart_5028381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028387 : List Nat := [1, 1, 1, 4, 4, 1, 4, 7]
def baseStart_5028387 : Nat := 118140960795 + 5028387 * 2 ^ 59
def prefixEnd_5028387 : Nat := 4983230072969 + 3 ^ 40 * 5028387 * 2
def baseEnd_5028387 : Nat := 95628868437767523942125

theorem tailTrace_5028387 : CollatzResearch.WordTrace tailWord_5028387 prefixEnd_5028387 95628868437767523942125 := by
  unfold tailWord_5028387
  simp only [CollatzResearch.WordTrace]
  refine ⟨183400340834020153973731415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122266893889346769315820943 183400340834020153973731415)
  ·
    refine ⟨275100511251030230960597123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183400340834020153973731415 275100511251030230960597123)
    ·
      refine ⟨412650766876545346440895685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275100511251030230960597123 412650766876545346440895685)
      ·
        refine ⟨77372018789352252457667941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 412650766876545346440895685 77372018789352252457667941)
        ·
          refine ⟨14507253523003547335812739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77372018789352252457667941 14507253523003547335812739)
          ·
            refine ⟨21760880284505321003719109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14507253523003547335812739 21760880284505321003719109)
            ·
              refine ⟨4080165053344747688197333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21760880284505321003719109 4080165053344747688197333)
              ·
                refine ⟨95628868437767523942125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4080165053344747688197333 95628868437767523942125)
                ·
                  rfl

theorem cell23_5028387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 7].length) (baseStart_5028387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028387 prefixEnd_5028387 := by exact prefixLift 5028387
  have htrace : WordTrace (prefixWord ++ tailWord_5028387) baseStart_5028387 baseEnd_5028387 := by
    simpa [prefixWord, tailWord_5028387, baseEnd_5028387] using wordTrace_append hprefix tailTrace_5028387
  have hstable : (prefixWord ++ tailWord_5028387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028387).length < 2 ^ (prefixWord ++ tailWord_5028387).sum := by decide
  have hdescent : baseEnd_5028387 < baseStart_5028387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028431 : List Nat := [1, 1, 2, 1, 1, 2, 8, 1, 2, 1, 3]
def baseStart_5028431 : Nat := 118140960795 + 5028431 * 2 ^ 59
def prefixEnd_5028431 : Nat := 4983230072969 + 3 ^ 40 * 5028431 * 2
def baseEnd_5028431 : Nat := 2582002040968520974287173

theorem tailTrace_5028431 : CollatzResearch.WordTrace tailWord_5028431 prefixEnd_5028431 2582002040968520974287173 := by
  unfold tailWord_5028431
  simp only [CollatzResearch.WordTrace]
  refine ⟨183401945645860749488333147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122267963763907166325555431 183401945645860749488333147)
  ·
    refine ⟨275102918468791124232499721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183401945645860749488333147 275102918468791124232499721)
    ·
      refine ⟨206327188851593343174374791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275102918468791124232499721 206327188851593343174374791)
      ·
        refine ⟨309490783277390014761562187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206327188851593343174374791 309490783277390014761562187)
        ·
          refine ⟨464236174916085022142343281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309490783277390014761562187 464236174916085022142343281)
          ·
            refine ⟨348177131187063766606757461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 464236174916085022142343281 348177131187063766606757461)
            ·
              refine ⟨4080200756098403514922939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 348177131187063766606757461 4080200756098403514922939)
              ·
                refine ⟨6120301134147605272384409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4080200756098403514922939 6120301134147605272384409)
                ·
                  refine ⟨4590225850610703954288307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6120301134147605272384409 4590225850610703954288307)
                  ·
                    refine ⟨6885338775916055931432461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4590225850610703954288307 6885338775916055931432461)
                    ·
                      refine ⟨2582002040968520974287173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6885338775916055931432461 2582002040968520974287173)
                      ·
                        rfl

theorem cell23_5028431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 2, 1, 3].length) (baseStart_5028431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028431 prefixEnd_5028431 := by exact prefixLift 5028431
  have htrace : WordTrace (prefixWord ++ tailWord_5028431) baseStart_5028431 baseEnd_5028431 := by
    simpa [prefixWord, tailWord_5028431, baseEnd_5028431] using wordTrace_append hprefix tailTrace_5028431
  have hstable : (prefixWord ++ tailWord_5028431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028431).length < 2 ^ (prefixWord ++ tailWord_5028431).sum := by decide
  have hdescent : baseEnd_5028431 < baseStart_5028431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028458 : List Nat := [3, 1, 3, 2, 1, 1, 5, 1, 1, 3, 2]
def baseStart_5028458 : Nat := 118140960795 + 5028458 * 2 ^ 59
def prefixEnd_5028458 : Nat := 4983230072969 + 3 ^ 40 * 5028458 * 2
def baseEnd_5028458 : Nat := 2582015904946192368649549

theorem tailTrace_5028458 : CollatzResearch.WordTrace tailWord_5028458 prefixEnd_5028458 2582015904946192368649549 := by
  unfold tailWord_5028458
  simp only [CollatzResearch.WordTrace]
  refine ⟨45850732604190733274891507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122268620277841955399710685 45850732604190733274891507)
  ·
    refine ⟨68776098906286099912337261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45850732604190733274891507 68776098906286099912337261)
    ·
      refine ⟨25791037089857287467126473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68776098906286099912337261 25791037089857287467126473)
      ·
        refine ⟨19343277817392965600344855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25791037089857287467126473 19343277817392965600344855)
        ·
          refine ⟨29014916726089448400517283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19343277817392965600344855 29014916726089448400517283)
          ·
            refine ⟨43522375089134172600775925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29014916726089448400517283 43522375089134172600775925)
            ·
              refine ⟨4080222664606328681322743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43522375089134172600775925 4080222664606328681322743)
              ·
                refine ⟨6120333996909493021984115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4080222664606328681322743 6120333996909493021984115)
                ·
                  refine ⟨9180500995364239532976173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6120333996909493021984115 9180500995364239532976173)
                  ·
                    refine ⟨3442687873261589824866065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9180500995364239532976173 3442687873261589824866065)
                    ·
                      refine ⟨2582015904946192368649549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3442687873261589824866065 2582015904946192368649549)
                      ·
                        rfl

theorem cell23_5028458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_5028458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028458 prefixEnd_5028458 := by exact prefixLift 5028458
  have htrace : WordTrace (prefixWord ++ tailWord_5028458) baseStart_5028458 baseEnd_5028458 := by
    simpa [prefixWord, tailWord_5028458, baseEnd_5028458] using wordTrace_append hprefix tailTrace_5028458
  have hstable : (prefixWord ++ tailWord_5028458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028458).length < 2 ^ (prefixWord ++ tailWord_5028458).sum := by decide
  have hdescent : baseEnd_5028458 < baseStart_5028458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028471 : List Nat := [1, 1, 3, 1, 1, 3, 3, 4, 2, 2, 2]
def baseStart_5028471 : Nat := 118140960795 + 5028471 * 2 ^ 59
def prefixEnd_5028471 : Nat := 4983230072969 + 3 ^ 40 * 5028471 * 2
def baseEnd_5028471 : Nat := 2582022580194700817786989

theorem tailTrace_5028471 : CollatzResearch.WordTrace tailWord_5028471 prefixEnd_5028471 2582022580194700817786989 := by
  unfold tailWord_5028471
  simp only [CollatzResearch.WordTrace]
  refine ⟨183403404565715836319789267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122268936377143890879859511 183403404565715836319789267)
  ·
    refine ⟨275105106848573754479683901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183403404565715836319789267 275105106848573754479683901)
    ·
      refine ⟨103164415068215157929881463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275105106848573754479683901 103164415068215157929881463)
      ·
        refine ⟨154746622602322736894822195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103164415068215157929881463 154746622602322736894822195)
        ·
          refine ⟨232119933903484105342233293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154746622602322736894822195 232119933903484105342233293)
          ·
            refine ⟨87044975213806539503337485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232119933903484105342233293 87044975213806539503337485)
            ·
              refine ⟨32641865705177452313751557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87044975213806539503337485 32641865705177452313751557)
              ·
                refine ⟨6120349819720772308828417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32641865705177452313751557 6120349819720772308828417)
                ·
                  refine ⟨4590262364790579231621313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6120349819720772308828417 4590262364790579231621313)
                  ·
                    refine ⟨3442696773592934423715985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4590262364790579231621313 3442696773592934423715985)
                    ·
                      refine ⟨2582022580194700817786989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3442696773592934423715985 2582022580194700817786989)
                      ·
                        rfl

theorem cell23_5028471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 2, 2, 2].length) (baseStart_5028471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028471 prefixEnd_5028471 := by exact prefixLift 5028471
  have htrace : WordTrace (prefixWord ++ tailWord_5028471) baseStart_5028471 baseEnd_5028471 := by
    simpa [prefixWord, tailWord_5028471, baseEnd_5028471] using wordTrace_append hprefix tailTrace_5028471
  have hstable : (prefixWord ++ tailWord_5028471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028471).length < 2 ^ (prefixWord ++ tailWord_5028471).sum := by decide
  have hdescent : baseEnd_5028471 < baseStart_5028471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028484 : List Nat := [2, 3, 2, 1, 3, 2, 1, 1, 2, 2, 4]
def baseStart_5028484 : Nat := 118140960795 + 5028484 * 2 ^ 59
def prefixEnd_5028484 : Nat := 4983230072969 + 3 ^ 40 * 5028484 * 2
def baseEnd_5028484 : Nat := 2582029255443209266924429

theorem tailTrace_5028484 : CollatzResearch.WordTrace tailWord_5028484 prefixEnd_5028484 2582029255443209266924429 := by
  unfold tailWord_5028484
  simp only [CollatzResearch.WordTrace]
  refine ⟨91701939357334369770006253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122269252476445826360008337 91701939357334369770006253)
  ·
    refine ⟨34388227259000388663752345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91701939357334369770006253 34388227259000388663752345)
    ·
      refine ⟨25791170444250291497814259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34388227259000388663752345 25791170444250291497814259)
      ·
        refine ⟨38686755666375437246721389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25791170444250291497814259 38686755666375437246721389)
        ·
          refine ⟨14507533374890788967520521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38686755666375437246721389 14507533374890788967520521)
          ·
            refine ⟨10880650031168091725640391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14507533374890788967520521 10880650031168091725640391)
            ·
              refine ⟨16320975046752137588460587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10880650031168091725640391 16320975046752137588460587)
              ·
                refine ⟨24481462570128206382690881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16320975046752137588460587 24481462570128206382690881)
                ·
                  refine ⟨18361096927596154787018161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24481462570128206382690881 18361096927596154787018161)
                  ·
                    refine ⟨13770822695697116090263621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18361096927596154787018161 13770822695697116090263621)
                    ·
                      refine ⟨2582029255443209266924429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13770822695697116090263621 2582029255443209266924429)
                      ·
                        rfl

theorem cell23_5028484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_5028484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028484 prefixEnd_5028484 := by exact prefixLift 5028484
  have htrace : WordTrace (prefixWord ++ tailWord_5028484) baseStart_5028484 baseEnd_5028484 := by
    simpa [prefixWord, tailWord_5028484, baseEnd_5028484] using wordTrace_append hprefix tailTrace_5028484
  have hstable : (prefixWord ++ tailWord_5028484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028484).length < 2 ^ (prefixWord ++ tailWord_5028484).sum := by decide
  have hdescent : baseEnd_5028484 < baseStart_5028484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028567 : List Nat := [1, 1, 3, 2, 1, 4, 1, 2, 8]
def baseStart_5028567 : Nat := 118140960795 + 5028567 * 2 ^ 59
def prefixEnd_5028567 : Nat := 4983230072969 + 3 ^ 40 * 5028567 * 2
def baseEnd_5028567 : Nat := 286896874926392493576283

theorem tailTrace_5028567 : CollatzResearch.WordTrace tailWord_5028567 prefixEnd_5028567 286896874926392493576283 := by
  unfold tailWord_5028567
  simp only [CollatzResearch.WordTrace]
  refine ⟨183406905973368044715283955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122271270648912029810189303 183406905973368044715283955)
  ·
    refine ⟨275110358960052067072925933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183406905973368044715283955 275110358960052067072925933)
    ·
      refine ⟨103166384610019525152347225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275110358960052067072925933 103166384610019525152347225)
      ·
        refine ⟨77374788457514643864260419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103166384610019525152347225 77374788457514643864260419)
        ·
          refine ⟨116062182686271965796390629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77374788457514643864260419 116062182686271965796390629)
          ·
            refine ⟨21761659253675993586823243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116062182686271965796390629 21761659253675993586823243)
            ·
              refine ⟨32642488880513990380234865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21761659253675993586823243 32642488880513990380234865)
              ·
                refine ⟨24481866660385492785176149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32642488880513990380234865 24481866660385492785176149)
                ·
                  refine ⟨286896874926392493576283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24481866660385492785176149 286896874926392493576283)
                  ·
                    rfl

theorem cell23_5028567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 8].length) (baseStart_5028567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028567 prefixEnd_5028567 := by exact prefixLift 5028567
  have htrace : WordTrace (prefixWord ++ tailWord_5028567) baseStart_5028567 baseEnd_5028567 := by
    simpa [prefixWord, tailWord_5028567, baseEnd_5028567] using wordTrace_append hprefix tailTrace_5028567
  have hstable : (prefixWord ++ tailWord_5028567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028567).length < 2 ^ (prefixWord ++ tailWord_5028567).sum := by decide
  have hdescent : baseEnd_5028567 < baseStart_5028567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028581 : List Nat := [1, 3, 1, 4, 1, 3, 1, 2, 2, 2, 3]
def baseStart_5028581 : Nat := 118140960795 + 5028581 * 2 ^ 59
def prefixEnd_5028581 : Nat := 4983230072969 + 3 ^ 40 * 5028581 * 2
def baseEnd_5028581 : Nat := 2582079063066695387411483

theorem tailTrace_5028581 : CollatzResearch.WordTrace tailWord_5028581 prefixEnd_5028581 2582079063066695387411483 := by
  unfold tailWord_5028581
  simp only [CollatzResearch.WordTrace]
  refine ⟨183407416595317325106293597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122271611063544883404195731 183407416595317325106293597)
  ·
    refine ⟨68777781223243996914860099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183407416595317325106293597 68777781223243996914860099)
    ·
      refine ⟨103166671834865995372290149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68777781223243996914860099 103166671834865995372290149)
      ·
        refine ⟨19343750969037374132304403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103166671834865995372290149 19343750969037374132304403)
        ·
          refine ⟨29015626453556061198456605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19343750969037374132304403 29015626453556061198456605)
          ·
            refine ⟨10880859920083522949421227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29015626453556061198456605 10880859920083522949421227)
            ·
              refine ⟨16321289880125284424131841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10880859920083522949421227 16321289880125284424131841)
              ·
                refine ⟨12240967410093963318098881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16321289880125284424131841 12240967410093963318098881)
                ·
                  refine ⟨9180725557570472488574161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12240967410093963318098881 9180725557570472488574161)
                  ·
                    refine ⟨6885544168177854366430621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9180725557570472488574161 6885544168177854366430621)
                    ·
                      refine ⟨2582079063066695387411483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6885544168177854366430621 2582079063066695387411483)
                      ·
                        rfl

theorem cell23_5028581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_5028581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028581 prefixEnd_5028581 := by exact prefixLift 5028581
  have htrace : WordTrace (prefixWord ++ tailWord_5028581) baseStart_5028581 baseEnd_5028581 := by
    simpa [prefixWord, tailWord_5028581, baseEnd_5028581] using wordTrace_append hprefix tailTrace_5028581
  have hstable : (prefixWord ++ tailWord_5028581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028581).length < 2 ^ (prefixWord ++ tailWord_5028581).sum := by decide
  have hdescent : baseEnd_5028581 < baseStart_5028581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028661 : List Nat := [1, 3, 3, 1, 3, 2, 2, 1, 1, 6]
def baseStart_5028661 : Nat := 118140960795 + 5028661 * 2 ^ 59
def prefixEnd_5028661 : Nat := 4983230072969 + 3 ^ 40 * 5028661 * 2
def baseEnd_5028661 : Nat := 860706713839685024803705

theorem tailTrace_5028661 : CollatzResearch.WordTrace tailWord_5028661 prefixEnd_5028661 860706713839685024803705 := by
  unfold tailWord_5028661
  simp only [CollatzResearch.WordTrace]
  refine ⟨183410334435027498769205837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122273556290018332512803891 183410334435027498769205837)
  ·
    refine ⟨68778875413135312038452189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183410334435027498769205837 68778875413135312038452189)
    ·
      refine ⟨25792078279925742014419571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68778875413135312038452189 25792078279925742014419571)
      ·
        refine ⟨38688117419888613021629357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25792078279925742014419571 38688117419888613021629357)
        ·
          refine ⟨14508044032458229883111009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38688117419888613021629357 14508044032458229883111009)
          ·
            refine ⟨10881033024343672412333257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14508044032458229883111009 10881033024343672412333257)
            ·
              refine ⟨8160774768257754309249943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10881033024343672412333257 8160774768257754309249943)
              ·
                refine ⟨12241162152386631463874915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8160774768257754309249943 12241162152386631463874915)
                ·
                  refine ⟨18361743228579947195812373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12241162152386631463874915 18361743228579947195812373)
                  ·
                    refine ⟨860706713839685024803705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18361743228579947195812373 860706713839685024803705)
                    ·
                      rfl

theorem cell23_5028661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_5028661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028661 prefixEnd_5028661 := by exact prefixLift 5028661
  have htrace : WordTrace (prefixWord ++ tailWord_5028661) baseStart_5028661 baseEnd_5028661 := by
    simpa [prefixWord, tailWord_5028661, baseEnd_5028661] using wordTrace_append hprefix tailTrace_5028661
  have hstable : (prefixWord ++ tailWord_5028661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028661).length < 2 ^ (prefixWord ++ tailWord_5028661).sum := by decide
  have hdescent : baseEnd_5028661 < baseStart_5028661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028671 : List Nat := [1, 1, 2, 2, 5, 1, 2, 1, 3, 2, 3]
def baseStart_5028671 : Nat := 118140960795 + 5028671 * 2 ^ 59
def prefixEnd_5028671 : Nat := 4983230072969 + 3 ^ 40 * 5028671 * 2
def baseEnd_5028671 : Nat := 2582125276325600035286069

theorem tailTrace_5028671 : CollatzResearch.WordTrace tailWord_5028671 prefixEnd_5028671 2582125276325600035286069 := by
  unfold tailWord_5028671
  simp only [CollatzResearch.WordTrace]
  refine ⟨183410699164991270477069867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122273799443327513651379911 183410699164991270477069867)
  ·
    refine ⟨275116048747486905715604801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183410699164991270477069867 275116048747486905715604801)
    ·
      refine ⟨206337036560615179286703601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275116048747486905715604801 206337036560615179286703601)
      ·
        refine ⟨154752777420461384465027701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206337036560615179286703601 154752777420461384465027701)
        ·
          refine ⟨14508072883168254793596347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 154752777420461384465027701 14508072883168254793596347)
          ·
            refine ⟨21762109324752382190394521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14508072883168254793596347 21762109324752382190394521)
            ·
              refine ⟨16321581993564286642795891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21762109324752382190394521 16321581993564286642795891)
              ·
                refine ⟨24482372990346429964193837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16321581993564286642795891 24482372990346429964193837)
                ·
                  refine ⟨9180889871379911236572689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24482372990346429964193837 9180889871379911236572689)
                  ·
                    refine ⟨6885667403534933427429517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9180889871379911236572689 6885667403534933427429517)
                    ·
                      refine ⟨2582125276325600035286069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6885667403534933427429517 2582125276325600035286069)
                      ·
                        rfl

theorem cell23_5028671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 3, 2, 3].length) (baseStart_5028671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028671 prefixEnd_5028671 := by exact prefixLift 5028671
  have htrace : WordTrace (prefixWord ++ tailWord_5028671) baseStart_5028671 baseEnd_5028671 := by
    simpa [prefixWord, tailWord_5028671, baseEnd_5028671] using wordTrace_append hprefix tailTrace_5028671
  have hstable : (prefixWord ++ tailWord_5028671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028671).length < 2 ^ (prefixWord ++ tailWord_5028671).sum := by decide
  have hdescent : baseEnd_5028671 < baseStart_5028671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028685 : List Nat := [1, 6, 1, 2, 2, 1, 1, 3, 1, 1, 4]
def baseStart_5028685 : Nat := 118140960795 + 5028685 * 2 ^ 59
def prefixEnd_5028685 : Nat := 4983230072969 + 3 ^ 40 * 5028685 * 2
def baseEnd_5028685 : Nat := 2582132465054762980511005

theorem tailTrace_5028685 : CollatzResearch.WordTrace tailWord_5028685 prefixEnd_5028685 2582132465054762980511005 := by
  unfold tailWord_5028685
  simp only [CollatzResearch.WordTrace]
  refine ⟨183411209786940550868079509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122274139857960367245386339 183411209786940550868079509)
  ·
    refine ⟨8597400458762838321941227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 183411209786940550868079509 8597400458762838321941227)
    ·
      refine ⟨12896100688144257482911841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8597400458762838321941227 12896100688144257482911841)
      ·
        refine ⟨9672075516108193112183881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12896100688144257482911841 9672075516108193112183881)
        ·
          refine ⟨7254056637081144834137911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9672075516108193112183881 7254056637081144834137911)
          ·
            refine ⟨10881084955621717251206867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7254056637081144834137911 10881084955621717251206867)
            ·
              refine ⟨16321627433432575876810301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10881084955621717251206867 16321627433432575876810301)
              ·
                refine ⟨6120610287537215953803863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16321627433432575876810301 6120610287537215953803863)
                ·
                  refine ⟨9180915431305823930705795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6120610287537215953803863 9180915431305823930705795)
                  ·
                    refine ⟨13771373146958735896058693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9180915431305823930705795 13771373146958735896058693)
                    ·
                      refine ⟨2582132465054762980511005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13771373146958735896058693 2582132465054762980511005)
                      ·
                        rfl

theorem cell23_5028685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_5028685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028685 prefixEnd_5028685 := by exact prefixLift 5028685
  have htrace : WordTrace (prefixWord ++ tailWord_5028685) baseStart_5028685 baseEnd_5028685 := by
    simpa [prefixWord, tailWord_5028685, baseEnd_5028685] using wordTrace_append hprefix tailTrace_5028685
  have hstable : (prefixWord ++ tailWord_5028685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028685).length < 2 ^ (prefixWord ++ tailWord_5028685).sum := by decide
  have hdescent : baseEnd_5028685 < baseStart_5028685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028688 : List Nat := [2, 1, 1, 1, 1, 4, 6, 1, 1, 2, 3]
def baseStart_5028688 : Nat := 118140960795 + 5028688 * 2 ^ 59
def prefixEnd_5028688 : Nat := 4983230072969 + 3 ^ 40 * 5028688 * 2
def baseEnd_5028688 : Nat := 2582134005496726468773491

theorem tailTrace_5028688 : CollatzResearch.WordTrace tailWord_5028688 prefixEnd_5028688 2582134005496726468773491 := by
  unfold tailWord_5028688
  simp only [CollatzResearch.WordTrace]
  refine ⟨91705659602964841190219359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122274212803953121586959145 91705659602964841190219359)
  ·
    refine ⟨137558489404447261785329039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91705659602964841190219359 137558489404447261785329039)
    ·
      refine ⟨206337734106670892677993559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137558489404447261785329039 206337734106670892677993559)
      ·
        refine ⟨309506601160006339016990339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206337734106670892677993559 309506601160006339016990339)
        ·
          refine ⟨464259901740009508525485509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309506601160006339016990339 464259901740009508525485509)
          ·
            refine ⟨87048731576251782848528533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 464259901740009508525485509 87048731576251782848528533)
            ·
              refine ⟨4080409292636802321024775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 87048731576251782848528533 4080409292636802321024775)
              ·
                refine ⟨6120613938955203481537163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4080409292636802321024775 6120613938955203481537163)
                ·
                  refine ⟨9180920908432805222305745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6120613938955203481537163 9180920908432805222305745)
                  ·
                    refine ⟨6885690681324603916729309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9180920908432805222305745 6885690681324603916729309)
                    ·
                      refine ⟨2582134005496726468773491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6885690681324603916729309 2582134005496726468773491)
                      ·
                        rfl

theorem cell23_5028688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 1, 2, 3].length) (baseStart_5028688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028688 prefixEnd_5028688 := by exact prefixLift 5028688
  have htrace : WordTrace (prefixWord ++ tailWord_5028688) baseStart_5028688 baseEnd_5028688 := by
    simpa [prefixWord, tailWord_5028688, baseEnd_5028688] using wordTrace_append hprefix tailTrace_5028688
  have hstable : (prefixWord ++ tailWord_5028688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028688).length < 2 ^ (prefixWord ++ tailWord_5028688).sum := by decide
  have hdescent : baseEnd_5028688 < baseStart_5028688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028798 : List Nat := [4, 2, 1, 1, 1, 2, 2, 5, 5]
def baseStart_5028798 : Nat := 118140960795 + 5028798 * 2 ^ 59
def prefixEnd_5028798 : Nat := 4983230072969 + 3 ^ 40 * 5028798 * 2
def baseEnd_5028798 : Nat := 286910054263191226488665

theorem tailTrace_5028798 : CollatzResearch.WordTrace tailWord_5028798 prefixEnd_5028798 286910054263191226488665 := by
  unfold tailWord_5028798
  simp only [CollatzResearch.WordTrace]
  refine ⟨22926916404441396395867881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122276887490354114111295365 22926916404441396395867881)
  ·
    refine ⟨17195187303331047296900911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22926916404441396395867881 17195187303331047296900911)
    ·
      refine ⟨25792780954996570945351367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17195187303331047296900911 25792780954996570945351367)
      ·
        refine ⟨38689171432494856418027051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25792780954996570945351367 38689171432494856418027051)
        ·
          refine ⟨58033757148742284627040577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38689171432494856418027051 58033757148742284627040577)
          ·
            refine ⟨43525317861556713470280433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58033757148742284627040577 43525317861556713470280433)
            ·
              refine ⟨32643988396167535102710325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43525317861556713470280433 32643988396167535102710325)
              ·
                refine ⟨3060373912140706415879093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32643988396167535102710325 3060373912140706415879093)
                ·
                  refine ⟨286910054263191226488665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3060373912140706415879093 286910054263191226488665)
                  ·
                    rfl

theorem cell23_5028798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_5028798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028798 prefixEnd_5028798 := by exact prefixLift 5028798
  have htrace : WordTrace (prefixWord ++ tailWord_5028798) baseStart_5028798 baseEnd_5028798 := by
    simpa [prefixWord, tailWord_5028798, baseEnd_5028798] using wordTrace_append hprefix tailTrace_5028798
  have hstable : (prefixWord ++ tailWord_5028798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028798).length < 2 ^ (prefixWord ++ tailWord_5028798).sum := by decide
  have hdescent : baseEnd_5028798 < baseStart_5028798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028811 : List Nat := [1, 1, 1, 1, 3, 5, 2, 2, 2, 5]
def baseStart_5028811 : Nat := 118140960795 + 5028811 * 2 ^ 59
def prefixEnd_5028811 : Nat := 4983230072969 + 3 ^ 40 * 5028811 * 2
def baseEnd_5028811 : Nat := 860732387872409829178475

theorem tailTrace_5028811 : CollatzResearch.WordTrace tailWord_5028811 prefixEnd_5028811 860732387872409829178475 := by
  unfold tailWord_5028811
  simp only [CollatzResearch.WordTrace]
  refine ⟨183415805384484074387166287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122277203589656049591444191 183415805384484074387166287)
  ·
    refine ⟨275123708076726111580749431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183415805384484074387166287 275123708076726111580749431)
    ·
      refine ⟨412685562115089167371124147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275123708076726111580749431 412685562115089167371124147)
      ·
        refine ⟨619028343172633751056686221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412685562115089167371124147 619028343172633751056686221)
        ·
          refine ⟨232135628689737656646257333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 619028343172633751056686221 232135628689737656646257333)
          ·
            refine ⟨21762715189662905310586625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 232135628689737656646257333 21762715189662905310586625)
            ·
              refine ⟨16322036392247178982939969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21762715189662905310586625 16322036392247178982939969)
              ·
                refine ⟨12241527294185384237204977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16322036392247178982939969 12241527294185384237204977)
                ·
                  refine ⟨9181145470639038177903733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12241527294185384237204977 9181145470639038177903733)
                  ·
                    refine ⟨860732387872409829178475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9181145470639038177903733 860732387872409829178475)
                    ·
                      rfl

theorem cell23_5028811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 5].length) (baseStart_5028811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028811 prefixEnd_5028811 := by exact prefixLift 5028811
  have htrace : WordTrace (prefixWord ++ tailWord_5028811) baseStart_5028811 baseEnd_5028811 := by
    simpa [prefixWord, tailWord_5028811, baseEnd_5028811] using wordTrace_append hprefix tailTrace_5028811
  have hstable : (prefixWord ++ tailWord_5028811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028811).length < 2 ^ (prefixWord ++ tailWord_5028811).sum := by decide
  have hdescent : baseEnd_5028811 < baseStart_5028811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028815 : List Nat := [1, 1, 2, 1, 1, 8, 2, 2, 5]
def baseStart_5028815 : Nat := 118140960795 + 5028815 * 2 ^ 59
def prefixEnd_5028815 : Nat := 4983230072969 + 3 ^ 40 * 5028815 * 2
def baseEnd_5028815 : Nat := 286911024171094163542823

theorem tailTrace_5028815 : CollatzResearch.WordTrace tailWord_5028815 prefixEnd_5028815 286911024171094163542823 := by
  unfold tailWord_5028815
  simp only [CollatzResearch.WordTrace]
  refine ⟨183415951276469583070311899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122277300850979722046874599 183415951276469583070311899)
  ·
    refine ⟨275123926914704374605467849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183415951276469583070311899 275123926914704374605467849)
    ·
      refine ⟨206342945186028280954100887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275123926914704374605467849 206342945186028280954100887)
      ·
        refine ⟨309514417779042421431151331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206342945186028280954100887 309514417779042421431151331)
        ·
          refine ⟨464271626668563632146726997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309514417779042421431151331 464271626668563632146726997)
          ·
            refine ⟨5440683125022230064219457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 464271626668563632146726997 5440683125022230064219457)
            ·
              refine ⟨4080512343766672548164593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5440683125022230064219457 4080512343766672548164593)
              ·
                refine ⟨3060384257825004411123445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4080512343766672548164593 3060384257825004411123445)
                ·
                  refine ⟨286911024171094163542823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3060384257825004411123445 286911024171094163542823)
                  ·
                    rfl

theorem cell23_5028815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 2, 5].length) (baseStart_5028815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028815 prefixEnd_5028815 := by exact prefixLift 5028815
  have htrace : WordTrace (prefixWord ++ tailWord_5028815) baseStart_5028815 baseEnd_5028815 := by
    simpa [prefixWord, tailWord_5028815, baseEnd_5028815] using wordTrace_append hprefix tailTrace_5028815
  have hstable : (prefixWord ++ tailWord_5028815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028815).length < 2 ^ (prefixWord ++ tailWord_5028815).sum := by decide
  have hdescent : baseEnd_5028815 < baseStart_5028815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028871 : List Nat := [1, 1, 4, 3, 1, 1, 3, 1, 8]
def baseStart_5028871 : Nat := 118140960795 + 5028871 * 2 ^ 59
def prefixEnd_5028871 : Nat := 4983230072969 + 3 ^ 40 * 5028871 * 2
def baseEnd_5028871 : Nat := 286914219161833250309461

theorem tailTrace_5028871 : CollatzResearch.WordTrace tailWord_5028871 prefixEnd_5028871 286914219161833250309461 := by
  unfold tailWord_5028871
  simp only [CollatzResearch.WordTrace]
  refine ⟨183417993764266704634350467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122278662509511136422900311 183417993764266704634350467)
  ·
    refine ⟨275126990646400056951525701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183417993764266704634350467 275126990646400056951525701)
    ·
      refine ⟨51586310746200010678411069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 275126990646400056951525701 51586310746200010678411069)
      ·
        refine ⟨19344866529825004004404151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51586310746200010678411069 19344866529825004004404151)
        ·
          refine ⟨29017299794737506006606227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19344866529825004004404151 29017299794737506006606227)
          ·
            refine ⟨43525949692106259009909341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29017299794737506006606227 43525949692106259009909341)
            ·
              refine ⟨16322231134539847128716003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43525949692106259009909341 16322231134539847128716003)
              ·
                refine ⟨24483346701809770693074005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16322231134539847128716003 24483346701809770693074005)
                ·
                  refine ⟨286914219161833250309461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24483346701809770693074005 286914219161833250309461)
                  ·
                    rfl

theorem cell23_5028871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 8].length) (baseStart_5028871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028871 prefixEnd_5028871 := by exact prefixLift 5028871
  have htrace : WordTrace (prefixWord ++ tailWord_5028871) baseStart_5028871 baseEnd_5028871 := by
    simpa [prefixWord, tailWord_5028871, baseEnd_5028871] using wordTrace_append hprefix tailTrace_5028871
  have hstable : (prefixWord ++ tailWord_5028871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028871).length < 2 ^ (prefixWord ++ tailWord_5028871).sum := by decide
  have hdescent : baseEnd_5028871 < baseStart_5028871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028875 : List Nat := [1, 1, 1, 1, 6, 2, 2, 4, 1, 4]
def baseStart_5028875 : Nat := 118140960795 + 5028875 * 2 ^ 59
def prefixEnd_5028875 : Nat := 4983230072969 + 3 ^ 40 * 5028875 * 2
def baseEnd_5028875 : Nat := 860743342126372412378377

theorem tailTrace_5028875 : CollatzResearch.WordTrace tailWord_5028875 prefixEnd_5028875 860743342126372412378377 := by
  unfold tailWord_5028875
  simp only [CollatzResearch.WordTrace]
  refine ⟨183418139656252213317496079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122278759770834808878330719 183418139656252213317496079)
  ·
    refine ⟨275127209484378319976244119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183418139656252213317496079 275127209484378319976244119)
    ·
      refine ⟨412690814226567479964366179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275127209484378319976244119 412690814226567479964366179)
      ·
        refine ⟨619036221339851219946549269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412690814226567479964366179 619036221339851219946549269)
        ·
          refine ⟨29017322875305525934994497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 619036221339851219946549269 29017322875305525934994497)
          ·
            refine ⟨21762992156479144451245873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29017322875305525934994497 21762992156479144451245873)
            ·
              refine ⟨16322244117359358338434405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21762992156479144451245873 16322244117359358338434405)
              ·
                refine ⟨3060420772004879688456451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16322244117359358338434405 3060420772004879688456451)
                ·
                  refine ⟨4590631158007319532684677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3060420772004879688456451 4590631158007319532684677)
                  ·
                    refine ⟨860743342126372412378377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4590631158007319532684677 860743342126372412378377)
                    ·
                      rfl

theorem cell23_5028875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 4, 1, 4].length) (baseStart_5028875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028875 prefixEnd_5028875 := by exact prefixLift 5028875
  have htrace : WordTrace (prefixWord ++ tailWord_5028875) baseStart_5028875 baseEnd_5028875 := by
    simpa [prefixWord, tailWord_5028875, baseEnd_5028875] using wordTrace_append hprefix tailTrace_5028875
  have hstable : (prefixWord ++ tailWord_5028875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028875).length < 2 ^ (prefixWord ++ tailWord_5028875).sum := by decide
  have hdescent : baseEnd_5028875 < baseStart_5028875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028908 : List Nat := [2, 2, 1, 1, 1, 2, 3, 3, 1, 5, 2]
def baseStart_5028908 : Nat := 118140960795 + 5028908 * 2 ^ 59
def prefixEnd_5028908 : Nat := 4983230072969 + 3 ^ 40 * 5028908 * 2
def baseEnd_5028908 : Nat := 2582246971240715608022479

theorem tailTrace_5028908 : CollatzResearch.WordTrace tailWord_5028908 prefixEnd_5028908 2582246971240715608022479 := by
  unfold tailWord_5028908
  simp only [CollatzResearch.WordTrace]
  refine ⟨91709671632566329976723689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122279562176755106635631585 91709671632566329976723689)
  ·
    refine ⟨68782253724424747482542767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91709671632566329976723689 68782253724424747482542767)
    ·
      refine ⟨103173380586637121223814151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68782253724424747482542767 103173380586637121223814151)
      ·
        refine ⟨154760070879955681835721227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103173380586637121223814151 154760070879955681835721227)
        ·
          refine ⟨232140106319933522753581841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154760070879955681835721227 232140106319933522753581841)
          ·
            refine ⟨174105079739950142065186381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232140106319933522753581841 174105079739950142065186381)
            ·
              refine ⟨65289404902481303274444893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174105079739950142065186381 65289404902481303274444893)
              ·
                refine ⟨24483526838430488727916835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65289404902481303274444893 24483526838430488727916835)
                ·
                  refine ⟨36725290257645733091875253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24483526838430488727916835 36725290257645733091875253)
                  ·
                    refine ⟨3442995961654287477363305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36725290257645733091875253 3442995961654287477363305)
                    ·
                      refine ⟨2582246971240715608022479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3442995961654287477363305 2582246971240715608022479)
                      ·
                        rfl

theorem cell23_5028908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 5, 2].length) (baseStart_5028908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028908 prefixEnd_5028908 := by exact prefixLift 5028908
  have htrace : WordTrace (prefixWord ++ tailWord_5028908) baseStart_5028908 baseEnd_5028908 := by
    simpa [prefixWord, tailWord_5028908, baseEnd_5028908] using wordTrace_append hprefix tailTrace_5028908
  have hstable : (prefixWord ++ tailWord_5028908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028908).length < 2 ^ (prefixWord ++ tailWord_5028908).sum := by decide
  have hdescent : baseEnd_5028908 < baseStart_5028908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028925 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 4, 3, 2]
def baseStart_5028925 : Nat := 118140960795 + 5028925 * 2 ^ 59
def prefixEnd_5028925 : Nat := 4983230072969 + 3 ^ 40 * 5028925 * 2
def baseEnd_5028925 : Nat := 2582255700411842041509901

theorem tailTrace_5028925 : CollatzResearch.WordTrace tailWord_5028925 prefixEnd_5028925 2582255700411842041509901 := by
  unfold tailWord_5028925
  simp only [CollatzResearch.WordTrace]
  refine ⟨183419963306071071856816229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122279975537380714571210819 183419963306071071856816229)
  ·
    refine ⟨34391243119888325973153043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183419963306071071856816229 34391243119888325973153043)
    ·
      refine ⟨51586864679832488959729565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34391243119888325973153043 51586864679832488959729565)
      ·
        refine ⟨19345074254937183359898587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51586864679832488959729565 19345074254937183359898587)
        ·
          refine ⟨29017611382405775039847881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19345074254937183359898587 29017611382405775039847881)
          ·
            refine ⟨21763208536804331279885911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29017611382405775039847881 21763208536804331279885911)
            ·
              refine ⟨32644812805206496919828867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21763208536804331279885911 32644812805206496919828867)
              ·
                refine ⟨48967219207809745379743301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32644812805206496919828867 48967219207809745379743301)
                ·
                  refine ⟨9181353601464327258701869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48967219207809745379743301 9181353601464327258701869)
                  ·
                    refine ⟨3443007600549122722013201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9181353601464327258701869 3443007600549122722013201)
                    ·
                      refine ⟨2582255700411842041509901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3443007600549122722013201 2582255700411842041509901)
                      ·
                        rfl

theorem cell23_5028925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_5028925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028925 prefixEnd_5028925 := by exact prefixLift 5028925
  have htrace : WordTrace (prefixWord ++ tailWord_5028925) baseStart_5028925 baseEnd_5028925 := by
    simpa [prefixWord, tailWord_5028925, baseEnd_5028925] using wordTrace_append hprefix tailTrace_5028925
  have hstable : (prefixWord ++ tailWord_5028925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028925).length < 2 ^ (prefixWord ++ tailWord_5028925).sum := by decide
  have hdescent : baseEnd_5028925 < baseStart_5028925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028961 : List Nat := [1, 2, 3, 1, 1, 2, 4, 9]
def baseStart_5028961 : Nat := 118140960795 + 5028961 * 2 ^ 59
def prefixEnd_5028961 : Nat := 4983230072969 + 3 ^ 40 * 5028961 * 2
def baseEnd_5028961 : Nat := 95639784656126070394805

theorem tailTrace_5028961 : CollatzResearch.WordTrace tailWord_5028961 prefixEnd_5028961 95639784656126070394805 := by
  unfold tailWord_5028961
  simp only [CollatzResearch.WordTrace]
  refine ⟨183421276333940650005126737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122280850889293766670084491 183421276333940650005126737)
  ·
    refine ⟨137565957250455487503845053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183421276333940650005126737 137565957250455487503845053)
    ·
      refine ⟨51587233968920807813941895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137565957250455487503845053 51587233968920807813941895)
      ·
        refine ⟨77380850953381211720912843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51587233968920807813941895 77380850953381211720912843)
        ·
          refine ⟨116071276430071817581369265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77380850953381211720912843 116071276430071817581369265)
          ·
            refine ⟨87053457322553863186026949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116071276430071817581369265 87053457322553863186026949)
            ·
              refine ⟨16322523247978849347380053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87053457322553863186026949 16322523247978849347380053)
              ·
                refine ⟨95639784656126070394805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16322523247978849347380053 95639784656126070394805)
                ·
                  rfl

theorem cell23_5028961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 9].length) (baseStart_5028961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028961 prefixEnd_5028961 := by exact prefixLift 5028961
  have htrace : WordTrace (prefixWord ++ tailWord_5028961) baseStart_5028961 baseEnd_5028961 := by
    simpa [prefixWord, tailWord_5028961, baseEnd_5028961] using wordTrace_append hprefix tailTrace_5028961
  have hstable : (prefixWord ++ tailWord_5028961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028961).length < 2 ^ (prefixWord ++ tailWord_5028961).sum := by decide
  have hdescent : baseEnd_5028961 < baseStart_5028961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028982 : List Nat := [5, 1, 1, 2, 1, 1, 4, 2, 2, 4]
def baseStart_5028982 : Nat := 118140960795 + 5028982 * 2 ^ 59
def prefixEnd_5028982 : Nat := 4983230072969 + 3 ^ 40 * 5028982 * 2
def baseEnd_5028982 : Nat := 860761656269716106165713

theorem tailTrace_5028982 : CollatzResearch.WordTrace tailWord_5028982 prefixEnd_5028982 860761656269716106165713 := by
  unfold tailWord_5028982
  simp only [CollatzResearch.WordTrace]
  refine ⟨11463877641679035661977575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122281361511243047061094133 11463877641679035661977575)
  ·
    refine ⟨17195816462518553492966363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11463877641679035661977575 17195816462518553492966363)
    ·
      refine ⟨25793724693777830239449545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17195816462518553492966363 25793724693777830239449545)
      ·
        refine ⟨19345293520333372679587159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25793724693777830239449545 19345293520333372679587159)
        ·
          refine ⟨29017940280500059019380739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19345293520333372679587159 29017940280500059019380739)
          ·
            refine ⟨43526910420750088529071109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29017940280500059019380739 43526910420750088529071109)
            ·
              refine ⟨8161295703890641599200833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43526910420750088529071109 8161295703890641599200833)
              ·
                refine ⟨6120971777917981199400625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8161295703890641599200833 6120971777917981199400625)
                ·
                  refine ⟨4590728833438485899550469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6120971777917981199400625 4590728833438485899550469)
                  ·
                    refine ⟨860761656269716106165713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4590728833438485899550469 860761656269716106165713)
                    ·
                      rfl

theorem cell23_5028982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_5028982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028982 prefixEnd_5028982 := by exact prefixLift 5028982
  have htrace : WordTrace (prefixWord ++ tailWord_5028982) baseStart_5028982 baseEnd_5028982 := by
    simpa [prefixWord, tailWord_5028982, baseEnd_5028982] using wordTrace_append hprefix tailTrace_5028982
  have hstable : (prefixWord ++ tailWord_5028982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028982).length < 2 ^ (prefixWord ++ tailWord_5028982).sum := by decide
  have hdescent : baseEnd_5028982 < baseStart_5028982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028988 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 3, 3, 3]
def baseStart_5028988 : Nat := 118140960795 + 5028988 * 2 ^ 59
def prefixEnd_5028988 : Nat := 4983230072969 + 3 ^ 40 * 5028988 * 2
def baseEnd_5028988 : Nat := 2582288049693075295022111

theorem tailTrace_5028988 : CollatzResearch.WordTrace tailWord_5028988 prefixEnd_5028988 2582288049693075295022111 := by
  unfold tailWord_5028988
  simp only [CollatzResearch.WordTrace]
  refine ⟨91711130552421416808179809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122281507403228555744239745 91711130552421416808179809)
  ·
    refine ⟨68783347914316062606134857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91711130552421416808179809 68783347914316062606134857)
    ·
      refine ⟨51587510935737046954601143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68783347914316062606134857 51587510935737046954601143)
      ·
        refine ⟨77381266403605570431901715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51587510935737046954601143 77381266403605570431901715)
        ·
          refine ⟨116071899605408355647852573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77381266403605570431901715 116071899605408355647852573)
          ·
            refine ⟨43526962352028133367944715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116071899605408355647852573 43526962352028133367944715)
            ·
              refine ⟨65290443528042200051917073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43526962352028133367944715 65290443528042200051917073)
              ·
                refine ⟨48967832646031650038937805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65290443528042200051917073 48967832646031650038937805)
                ·
                  refine ⟨18362937242261868764601677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48967832646031650038937805 18362937242261868764601677)
                  ·
                    refine ⟨6886101465848200786725629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18362937242261868764601677 6886101465848200786725629)
                    ·
                      refine ⟨2582288049693075295022111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6886101465848200786725629 2582288049693075295022111)
                      ·
                        rfl

theorem cell23_5028988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_5028988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028988 prefixEnd_5028988 := by exact prefixLift 5028988
  have htrace : WordTrace (prefixWord ++ tailWord_5028988) baseStart_5028988 baseEnd_5028988 := by
    simpa [prefixWord, tailWord_5028988, baseEnd_5028988] using wordTrace_append hprefix tailTrace_5028988
  have hstable : (prefixWord ++ tailWord_5028988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028988).length < 2 ^ (prefixWord ++ tailWord_5028988).sum := by decide
  have hdescent : baseEnd_5028988 < baseStart_5028988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5028989 : List Nat := [1, 4, 1, 1, 3, 1, 3, 4, 1, 2, 2]
def baseStart_5028989 : Nat := 118140960795 + 5028989 * 2 ^ 59
def prefixEnd_5028989 : Nat := 4983230072969 + 3 ^ 40 * 5028989 * 2
def baseEnd_5028989 : Nat := 2582288563173729791109607

theorem tailTrace_5028989 : CollatzResearch.WordTrace tailWord_5028989 prefixEnd_5028989 2582288563173729791109607 := by
  unfold tailWord_5028989
  simp only [CollatzResearch.WordTrace]
  refine ⟨183422297577839210787146021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122281531718559473858097347 183422297577839210787146021)
  ·
    refine ⟨34391680795844852022589879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183422297577839210787146021 34391680795844852022589879)
    ·
      refine ⟨51587521193767278033884819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34391680795844852022589879 51587521193767278033884819)
      ·
        refine ⟨77381281790650917050827229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51587521193767278033884819 77381281790650917050827229)
        ·
          refine ⟨29017980671494093894060211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77381281790650917050827229 29017980671494093894060211)
          ·
            refine ⟨43526971007241140841090317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29017980671494093894060211 43526971007241140841090317)
            ·
              refine ⟨16322614127715427815408869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43526971007241140841090317 16322614127715427815408869)
              ·
                refine ⟨3060490148946642715389163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16322614127715427815408869 3060490148946642715389163)
                ·
                  refine ⟨4590735223419964073083745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3060490148946642715389163 4590735223419964073083745)
                  ·
                    refine ⟨3443051417564973054812809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4590735223419964073083745 3443051417564973054812809)
                    ·
                      refine ⟨2582288563173729791109607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3443051417564973054812809 2582288563173729791109607)
                      ·
                        rfl

theorem cell23_5028989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 4, 1, 2, 2].length) (baseStart_5028989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5028989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5028989 prefixEnd_5028989 := by exact prefixLift 5028989
  have htrace : WordTrace (prefixWord ++ tailWord_5028989) baseStart_5028989 baseEnd_5028989 := by
    simpa [prefixWord, tailWord_5028989, baseEnd_5028989] using wordTrace_append hprefix tailTrace_5028989
  have hstable : (prefixWord ++ tailWord_5028989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5028989).length < 2 ^ (prefixWord ++ tailWord_5028989).sum := by decide
  have hdescent : baseEnd_5028989 < baseStart_5028989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5028989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029022 : List Nat := [4, 3, 1, 1, 2, 1, 2, 2, 1, 3, 3]
def baseStart_5029022 : Nat := 118140960795 + 5029022 * 2 ^ 59
def prefixEnd_5029022 : Nat := 4983230072969 + 3 ^ 40 * 5029022 * 2
def baseEnd_5029022 : Nat := 2582305508035328161996955

theorem tailTrace_5029022 : CollatzResearch.WordTrace tailWord_5029022 prefixEnd_5029022 2582305508035328161996955 := by
  unfold tailWord_5029022
  simp only [CollatzResearch.WordTrace]
  refine ⟨22927937648339957177887165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122282334124479771615398213 22927937648339957177887165)
  ·
    refine ⟨8597976618127483941707687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22927937648339957177887165 8597976618127483941707687)
    ·
      refine ⟨12896964927191225912561531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8597976618127483941707687 12896964927191225912561531)
      ·
        refine ⟨19345447390786838868842297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12896964927191225912561531 19345447390786838868842297)
        ·
          refine ⟨14509085543090129151631723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19345447390786838868842297 14509085543090129151631723)
          ·
            refine ⟨21763628314635193727447585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14509085543090129151631723 21763628314635193727447585)
            ·
              refine ⟨16322721235976395295585689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21763628314635193727447585 16322721235976395295585689)
              ·
                refine ⟨12242040926982296471689267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16322721235976395295585689 12242040926982296471689267)
                ·
                  refine ⟨18363061390473444707533901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12242040926982296471689267 18363061390473444707533901)
                  ·
                    refine ⟨6886148021427541765325213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18363061390473444707533901 6886148021427541765325213)
                    ·
                      refine ⟨2582305508035328161996955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6886148021427541765325213 2582305508035328161996955)
                      ·
                        rfl

theorem cell23_5029022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_5029022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029022 prefixEnd_5029022 := by exact prefixLift 5029022
  have htrace : WordTrace (prefixWord ++ tailWord_5029022) baseStart_5029022 baseEnd_5029022 := by
    simpa [prefixWord, tailWord_5029022, baseEnd_5029022] using wordTrace_append hprefix tailTrace_5029022
  have hstable : (prefixWord ++ tailWord_5029022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029022).length < 2 ^ (prefixWord ++ tailWord_5029022).sum := by decide
  have hdescent : baseEnd_5029022 < baseStart_5029022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029026 : List Nat := [3, 3, 1, 3, 2, 2, 2, 1, 1, 2, 3]
def baseStart_5029026 : Nat := 118140960795 + 5029026 * 2 ^ 59
def prefixEnd_5029026 : Nat := 4983230072969 + 3 ^ 40 * 5029026 * 2
def baseEnd_5029026 : Nat := 2582307561957946146346937

theorem tailTrace_5029026 : CollatzResearch.WordTrace tailWord_5029026 prefixEnd_5029026 2582307561957946146346937 := by
  unfold tailWord_5029026
  simp only [CollatzResearch.WordTrace]
  refine ⟨45855911769676291526560733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122282431385803444070828621 45855911769676291526560733)
  ·
    refine ⟨17195966913628609322460275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45855911769676291526560733 17195966913628609322460275)
    ·
      refine ⟨25793950370442913983690413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17195966913628609322460275 25793950370442913983690413)
      ·
        refine ⟨9672731388916092743883905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25793950370442913983690413 9672731388916092743883905)
        ·
          refine ⟨7254548541687069557912929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9672731388916092743883905 7254548541687069557912929)
          ·
            refine ⟨5440911406265302168434697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7254548541687069557912929 5440911406265302168434697)
            ·
              refine ⟨4080683554698976626326023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5440911406265302168434697 4080683554698976626326023)
              ·
                refine ⟨6121025332048464939489035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4080683554698976626326023 6121025332048464939489035)
                ·
                  refine ⟨9181537998072697409233553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6121025332048464939489035 9181537998072697409233553)
                  ·
                    refine ⟨6886153498554523056925165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9181537998072697409233553 6886153498554523056925165)
                    ·
                      refine ⟨2582307561957946146346937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6886153498554523056925165 2582307561957946146346937)
                      ·
                        rfl

theorem cell23_5029026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_5029026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029026 prefixEnd_5029026 := by exact prefixLift 5029026
  have htrace : WordTrace (prefixWord ++ tailWord_5029026) baseStart_5029026 baseEnd_5029026 := by
    simpa [prefixWord, tailWord_5029026, baseEnd_5029026] using wordTrace_append hprefix tailTrace_5029026
  have hstable : (prefixWord ++ tailWord_5029026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029026).length < 2 ^ (prefixWord ++ tailWord_5029026).sum := by decide
  have hdescent : baseEnd_5029026 < baseStart_5029026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029048 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 2, 4, 3]
def baseStart_5029048 : Nat := 118140960795 + 5029048 * 2 ^ 59
def prefixEnd_5029048 : Nat := 4983230072969 + 3 ^ 40 * 5029048 * 2
def baseEnd_5029048 : Nat := 2582318858532345060271835

theorem tailTrace_5029048 : CollatzResearch.WordTrace tailWord_5029048 prefixEnd_5029048 2582318858532345060271835 := by
  unfold tailWord_5029048
  simp only [CollatzResearch.WordTrace]
  refine ⟨91712224742312731931771899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122282966323083642575695865 91712224742312731931771899)
  ·
    refine ⟨137568337113469097897657849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91712224742312731931771899 137568337113469097897657849)
    ·
      refine ⟨103176252835101823423243387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137568337113469097897657849 103176252835101823423243387)
      ·
        refine ⟨154764379252652735134865081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103176252835101823423243387 154764379252652735134865081)
        ·
          refine ⟨116073284439489551351148811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154764379252652735134865081 116073284439489551351148811)
          ·
            refine ⟨174109926659234327026723217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116073284439489551351148811 174109926659234327026723217)
            ·
              refine ⟨130582444994425745270042413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174109926659234327026723217 130582444994425745270042413)
              ·
                refine ⟨48968416872909654476265905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130582444994425745270042413 48968416872909654476265905)
                ·
                  refine ⟨36726312654682240857199429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48968416872909654476265905 36726312654682240857199429)
                  ·
                    refine ⟨6886183622752920160724893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36726312654682240857199429 6886183622752920160724893)
                    ·
                      refine ⟨2582318858532345060271835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6886183622752920160724893 2582318858532345060271835)
                      ·
                        rfl

theorem cell23_5029048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 4, 3].length) (baseStart_5029048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029048 prefixEnd_5029048 := by exact prefixLift 5029048
  have htrace : WordTrace (prefixWord ++ tailWord_5029048) baseStart_5029048 baseEnd_5029048 := by
    simpa [prefixWord, tailWord_5029048, baseEnd_5029048] using wordTrace_append hprefix tailTrace_5029048
  have hstable : (prefixWord ++ tailWord_5029048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029048).length < 2 ^ (prefixWord ++ tailWord_5029048).sum := by decide
  have hdescent : baseEnd_5029048 < baseStart_5029048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029105 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 2, 5, 2]
def baseStart_5029105 : Nat := 118140960795 + 5029105 * 2 ^ 59
def prefixEnd_5029105 : Nat := 4983230072969 + 3 ^ 40 * 5029105 * 2
def baseEnd_5029105 : Nat := 2582348126929651337259073

theorem tailTrace_5029105 : CollatzResearch.WordTrace tailWord_5029105 prefixEnd_5029105 2582348126929651337259073 := by
  unfold tailWord_5029105
  simp only [CollatzResearch.WordTrace]
  refine ⟨183426528445418962598368769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122284352296945975065579179 183426528445418962598368769)
  ·
    refine ⟨137569896334064221948776577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183426528445418962598368769 137569896334064221948776577)
    ·
      refine ⟨103177422250548166461582433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137569896334064221948776577 103177422250548166461582433)
      ·
        refine ⟨77383066687911124846186825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103177422250548166461582433 77383066687911124846186825)
        ·
          refine ⟨58037300015933343634640119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77383066687911124846186825 58037300015933343634640119)
          ·
            refine ⟨87055950023900015451960179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58037300015933343634640119 87055950023900015451960179)
            ·
              refine ⟨130583925035850023177940269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87055950023900015451960179 130583925035850023177940269)
              ·
                refine ⟨48968971888443758691727601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130583925035850023177940269 48968971888443758691727601)
                ·
                  refine ⟨36726728916332819018795701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48968971888443758691727601 36726728916332819018795701)
                  ·
                    refine ⟨3443130835906201783012097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36726728916332819018795701 3443130835906201783012097)
                    ·
                      refine ⟨2582348126929651337259073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3443130835906201783012097 2582348126929651337259073)
                      ·
                        rfl

theorem cell23_5029105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 5, 2].length) (baseStart_5029105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029105 prefixEnd_5029105 := by exact prefixLift 5029105
  have htrace : WordTrace (prefixWord ++ tailWord_5029105) baseStart_5029105 baseEnd_5029105 := by
    simpa [prefixWord, tailWord_5029105, baseEnd_5029105] using wordTrace_append hprefix tailTrace_5029105
  have hstable : (prefixWord ++ tailWord_5029105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029105).length < 2 ^ (prefixWord ++ tailWord_5029105).sum := by decide
  have hdescent : baseEnd_5029105 < baseStart_5029105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029135 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 6, 4, 2]
def baseStart_5029135 : Nat := 118140960795 + 5029135 * 2 ^ 59
def prefixEnd_5029135 : Nat := 4983230072969 + 3 ^ 40 * 5029135 * 2
def baseEnd_5029135 : Nat := 2582363531349286219883935

theorem tailTrace_5029135 : CollatzResearch.WordTrace tailWord_5029135 prefixEnd_5029135 2582363531349286219883935 := by
  unfold tailWord_5029135
  simp only [CollatzResearch.WordTrace]
  refine ⟨183427622635310277721960859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122285081756873518481307239 183427622635310277721960859)
  ·
    refine ⟨275141433952965416582941289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183427622635310277721960859 275141433952965416582941289)
    ·
      refine ⟨206356075464724062437205967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275141433952965416582941289 206356075464724062437205967)
      ·
        refine ⟨309534113197086093655808951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206356075464724062437205967 309534113197086093655808951)
        ·
          refine ⟨464301169795629140483713427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309534113197086093655808951 464301169795629140483713427)
          ·
            refine ⟨696451754693443710725570141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464301169795629140483713427 696451754693443710725570141)
            ·
              refine ⟨261169408010041391522088803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 696451754693443710725570141 261169408010041391522088803)
              ·
                refine ⟨391754112015062087283133205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261169408010041391522088803 391754112015062087283133205)
                ·
                  refine ⟨18363474000706035341396869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 391754112015062087283133205 18363474000706035341396869)
                  ·
                    refine ⟨3443151375132381626511913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18363474000706035341396869 3443151375132381626511913)
                    ·
                      refine ⟨2582363531349286219883935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3443151375132381626511913 2582363531349286219883935)
                      ·
                        rfl

theorem cell23_5029135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 4, 2].length) (baseStart_5029135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029135 prefixEnd_5029135 := by exact prefixLift 5029135
  have htrace : WordTrace (prefixWord ++ tailWord_5029135) baseStart_5029135 baseEnd_5029135 := by
    simpa [prefixWord, tailWord_5029135, baseEnd_5029135] using wordTrace_append hprefix tailTrace_5029135
  have hstable : (prefixWord ++ tailWord_5029135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029135).length < 2 ^ (prefixWord ++ tailWord_5029135).sum := by decide
  have hdescent : baseEnd_5029135 < baseStart_5029135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029172 : List Nat := [2, 5, 1, 1, 1, 1, 2, 2, 1, 4, 3]
def baseStart_5029172 : Nat := 118140960795 + 5029172 * 2 ^ 59
def prefixEnd_5029172 : Nat := 4983230072969 + 3 ^ 40 * 5029172 * 2
def baseEnd_5029172 : Nat := 2582382530133502575121265

theorem tailTrace_5029172 : CollatzResearch.WordTrace tailWord_5029172 prefixEnd_5029172 2582382530133502575121265 := by
  unfold tailWord_5029172
  simp only [CollatzResearch.WordTrace]
  refine ⟨91714486068088116520528885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122285981424117488694038513 91714486068088116520528885)
  ·
    refine ⟨8598233068883260923799583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91714486068088116520528885 8598233068883260923799583)
    ·
      refine ⟨12897349603324891385699375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8598233068883260923799583 12897349603324891385699375)
      ·
        refine ⟨19346024404987337078549063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12897349603324891385699375 19346024404987337078549063)
        ·
          refine ⟨29019036607481005617823595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19346024404987337078549063 29019036607481005617823595)
          ·
            refine ⟨43528554911221508426735393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29019036607481005617823595 43528554911221508426735393)
            ·
              refine ⟨32646416183416131320051545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43528554911221508426735393 32646416183416131320051545)
              ·
                refine ⟨24484812137562098490038659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32646416183416131320051545 24484812137562098490038659)
                ·
                  refine ⟨36727218206343147735057989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24484812137562098490038659 36727218206343147735057989)
                  ·
                    refine ⟨6886353413689340200323373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36727218206343147735057989 6886353413689340200323373)
                    ·
                      refine ⟨2582382530133502575121265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6886353413689340200323373 2582382530133502575121265)
                      ·
                        rfl

theorem cell23_5029172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_5029172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029172 prefixEnd_5029172 := by exact prefixLift 5029172
  have htrace : WordTrace (prefixWord ++ tailWord_5029172) baseStart_5029172 baseEnd_5029172 := by
    simpa [prefixWord, tailWord_5029172, baseEnd_5029172] using wordTrace_append hprefix tailTrace_5029172
  have hstable : (prefixWord ++ tailWord_5029172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029172).length < 2 ^ (prefixWord ++ tailWord_5029172).sum := by decide
  have hdescent : baseEnd_5029172 < baseStart_5029172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029202 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3]
def baseStart_5029202 : Nat := 118140960795 + 5029202 * 2 ^ 59
def prefixEnd_5029202 : Nat := 4983230072969 + 3 ^ 40 * 5029202 * 2
def baseEnd_5029202 : Nat := 2582397934553137457746127

theorem tailTrace_5029202 : CollatzResearch.WordTrace tailWord_5029202 prefixEnd_5029202 2582397934553137457746127 := by
  unfold tailWord_5029202
  simp only [CollatzResearch.WordTrace]
  refine ⟨45857516581516887041162465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122286710884045032109766573 45857516581516887041162465)
  ·
    refine ⟨34393137436137665280871849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45857516581516887041162465 34393137436137665280871849)
    ·
      refine ⟨25794853077103248960653887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34393137436137665280871849 25794853077103248960653887)
      ·
        refine ⟨38692279615654873440980831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25794853077103248960653887 38692279615654873440980831)
        ·
          refine ⟨58038419423482310161471247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38692279615654873440980831 58038419423482310161471247)
          ·
            refine ⟨87057629135223465242206871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58038419423482310161471247 87057629135223465242206871)
            ·
              refine ⟨130586443702835197863310307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87057629135223465242206871 130586443702835197863310307)
              ·
                refine ⟨195879665554252796794965461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130586443702835197863310307 195879665554252796794965461)
                ·
                  refine ⟨4590929661427799924882003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 195879665554252796794965461 4590929661427799924882003)
                  ·
                    refine ⟨6886394492141699887323005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4590929661427799924882003 6886394492141699887323005)
                    ·
                      refine ⟨2582397934553137457746127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6886394492141699887323005 2582397934553137457746127)
                      ·
                        rfl

theorem cell23_5029202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_5029202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029202 prefixEnd_5029202 := by exact prefixLift 5029202
  have htrace : WordTrace (prefixWord ++ tailWord_5029202) baseStart_5029202 baseEnd_5029202 := by
    simpa [prefixWord, tailWord_5029202, baseEnd_5029202] using wordTrace_append hprefix tailTrace_5029202
  have hstable : (prefixWord ++ tailWord_5029202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029202).length < 2 ^ (prefixWord ++ tailWord_5029202).sum := by decide
  have hdescent : baseEnd_5029202 < baseStart_5029202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029213 : List Nat := [1, 4, 5, 1, 1, 1, 2, 1, 3, 4]
def baseStart_5029213 : Nat := 118140960795 + 5029213 * 2 ^ 59
def prefixEnd_5029213 : Nat := 4983230072969 + 3 ^ 40 * 5029213 * 2
def baseEnd_5029213 : Nat := 860801194280112304902859

theorem tailTrace_5029213 : CollatzResearch.WordTrace tailWord_5029213 prefixEnd_5029213 860801194280112304902859 := by
  unfold tailWord_5029213
  simp only [CollatzResearch.WordTrace]
  refine ⟨183430467529027697043300293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122286978352685131362200195 183430467529027697043300293)
  ·
    refine ⟨34393212661692693195618805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183430467529027697043300293 34393212661692693195618805)
    ·
      refine ⟨3224363687033689987089263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34393212661692693195618805 3224363687033689987089263)
      ·
        refine ⟨4836545530550534980633895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3224363687033689987089263 4836545530550534980633895)
        ·
          refine ⟨7254818295825802470950843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4836545530550534980633895 7254818295825802470950843)
          ·
            refine ⟨10882227443738703706426265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7254818295825802470950843 10882227443738703706426265)
            ·
              refine ⟨8161670582804027779819699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10882227443738703706426265 8161670582804027779819699)
              ·
                refine ⟨12242505874206041669729549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8161670582804027779819699 12242505874206041669729549)
                ·
                  refine ⟨4590939702827265626148581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12242505874206041669729549 4590939702827265626148581)
                  ·
                    refine ⟨860801194280112304902859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4590939702827265626148581 860801194280112304902859)
                    ·
                      rfl

theorem cell23_5029213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_5029213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029213 prefixEnd_5029213 := by exact prefixLift 5029213
  have htrace : WordTrace (prefixWord ++ tailWord_5029213) baseStart_5029213 baseEnd_5029213 := by
    simpa [prefixWord, tailWord_5029213, baseEnd_5029213] using wordTrace_append hprefix tailTrace_5029213
  have hstable : (prefixWord ++ tailWord_5029213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029213).length < 2 ^ (prefixWord ++ tailWord_5029213).sum := by decide
  have hdescent : baseEnd_5029213 < baseStart_5029213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029219 : List Nat := [1, 1, 1, 5, 2, 3, 2, 1, 3, 1, 3]
def baseStart_5029219 : Nat := 118140960795 + 5029219 * 2 ^ 59
def prefixEnd_5029219 : Nat := 4983230072969 + 3 ^ 40 * 5029219 * 2
def baseEnd_5029219 : Nat := 2582406663724263891233549

theorem tailTrace_5029219 : CollatzResearch.WordTrace tailWord_5029219 prefixEnd_5029219 2582406663724263891233549 := by
  unfold tailWord_5029219
  simp only [CollatzResearch.WordTrace]
  refine ⟨183430686367005960068018711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122287124244670640045345807 183430686367005960068018711)
  ·
    refine ⟨275146029550508940102028067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183430686367005960068018711 275146029550508940102028067)
    ·
      refine ⟨412719044325763410153042101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275146029550508940102028067 412719044325763410153042101)
      ·
        refine ⟨38692410405540319701847697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 412719044325763410153042101 38692410405540319701847697)
        ·
          refine ⟨29019307804155239776385773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38692410405540319701847697 29019307804155239776385773)
          ·
            refine ⟨10882240426558214916144665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29019307804155239776385773 10882240426558214916144665)
            ·
              refine ⟨8161680319918661187108499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10882240426558214916144665 8161680319918661187108499)
              ·
                refine ⟨12242520479877991780662749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8161680319918661187108499 12242520479877991780662749)
                ·
                  refine ⟨4590945179954246917748531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12242520479877991780662749 4590945179954246917748531)
                  ·
                    refine ⟨6886417769931370376622797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4590945179954246917748531 6886417769931370376622797)
                    ·
                      refine ⟨2582406663724263891233549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6886417769931370376622797 2582406663724263891233549)
                      ·
                        rfl

theorem cell23_5029219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_5029219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029219 prefixEnd_5029219 := by exact prefixLift 5029219
  have htrace : WordTrace (prefixWord ++ tailWord_5029219) baseStart_5029219 baseEnd_5029219 := by
    simpa [prefixWord, tailWord_5029219, baseEnd_5029219] using wordTrace_append hprefix tailTrace_5029219
  have hstable : (prefixWord ++ tailWord_5029219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029219).length < 2 ^ (prefixWord ++ tailWord_5029219).sum := by decide
  have hdescent : baseEnd_5029219 < baseStart_5029219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029225 : List Nat := [1, 2, 1, 1, 1, 3, 2, 4, 3, 1, 4]
def baseStart_5029225 : Nat := 118140960795 + 5029225 * 2 ^ 59
def prefixEnd_5029225 : Nat := 4983230072969 + 3 ^ 40 * 5029225 * 2
def baseEnd_5029225 : Nat := 2582409744608190867758521

theorem tailTrace_5029225 : CollatzResearch.WordTrace tailWord_5029225 prefixEnd_5029225 2582409744608190867758521 := by
  unfold tailWord_5029225
  simp only [CollatzResearch.WordTrace]
  refine ⟨183430905204984223092737129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122287270136656148728491419 183430905204984223092737129)
  ·
    refine ⟨137573178903738167319552847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183430905204984223092737129 137573178903738167319552847)
    ·
      refine ⟨206359768355607250979329271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137573178903738167319552847 206359768355607250979329271)
      ·
        refine ⟨309539652533410876468993907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206359768355607250979329271 309539652533410876468993907)
        ·
          refine ⟨464309478800116314703490861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309539652533410876468993907 464309478800116314703490861)
          ·
            refine ⟨174116054550043618013809073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 464309478800116314703490861 174116054550043618013809073)
            ·
              refine ⟨130587040912532713510356805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174116054550043618013809073 130587040912532713510356805)
              ·
                refine ⟨24485070171099883783191901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130587040912532713510356805 24485070171099883783191901)
                ·
                  refine ⟨9181901314162456418696963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24485070171099883783191901 9181901314162456418696963)
                  ·
                    refine ⟨13772851971243684628045445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9181901314162456418696963 13772851971243684628045445)
                    ·
                      refine ⟨2582409744608190867758521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13772851971243684628045445 2582409744608190867758521)
                      ·
                        rfl

theorem cell23_5029225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 1, 4].length) (baseStart_5029225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029225 prefixEnd_5029225 := by exact prefixLift 5029225
  have htrace : WordTrace (prefixWord ++ tailWord_5029225) baseStart_5029225 baseEnd_5029225 := by
    simpa [prefixWord, tailWord_5029225, baseEnd_5029225] using wordTrace_append hprefix tailTrace_5029225
  have hstable : (prefixWord ++ tailWord_5029225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029225).length < 2 ^ (prefixWord ++ tailWord_5029225).sum := by decide
  have hdescent : baseEnd_5029225 < baseStart_5029225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029235 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 8, 4]
def baseStart_5029235 : Nat := 118140960795 + 5029235 * 2 ^ 59
def prefixEnd_5029235 : Nat := 4983230072969 + 3 ^ 40 * 5029235 * 2
def baseEnd_5029235 : Nat := 860804959804911942877825

theorem tailTrace_5029235 : CollatzResearch.WordTrace tailWord_5029235 prefixEnd_5029235 860804959804911942877825 := by
  unfold tailWord_5029235
  simp only [CollatzResearch.WordTrace]
  refine ⟨183431269934947994800601159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122287513289965329867067439 183431269934947994800601159)
  ·
    refine ⟨275146904902421992200901739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183431269934947994800601159 275146904902421992200901739)
    ·
      refine ⟨412720357353632988301352609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275146904902421992200901739 412720357353632988301352609)
      ·
        refine ⟨309540268015224741226014457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412720357353632988301352609 309540268015224741226014457)
        ·
          refine ⟨232155201011418555919510843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309540268015224741226014457 232155201011418555919510843)
          ·
            refine ⟨348232801517127833879266265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232155201011418555919510843 348232801517127833879266265)
            ·
              refine ⟨261174601137845875409449699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 348232801517127833879266265 261174601137845875409449699)
              ·
                refine ⟨391761901706768813114174549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261174601137845875409449699 391761901706768813114174549)
                ·
                  refine ⟨4590959785626197028681733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 391761901706768813114174549 4590959785626197028681733)
                  ·
                    refine ⟨860804959804911942877825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4590959785626197028681733 860804959804911942877825)
                    ·
                      rfl

theorem cell23_5029235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 8, 4].length) (baseStart_5029235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029235 prefixEnd_5029235 := by exact prefixLift 5029235
  have htrace : WordTrace (prefixWord ++ tailWord_5029235) baseStart_5029235 baseEnd_5029235 := by
    simpa [prefixWord, tailWord_5029235, baseEnd_5029235] using wordTrace_append hprefix tailTrace_5029235
  have hstable : (prefixWord ++ tailWord_5029235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029235).length < 2 ^ (prefixWord ++ tailWord_5029235).sum := by decide
  have hdescent : baseEnd_5029235 < baseStart_5029235 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029245 : List Nat := [1, 4, 1, 1, 2, 2, 1, 2, 3, 1, 5]
def baseStart_5029245 : Nat := 118140960795 + 5029245 * 2 ^ 59
def prefixEnd_5029245 : Nat := 4983230072969 + 3 ^ 40 * 5029245 * 2
def baseEnd_5029245 : Nat := 2582420014221280789508429

theorem tailTrace_5029245 : CollatzResearch.WordTrace tailWord_5029245 prefixEnd_5029245 2582420014221280789508429 := by
  unfold tailWord_5029245
  simp only [CollatzResearch.WordTrace]
  refine ⟨183431634664911766508465189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122287756443274511005643459 183431634664911766508465189)
  ·
    refine ⟨34393431499670956220337223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183431634664911766508465189 34393431499670956220337223)
    ·
      refine ⟨51590147249506434330505835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34393431499670956220337223 51590147249506434330505835)
      ·
        refine ⟨77385220874259651495758753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51590147249506434330505835 77385220874259651495758753)
        ·
          refine ⟨58038915655694738621819065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77385220874259651495758753 58038915655694738621819065)
          ·
            refine ⟨43529186741771053966364299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58038915655694738621819065 43529186741771053966364299)
            ·
              refine ⟨65293780112656580949546449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43529186741771053966364299 65293780112656580949546449)
              ·
                refine ⟨48970335084492435712159837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65293780112656580949546449 48970335084492435712159837)
                ·
                  refine ⟨18363875656684663392059939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48970335084492435712159837 18363875656684663392059939)
                  ·
                    refine ⟨27545813485026995088089909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18363875656684663392059939 27545813485026995088089909)
                    ·
                      refine ⟨2582420014221280789508429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27545813485026995088089909 2582420014221280789508429)
                      ·
                        rfl

theorem cell23_5029245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_5029245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029245 prefixEnd_5029245 := by exact prefixLift 5029245
  have htrace : WordTrace (prefixWord ++ tailWord_5029245) baseStart_5029245 baseEnd_5029245 := by
    simpa [prefixWord, tailWord_5029245, baseEnd_5029245] using wordTrace_append hprefix tailTrace_5029245
  have hstable : (prefixWord ++ tailWord_5029245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029245).length < 2 ^ (prefixWord ++ tailWord_5029245).sum := by decide
  have hdescent : baseEnd_5029245 < baseStart_5029245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029252 : List Nat := [2, 3, 2, 1, 1, 3, 1, 2, 4, 4]
def baseStart_5029252 : Nat := 118140960795 + 5029252 * 2 ^ 59
def prefixEnd_5029252 : Nat := 4983230072969 + 3 ^ 40 * 5029252 * 2
def baseEnd_5029252 : Nat := 860807869528620754040299

theorem tailTrace_5029252 : CollatzResearch.WordTrace tailWord_5029252 prefixEnd_5029252 860807869528620754040299 := by
  unfold tailWord_5029252
  simp only [CollatzResearch.WordTrace]
  refine ⟨91715944987943203351985005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122287926650590937802646673 91715944987943203351985005)
  ·
    refine ⟨34393479370478701256994377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91715944987943203351985005 34393479370478701256994377)
    ·
      refine ⟨25795109527859025942745783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34393479370478701256994377 25795109527859025942745783)
      ·
        refine ⟨38692664291788538914118675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25795109527859025942745783 38692664291788538914118675)
        ·
          refine ⟨58038996437682808371178013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38692664291788538914118675 58038996437682808371178013)
          ·
            refine ⟨21764623664131053139191755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58038996437682808371178013 21764623664131053139191755)
            ·
              refine ⟨32646935496196579708787633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21764623664131053139191755 32646935496196579708787633)
              ·
                refine ⟨24485201622147434781590725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32646935496196579708787633 24485201622147434781590725)
                ·
                  refine ⟨4590975304152644021548261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24485201622147434781590725 4590975304152644021548261)
                  ·
                    refine ⟨860807869528620754040299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4590975304152644021548261 860807869528620754040299)
                    ·
                      rfl

theorem cell23_5029252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_5029252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029252 prefixEnd_5029252 := by exact prefixLift 5029252
  have htrace : WordTrace (prefixWord ++ tailWord_5029252) baseStart_5029252 baseEnd_5029252 := by
    simpa [prefixWord, tailWord_5029252, baseEnd_5029252] using wordTrace_append hprefix tailTrace_5029252
  have hstable : (prefixWord ++ tailWord_5029252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029252).length < 2 ^ (prefixWord ++ tailWord_5029252).sum := by decide
  have hdescent : baseEnd_5029252 < baseStart_5029252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029282 : List Nat := [3, 3, 1, 2, 1, 3, 2, 8]
def baseStart_5029282 : Nat := 118140960795 + 5029282 * 2 ^ 59
def prefixEnd_5029282 : Nat := 4983230072969 + 3 ^ 40 * 5029282 * 2
def baseEnd_5029282 : Nat := 95645889370573968323917

theorem tailTrace_5029282 : CollatzResearch.WordTrace tailWord_5029282 prefixEnd_5029282 95645889370573968323917 := by
  unfold tailWord_5029282
  simp only [CollatzResearch.WordTrace]
  refine ⟨45858246041444430456890525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122288656110518481218374733 45858246041444430456890525)
  ·
    refine ⟨17196842265541661421333947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45858246041444430456890525 17196842265541661421333947)
    ·
      refine ⟨25795263398312492132000921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17196842265541661421333947 25795263398312492132000921)
      ·
        refine ⟨19346447548734369099000691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25795263398312492132000921 19346447548734369099000691)
        ·
          refine ⟨29019671323101553648501037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19346447548734369099000691 29019671323101553648501037)
          ·
            refine ⟨10882376746163082618187889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29019671323101553648501037 10882376746163082618187889)
            ·
              refine ⟨8161782559622311963640917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10882376746163082618187889 8161782559622311963640917)
              ·
                refine ⟨95645889370573968323917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8161782559622311963640917 95645889370573968323917)
                ·
                  rfl

theorem cell23_5029282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 8].length) (baseStart_5029282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029282 prefixEnd_5029282 := by exact prefixLift 5029282
  have htrace : WordTrace (prefixWord ++ tailWord_5029282) baseStart_5029282 baseEnd_5029282 := by
    simpa [prefixWord, tailWord_5029282, baseEnd_5029282] using wordTrace_append hprefix tailTrace_5029282
  have hstable : (prefixWord ++ tailWord_5029282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029282).length < 2 ^ (prefixWord ++ tailWord_5029282).sum := by decide
  have hdescent : baseEnd_5029282 < baseStart_5029282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029335 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 5]
def baseStart_5029335 : Nat := 118140960795 + 5029335 * 2 ^ 59
def prefixEnd_5029335 : Nat := 4983230072969 + 3 ^ 40 * 5029335 * 2
def baseEnd_5029335 : Nat := 2582466227480185437383015

theorem tailTrace_5029335 : CollatzResearch.WordTrace tailWord_5029335 prefixEnd_5029335 2582466227480185437383015 := by
  unfold tailWord_5029335
  simp only [CollatzResearch.WordTrace]
  refine ⟨183434917234585711879241459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122289944823057141252827639 183434917234585711879241459)
  ·
    refine ⟨275152375851878567818862189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183434917234585711879241459 275152375851878567818862189)
    ·
      refine ⟨103182140944454462932073321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275152375851878567818862189 103182140944454462932073321)
      ·
        refine ⟨77386605708340847199054991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103182140944454462932073321 77386605708340847199054991)
        ·
          refine ⟨116079908562511270798582487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77386605708340847199054991 116079908562511270798582487)
          ·
            refine ⟨174119862843766906197873731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116079908562511270798582487 174119862843766906197873731)
            ·
              refine ⟨261179794265650359296810597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174119862843766906197873731 261179794265650359296810597)
              ·
                refine ⟨48971211424809442368151987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 261179794265650359296810597 48971211424809442368151987)
                ·
                  refine ⟨73456817137214163552227981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48971211424809442368151987 73456817137214163552227981)
                  ·
                    refine ⟨27546306426455311332085493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73456817137214163552227981 27546306426455311332085493)
                    ·
                      refine ⟨2582466227480185437383015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27546306426455311332085493 2582466227480185437383015)
                      ·
                        rfl

theorem cell23_5029335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_5029335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029335 prefixEnd_5029335 := by exact prefixLift 5029335
  have htrace : WordTrace (prefixWord ++ tailWord_5029335) baseStart_5029335 baseEnd_5029335 := by
    simpa [prefixWord, tailWord_5029335, baseEnd_5029335] using wordTrace_append hprefix tailTrace_5029335
  have hstable : (prefixWord ++ tailWord_5029335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029335).length < 2 ^ (prefixWord ++ tailWord_5029335).sum := by decide
  have hdescent : baseEnd_5029335 < baseStart_5029335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029352 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 2, 4, 3]
def baseStart_5029352 : Nat := 118140960795 + 5029352 * 2 ^ 59
def prefixEnd_5029352 : Nat := 4983230072969 + 3 ^ 40 * 5029352 * 2
def baseEnd_5029352 : Nat := 2582474956651311870870437

theorem tailTrace_5029352 : CollatzResearch.WordTrace tailWord_5029352 prefixEnd_5029352 2582474956651311870870437 := by
  unfold tailWord_5029352
  simp only [CollatzResearch.WordTrace]
  refine ⟨91717768637762061891305155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122290358183682749188406873 91717768637762061891305155)
  ·
    refine ⟨137576652956643092836957733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91717768637762061891305155 137576652956643092836957733)
    ·
      refine ⟨25795622429370579906929575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137576652956643092836957733 25795622429370579906929575)
      ·
        refine ⟨38693433644055869860394363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25795622429370579906929575 38693433644055869860394363)
        ·
          refine ⟨58040150466083804790591545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38693433644055869860394363 58040150466083804790591545)
          ·
            refine ⟨43530112849562853592943659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58040150466083804790591545 43530112849562853592943659)
            ·
              refine ⟨65295169274344280389415489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43530112849562853592943659 65295169274344280389415489)
              ·
                refine ⟨48971376955758210292061617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65295169274344280389415489 48971376955758210292061617)
                ·
                  refine ⟨36728532716818657719046213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48971376955758210292061617 36728532716818657719046213)
                  ·
                    refine ⟨6886599884403498322321165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36728532716818657719046213 6886599884403498322321165)
                    ·
                      refine ⟨2582474956651311870870437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6886599884403498322321165 2582474956651311870870437)
                      ·
                        rfl

theorem cell23_5029352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_5029352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029352 prefixEnd_5029352 := by exact prefixLift 5029352
  have htrace : WordTrace (prefixWord ++ tailWord_5029352) baseStart_5029352 baseEnd_5029352 := by
    simpa [prefixWord, tailWord_5029352, baseEnd_5029352] using wordTrace_append hprefix tailTrace_5029352
  have hstable : (prefixWord ++ tailWord_5029352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029352).length < 2 ^ (prefixWord ++ tailWord_5029352).sum := by decide
  have hdescent : baseEnd_5029352 < baseStart_5029352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029366 : List Nat := [5, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2]
def baseStart_5029366 : Nat := 118140960795 + 5029366 * 2 ^ 59
def prefixEnd_5029366 : Nat := 4983230072969 + 3 ^ 40 * 5029366 * 2
def baseEnd_5029366 : Nat := 2582482145380474816095373

theorem tailTrace_5029366 : CollatzResearch.WordTrace tailWord_5029366 prefixEnd_5029366 2582482145380474816095373 := by
  unfold tailWord_5029366
  simp only [CollatzResearch.WordTrace]
  refine ⟨11464752993592087760851247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122290698598315602782413301 11464752993592087760851247)
  ·
    refine ⟨17197129490388131641276871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11464752993592087760851247 17197129490388131641276871)
    ·
      refine ⟨25795694235582197461915307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17197129490388131641276871 25795694235582197461915307)
      ·
        refine ⟨38693541353373296192872961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25795694235582197461915307 38693541353373296192872961)
        ·
          refine ⟨29020156015029972144654721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38693541353373296192872961 29020156015029972144654721)
          ·
            refine ⟨21765117011272479108491041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29020156015029972144654721 21765117011272479108491041)
            ·
              refine ⟨16323837758454359331368281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21765117011272479108491041 16323837758454359331368281)
              ·
                refine ⟨12242878318840769498526211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16323837758454359331368281 12242878318840769498526211)
                ·
                  refine ⟨18364317478261154247789317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12242878318840769498526211 18364317478261154247789317)
                  ·
                    refine ⟨3443309527173966421460497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18364317478261154247789317 3443309527173966421460497)
                    ·
                      refine ⟨2582482145380474816095373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3443309527173966421460497 2582482145380474816095373)
                      ·
                        rfl

theorem cell23_5029366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_5029366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029366 prefixEnd_5029366 := by exact prefixLift 5029366
  have htrace : WordTrace (prefixWord ++ tailWord_5029366) baseStart_5029366 baseEnd_5029366 := by
    simpa [prefixWord, tailWord_5029366, baseEnd_5029366] using wordTrace_append hprefix tailTrace_5029366
  have hstable : (prefixWord ++ tailWord_5029366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029366).length < 2 ^ (prefixWord ++ tailWord_5029366).sum := by decide
  have hdescent : baseEnd_5029366 < baseStart_5029366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029383 : List Nat := [1, 1, 4, 3, 2, 1, 3, 2, 2, 2, 2]
def baseStart_5029383 : Nat := 118140960795 + 5029383 * 2 ^ 59
def prefixEnd_5029383 : Nat := 4983230072969 + 3 ^ 40 * 5029383 * 2
def baseEnd_5029383 : Nat := 2582490874551601249582795

theorem tailTrace_5029383 : CollatzResearch.WordTrace tailWord_5029383 prefixEnd_5029383 2582490874551601249582795 := by
  unfold tailWord_5029383
  simp only [CollatzResearch.WordTrace]
  refine ⟨183436667938411816076988803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122291111958941210717992535 183436667938411816076988803)
  ·
    refine ⟨275155001907617724115483205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183436667938411816076988803 275155001907617724115483205)
    ·
      refine ⟨51591562857678323271653101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 275155001907617724115483205 51591562857678323271653101)
      ·
        refine ⟨19346836071629371226869913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51591562857678323271653101 19346836071629371226869913)
        ·
          refine ⟨14510127053722028420152435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19346836071629371226869913 14510127053722028420152435)
          ·
            refine ⟨21765190580583042630228653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14510127053722028420152435 21765190580583042630228653)
            ·
              refine ⟨8161946467718640986335745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21765190580583042630228653 8161946467718640986335745)
              ·
                refine ⟨6121459850788980739751809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8161946467718640986335745 6121459850788980739751809)
                ·
                  refine ⟨4591094888091735554813857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6121459850788980739751809 4591094888091735554813857)
                  ·
                    refine ⟨3443321166068801666110393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4591094888091735554813857 3443321166068801666110393)
                    ·
                      refine ⟨2582490874551601249582795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3443321166068801666110393 2582490874551601249582795)
                      ·
                        rfl

theorem cell23_5029383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_5029383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029383 prefixEnd_5029383 := by exact prefixLift 5029383
  have htrace : WordTrace (prefixWord ++ tailWord_5029383) baseStart_5029383 baseEnd_5029383 := by
    simpa [prefixWord, tailWord_5029383, baseEnd_5029383] using wordTrace_append hprefix tailTrace_5029383
  have hstable : (prefixWord ++ tailWord_5029383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029383).length < 2 ^ (prefixWord ++ tailWord_5029383).sum := by decide
  have hdescent : baseEnd_5029383 < baseStart_5029383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029400 : List Nat := [2, 1, 2, 3, 4, 1, 3, 1, 2, 2, 2]
def baseStart_5029400 : Nat := 118140960795 + 5029400 * 2 ^ 59
def prefixEnd_5029400 : Nat := 4983230072969 + 3 ^ 40 * 5029400 * 2
def baseEnd_5029400 : Nat := 2582499603722727683070217

theorem tailTrace_5029400 : CollatzResearch.WordTrace tailWord_5029400 prefixEnd_5029400 2582499603722727683070217 := by
  unfold tailWord_5029400
  simp only [CollatzResearch.WordTrace]
  refine ⟨91718643989675113990178827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122291525319566818653571769 91718643989675113990178827)
  ·
    refine ⟨137577965984512670985268241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91718643989675113990178827 137577965984512670985268241)
    ·
      refine ⟨103183474488384503238951181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137577965984512670985268241 103183474488384503238951181)
      ·
        refine ⟨38693802933144188714606693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103183474488384503238951181 38693802933144188714606693)
        ·
          refine ⟨7255088049964535383988755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38693802933144188714606693 7255088049964535383988755)
          ·
            refine ⟨10882632074946803075983133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7255088049964535383988755 10882632074946803075983133)
            ·
              refine ⟨4080987028105051153493675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10882632074946803075983133 4080987028105051153493675)
              ·
                refine ⟨6121480542157576730240513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4080987028105051153493675 6121480542157576730240513)
                ·
                  refine ⟨4591110406618182547680385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6121480542157576730240513 4591110406618182547680385)
                  ·
                    refine ⟨3443332804963636910760289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4591110406618182547680385 3443332804963636910760289)
                    ·
                      refine ⟨2582499603722727683070217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3443332804963636910760289 2582499603722727683070217)
                      ·
                        rfl

theorem cell23_5029400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_5029400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029400 prefixEnd_5029400 := by exact prefixLift 5029400
  have htrace : WordTrace (prefixWord ++ tailWord_5029400) baseStart_5029400 baseEnd_5029400 := by
    simpa [prefixWord, tailWord_5029400, baseEnd_5029400] using wordTrace_append hprefix tailTrace_5029400
  have hstable : (prefixWord ++ tailWord_5029400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029400).length < 2 ^ (prefixWord ++ tailWord_5029400).sum := by decide
  have hdescent : baseEnd_5029400 < baseStart_5029400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029439 : List Nat := [1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 4]
def baseStart_5029439 : Nat := 118140960795 + 5029439 * 2 ^ 59
def prefixEnd_5029439 : Nat := 4983230072969 + 3 ^ 40 * 5029439 * 2
def baseEnd_5029439 : Nat := 2582519629468253030482537

theorem tailTrace_5029439 : CollatzResearch.WordTrace tailWord_5029439 prefixEnd_5029439 2582519629468253030482537 := by
  unfold tailWord_5029439
  simp only [CollatzResearch.WordTrace]
  refine ⟨183438710426208937641027371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122292473617472625094018247 183438710426208937641027371)
  ·
    refine ⟨275158065639313406461541057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183438710426208937641027371 275158065639313406461541057)
    ·
      refine ⟨206368549229485054846155793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275158065639313406461541057 206368549229485054846155793)
      ·
        refine ⟨154776411922113791134616845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206368549229485054846155793 154776411922113791134616845)
        ·
          refine ⟨58041154470792671675481317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154776411922113791134616845 58041154470792671675481317)
          ·
            refine ⟨10882716463273625939152747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58041154470792671675481317 10882716463273625939152747)
            ·
              refine ⟨16324074694910438908729121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10882716463273625939152747 16324074694910438908729121)
              ·
                refine ⟨12243056021182829181546841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16324074694910438908729121 12243056021182829181546841)
                ·
                  refine ⟨9182292015887121886160131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12243056021182829181546841 9182292015887121886160131)
                  ·
                    refine ⟨13773438023830682829240197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9182292015887121886160131 13773438023830682829240197)
                    ·
                      refine ⟨2582519629468253030482537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13773438023830682829240197 2582519629468253030482537)
                      ·
                        rfl

theorem cell23_5029439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_5029439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029439 prefixEnd_5029439 := by exact prefixLift 5029439
  have htrace : WordTrace (prefixWord ++ tailWord_5029439) baseStart_5029439 baseEnd_5029439 := by
    simpa [prefixWord, tailWord_5029439, baseEnd_5029439] using wordTrace_append hprefix tailTrace_5029439
  have hstable : (prefixWord ++ tailWord_5029439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029439).length < 2 ^ (prefixWord ++ tailWord_5029439).sum := by decide
  have hdescent : baseEnd_5029439 < baseStart_5029439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029476 : List Nat := [2, 3, 1, 1, 2, 4, 2, 1, 2, 2, 3]
def baseStart_5029476 : Nat := 118140960795 + 5029476 * 2 ^ 59
def prefixEnd_5029476 : Nat := 4983230072969 + 3 ^ 40 * 5029476 * 2
def baseEnd_5029476 : Nat := 2582538628252469385719867

theorem tailTrace_5029476 : CollatzResearch.WordTrace tailWord_5029476 prefixEnd_5029476 2582538628252469385719867 := by
  unfold tailWord_5029476
  simp only [CollatzResearch.WordTrace]
  refine ⟨91720029963537446480062141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122293373284716595306749521 91720029963537446480062141)
  ·
    refine ⟨34395011236326542430023303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91720029963537446480062141 34395011236326542430023303)
    ·
      refine ⟨51592516854489813645034955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34395011236326542430023303 51592516854489813645034955)
      ·
        refine ⟨77388775281734720467552433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51592516854489813645034955 77388775281734720467552433)
        ·
          refine ⟨58041581461301040350664325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77388775281734720467552433 58041581461301040350664325)
          ·
            refine ⟨10882796523993945065749561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58041581461301040350664325 10882796523993945065749561)
            ·
              refine ⟨8162097392995458799312171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10882796523993945065749561 8162097392995458799312171)
              ·
                refine ⟨12243146089493188198968257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8162097392995458799312171 12243146089493188198968257)
                ·
                  refine ⟨9182359567119891149226193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12243146089493188198968257 9182359567119891149226193)
                  ·
                    refine ⟨6886769675339918361919645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9182359567119891149226193 6886769675339918361919645)
                    ·
                      refine ⟨2582538628252469385719867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6886769675339918361919645 2582538628252469385719867)
                      ·
                        rfl

theorem cell23_5029476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_5029476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029476 prefixEnd_5029476 := by exact prefixLift 5029476
  have htrace : WordTrace (prefixWord ++ tailWord_5029476) baseStart_5029476 baseEnd_5029476 := by
    simpa [prefixWord, tailWord_5029476, baseEnd_5029476] using wordTrace_append hprefix tailTrace_5029476
  have hstable : (prefixWord ++ tailWord_5029476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029476).length < 2 ^ (prefixWord ++ tailWord_5029476).sum := by decide
  have hdescent : baseEnd_5029476 < baseStart_5029476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029529 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 1, 8, 2]
def baseStart_5029529 : Nat := 118140960795 + 5029529 * 2 ^ 59
def prefixEnd_5029529 : Nat := 4983230072969 + 3 ^ 40 * 5029529 * 2
def baseEnd_5029529 : Nat := 2582565842727157678357123

theorem tailTrace_5029529 : CollatzResearch.WordTrace tailWord_5029529 prefixEnd_5029529 2582565842727157678357123 := by
  unfold tailWord_5029529
  simp only [CollatzResearch.WordTrace]
  refine ⟨183441992995882883011803641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122294661997255255341202427 183441992995882883011803641)
  ·
    refine ⟨137581494746912162258852731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183441992995882883011803641 137581494746912162258852731)
    ·
      refine ⟨206372242120368243388279097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137581494746912162258852731 206372242120368243388279097)
      ·
        refine ⟨154779181590276182541209323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206372242120368243388279097 154779181590276182541209323)
        ·
          refine ⟨232168772385414273811813985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154779181590276182541209323 232168772385414273811813985)
          ·
            refine ⟨174126579289060705358860489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232168772385414273811813985 174126579289060705358860489)
            ·
              refine ⟨130594934466795529019145367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174126579289060705358860489 130594934466795529019145367)
              ·
                refine ⟨195892401700193293528718051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130594934466795529019145367 195892401700193293528718051)
                ·
                  refine ⟨293838602550289940293077077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 195892401700193293528718051 293838602550289940293077077)
                  ·
                    refine ⟨3443421123636210237809497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 293838602550289940293077077 3443421123636210237809497)
                    ·
                      refine ⟨2582565842727157678357123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3443421123636210237809497 2582565842727157678357123)
                      ·
                        rfl

theorem cell23_5029529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 8, 2].length) (baseStart_5029529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029529 prefixEnd_5029529 := by exact prefixLift 5029529
  have htrace : WordTrace (prefixWord ++ tailWord_5029529) baseStart_5029529 baseEnd_5029529 := by
    simpa [prefixWord, tailWord_5029529, baseEnd_5029529] using wordTrace_append hprefix tailTrace_5029529
  have hstable : (prefixWord ++ tailWord_5029529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029529).length < 2 ^ (prefixWord ++ tailWord_5029529).sum := by decide
  have hdescent : baseEnd_5029529 < baseStart_5029529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029539 : List Nat := [1, 1, 1, 4, 1, 1, 4, 2, 4, 4]
def baseStart_5029539 : Nat := 118140960795 + 5029539 * 2 ^ 59
def prefixEnd_5029539 : Nat := 4983230072969 + 3 ^ 40 * 5029539 * 2
def baseEnd_5029539 : Nat := 860856992511234213077359

theorem tailTrace_5029539 : CollatzResearch.WordTrace tailWord_5029539 prefixEnd_5029539 860856992511234213077359 := by
  unfold tailWord_5029539
  simp only [CollatzResearch.WordTrace]
  refine ⟨183442357725846654719667671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122294905150564436479778447 183442357725846654719667671)
  ·
    refine ⟨275163536588769982079501507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183442357725846654719667671 275163536588769982079501507)
    ·
      refine ⟨412745304883154973119252261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275163536588769982079501507 412745304883154973119252261)
      ·
        refine ⟨77389744665591557459859799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 412745304883154973119252261 77389744665591557459859799)
        ·
          refine ⟨116084616998387336189789699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77389744665591557459859799 116084616998387336189789699)
          ·
            refine ⟨174126925497581004284684549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116084616998387336189789699 174126925497581004284684549)
            ·
              refine ⟨32648798530796438303378353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 174126925497581004284684549 32648798530796438303378353)
              ·
                refine ⟨24486598898097328727533765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32648798530796438303378353 24486598898097328727533765)
                ·
                  refine ⟨4591237293393249136412581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24486598898097328727533765 4591237293393249136412581)
                  ·
                    refine ⟨860856992511234213077359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4591237293393249136412581 860856992511234213077359)
                    ·
                      rfl

theorem cell23_5029539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 4, 4].length) (baseStart_5029539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029539 prefixEnd_5029539 := by exact prefixLift 5029539
  have htrace : WordTrace (prefixWord ++ tailWord_5029539) baseStart_5029539 baseEnd_5029539 := by
    simpa [prefixWord, tailWord_5029539, baseEnd_5029539] using wordTrace_append hprefix tailTrace_5029539
  have hstable : (prefixWord ++ tailWord_5029539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029539).length < 2 ^ (prefixWord ++ tailWord_5029539).sum := by decide
  have hdescent : baseEnd_5029539 < baseStart_5029539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029540 : List Nat := [2, 3, 1, 2, 2, 3, 2, 3, 1, 1, 3]
def baseStart_5029540 : Nat := 118140960795 + 5029540 * 2 ^ 59
def prefixEnd_5029540 : Nat := 4983230072969 + 3 ^ 40 * 5029540 * 2
def baseEnd_5029540 : Nat := 2582571491014357135319573

theorem tailTrace_5029540 : CollatzResearch.WordTrace tailWord_5029540 prefixEnd_5029540 2582571491014357135319573 := by
  unfold tailWord_5029540
  simp only [CollatzResearch.WordTrace]
  refine ⟨91721197099421515945227037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122294929465895354593636049 91721197099421515945227037)
  ·
    refine ⟨34395448912283068479460139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91721197099421515945227037 34395448912283068479460139)
    ·
      refine ⟨51593173368424602719190209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34395448912283068479460139 51593173368424602719190209)
      ·
        refine ⟨38694880026318452039392657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51593173368424602719190209 38694880026318452039392657)
        ·
          refine ⟨29021160019738839029544493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38694880026318452039392657 29021160019738839029544493)
          ·
            refine ⟨10882935007402064636079185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29021160019738839029544493 10882935007402064636079185)
            ·
              refine ⟨8162201255551548477059389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10882935007402064636079185 8162201255551548477059389)
              ·
                refine ⟨3060825470831830678897271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8162201255551548477059389 3060825470831830678897271)
                ·
                  refine ⟨4591238206247746018345907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3060825470831830678897271 4591238206247746018345907)
                  ·
                    refine ⟨6886857309371619027518861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4591238206247746018345907 6886857309371619027518861)
                    ·
                      refine ⟨2582571491014357135319573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6886857309371619027518861 2582571491014357135319573)
                      ·
                        rfl

theorem cell23_5029540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_5029540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029540 prefixEnd_5029540 := by exact prefixLift 5029540
  have htrace : WordTrace (prefixWord ++ tailWord_5029540) baseStart_5029540 baseEnd_5029540 := by
    simpa [prefixWord, tailWord_5029540, baseEnd_5029540] using wordTrace_append hprefix tailTrace_5029540
  have hstable : (prefixWord ++ tailWord_5029540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029540).length < 2 ^ (prefixWord ++ tailWord_5029540).sum := by decide
  have hdescent : baseEnd_5029540 < baseStart_5029540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029566 : List Nat := [4, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5]
def baseStart_5029566 : Nat := 118140960795 + 5029566 * 2 ^ 59
def prefixEnd_5029566 : Nat := 4983230072969 + 3 ^ 40 * 5029566 * 2
def baseEnd_5029566 : Nat := 2582584841511374033594453

theorem tailTrace_5029566 : CollatzResearch.WordTrace tailWord_5029566 prefixEnd_5029566 2582584841511374033594453 := by
  unfold tailWord_5029566
  simp only [CollatzResearch.WordTrace]
  refine ⟨22930417812093604791362569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122295561664499225553933701 22930417812093604791362569)
  ·
    refine ⟨17197813359070203593521927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22930417812093604791362569 17197813359070203593521927)
    ·
      refine ⟨25796720038605305390282891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17197813359070203593521927 25796720038605305390282891)
      ·
        refine ⟨38695080057907958085424337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25796720038605305390282891 38695080057907958085424337)
        ·
          refine ⟨29021310043430968564068253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38695080057907958085424337 29021310043430968564068253)
          ·
            refine ⟨10882991266286613211525595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29021310043430968564068253 10882991266286613211525595)
            ·
              refine ⟨16324486899429919817288393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10882991266286613211525595 16324486899429919817288393)
              ·
                refine ⟨12243365174572439862966295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16324486899429919817288393 12243365174572439862966295)
                ·
                  refine ⟨18365047761858659794449443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12243365174572439862966295 18365047761858659794449443)
                  ·
                    refine ⟨27547571642787989691674165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18365047761858659794449443 27547571642787989691674165)
                    ·
                      refine ⟨2582584841511374033594453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27547571642787989691674165 2582584841511374033594453)
                      ·
                        rfl

theorem cell23_5029566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_5029566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029566 prefixEnd_5029566 := by exact prefixLift 5029566
  have htrace : WordTrace (prefixWord ++ tailWord_5029566) baseStart_5029566 baseEnd_5029566 := by
    simpa [prefixWord, tailWord_5029566, baseEnd_5029566] using wordTrace_append hprefix tailTrace_5029566
  have hstable : (prefixWord ++ tailWord_5029566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029566).length < 2 ^ (prefixWord ++ tailWord_5029566).sum := by decide
  have hdescent : baseEnd_5029566 < baseStart_5029566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029586 : List Nat := [3, 2, 2, 2, 2, 1, 4, 7]
def baseStart_5029586 : Nat := 118140960795 + 5029586 * 2 ^ 59
def prefixEnd_5029586 : Nat := 4983230072969 + 3 ^ 40 * 5029586 * 2
def baseEnd_5029586 : Nat := 95651670782387553901643

theorem tailTrace_5029586 : CollatzResearch.WordTrace tailWord_5029586 prefixEnd_5029586 95651670782387553901643 := by
  unfold tailWord_5029586
  simp only [CollatzResearch.WordTrace]
  refine ⟨45861017989169095436657153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122296047971117587831085741 45861017989169095436657153)
  ·
    refine ⟨34395763491876821577492865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45861017989169095436657153 34395763491876821577492865)
    ·
      refine ⟨25796822618907616183119649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34395763491876821577492865 25796822618907616183119649)
      ·
        refine ⟨19347616964180712137339737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25796822618907616183119649 19347616964180712137339737)
        ·
          refine ⟨14510712723135534103004803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19347616964180712137339737 14510712723135534103004803)
          ·
            refine ⟨21766069084703301154507205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14510712723135534103004803 21766069084703301154507205)
            ·
              refine ⟨4081137953381868966470101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21766069084703301154507205 4081137953381868966470101)
              ·
                refine ⟨95651670782387553901643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4081137953381868966470101 95651670782387553901643)
                ·
                  rfl

theorem cell23_5029586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 7].length) (baseStart_5029586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029586 prefixEnd_5029586 := by exact prefixLift 5029586
  have htrace : WordTrace (prefixWord ++ tailWord_5029586) baseStart_5029586 baseEnd_5029586 := by
    simpa [prefixWord, tailWord_5029586, baseEnd_5029586] using wordTrace_append hprefix tailTrace_5029586
  have hstable : (prefixWord ++ tailWord_5029586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029586).length < 2 ^ (prefixWord ++ tailWord_5029586).sum := by decide
  have hdescent : baseEnd_5029586 < baseStart_5029586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029613 : List Nat := [1, 5, 1, 2, 1, 2, 2, 1, 4, 1, 3]
def baseStart_5029613 : Nat := 118140960795 + 5029613 * 2 ^ 59
def prefixEnd_5029613 : Nat := 4983230072969 + 3 ^ 40 * 5029613 * 2
def baseEnd_5029613 : Nat := 2582608975102135349706737

theorem tailTrace_5029613 : CollatzResearch.WordTrace tailWord_5029613 prefixEnd_5029613 2582608975102135349706737 := by
  unfold tailWord_5029613
  simp only [CollatzResearch.WordTrace]
  refine ⟨183445056727578565357861493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122296704485052376905240995 183445056727578565357861493)
  ·
    refine ⟨17197974068210490502299515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 183445056727578565357861493 17197974068210490502299515)
    ·
      refine ⟨25796961102315735753449273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17197974068210490502299515 25796961102315735753449273)
      ·
        refine ⟨19347720826736801815086955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25796961102315735753449273 19347720826736801815086955)
        ·
          refine ⟨29021581240105202722630433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19347720826736801815086955 29021581240105202722630433)
          ·
            refine ⟨21766185930078902041972825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29021581240105202722630433 21766185930078902041972825)
            ·
              refine ⟨16324639447559176531479619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21766185930078902041972825 16324639447559176531479619)
              ·
                refine ⟨24486959171338764797219429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16324639447559176531479619 24486959171338764797219429)
                ·
                  refine ⟨4591304844626018399478643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24486959171338764797219429 4591304844626018399478643)
                  ·
                    refine ⟨6886957266939027599217965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4591304844626018399478643 6886957266939027599217965)
                    ·
                      refine ⟨2582608975102135349706737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6886957266939027599217965 2582608975102135349706737)
                      ·
                        rfl

theorem cell23_5029613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_5029613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029613 prefixEnd_5029613 := by exact prefixLift 5029613
  have htrace : WordTrace (prefixWord ++ tailWord_5029613) baseStart_5029613 baseEnd_5029613 := by
    simpa [prefixWord, tailWord_5029613, baseEnd_5029613] using wordTrace_append hprefix tailTrace_5029613
  have hstable : (prefixWord ++ tailWord_5029613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029613).length < 2 ^ (prefixWord ++ tailWord_5029613).sum := by decide
  have hdescent : baseEnd_5029613 < baseStart_5029613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029649 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 4]
def baseStart_5029649 : Nat := 118140960795 + 5029649 * 2 ^ 59
def prefixEnd_5029649 : Nat := 4983230072969 + 3 ^ 40 * 5029649 * 2
def baseEnd_5029649 : Nat := 2582627460405697208856571

theorem tailTrace_5029649 : CollatzResearch.WordTrace tailWord_5029649 prefixEnd_5029649 2582627460405697208856571 := by
  unfold tailWord_5029649
  simp only [CollatzResearch.WordTrace]
  refine ⟨183446369755448143506172001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122297579836965429004114667 183446369755448143506172001)
  ·
    refine ⟨137584777316586107629629001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183446369755448143506172001 137584777316586107629629001)
    ·
      refine ⟨103188582987439580722221751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137584777316586107629629001 103188582987439580722221751)
      ·
        refine ⟨154782874481159371083332627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103188582987439580722221751 154782874481159371083332627)
        ·
          refine ⟨232174311721739056624998941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154782874481159371083332627 232174311721739056624998941)
          ·
            refine ⟨87065366895652146234374603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232174311721739056624998941 87065366895652146234374603)
            ·
              refine ⟨130598050343478219351561905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87065366895652146234374603 130598050343478219351561905)
              ·
                refine ⟨97948537757608664513671429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130598050343478219351561905 97948537757608664513671429)
                ·
                  refine ⟨18365350829551624596313393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97948537757608664513671429 18365350829551624596313393)
                  ·
                    refine ⟨13774013122163718447235045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18365350829551624596313393 13774013122163718447235045)
                    ·
                      refine ⟨2582627460405697208856571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13774013122163718447235045 2582627460405697208856571)
                      ·
                        rfl

theorem cell23_5029649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_5029649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029649 prefixEnd_5029649 := by exact prefixLift 5029649
  have htrace : WordTrace (prefixWord ++ tailWord_5029649) baseStart_5029649 baseEnd_5029649 := by
    simpa [prefixWord, tailWord_5029649, baseEnd_5029649] using wordTrace_append hprefix tailTrace_5029649
  have hstable : (prefixWord ++ tailWord_5029649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029649).length < 2 ^ (prefixWord ++ tailWord_5029649).sum := by decide
  have hdescent : baseEnd_5029649 < baseStart_5029649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029653 : List Nat := [1, 3, 2, 1, 2, 4, 1, 2, 1, 4, 2]
def baseStart_5029653 : Nat := 118140960795 + 5029653 * 2 ^ 59
def prefixEnd_5029653 : Nat := 4983230072969 + 3 ^ 40 * 5029653 * 2
def baseEnd_5029653 : Nat := 2582629514328315193206553

theorem tailTrace_5029653 : CollatzResearch.WordTrace tailWord_5029653 prefixEnd_5029653 2582629514328315193206553 := by
  unfold tailWord_5029653
  simp only [CollatzResearch.WordTrace]
  refine ⟨183446515647433652189317613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122297677098289101459545075 183446515647433652189317613)
  ·
    refine ⟨68792443367787619570994105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183446515647433652189317613 68792443367787619570994105)
    ·
      refine ⟨51594332525840714678245579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68792443367787619570994105 51594332525840714678245579)
      ·
        refine ⟨77391498788761072017368369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51594332525840714678245579 77391498788761072017368369)
        ·
          refine ⟨58043624091570804013026277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77391498788761072017368369 58043624091570804013026277)
          ·
            refine ⟨10883179517169525752442427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58043624091570804013026277 10883179517169525752442427)
            ·
              refine ⟨16324769275754288628663641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10883179517169525752442427 16324769275754288628663641)
              ·
                refine ⟨12243576956815716471497731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16324769275754288628663641 12243576956815716471497731)
                ·
                  refine ⟨18365365435223574707246597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12243576956815716471497731 18365365435223574707246597)
                  ·
                    refine ⟨3443506019104420257608737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18365365435223574707246597 3443506019104420257608737)
                    ·
                      refine ⟨2582629514328315193206553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3443506019104420257608737 2582629514328315193206553)
                      ·
                        rfl

theorem cell23_5029653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 4, 2].length) (baseStart_5029653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029653 prefixEnd_5029653 := by exact prefixLift 5029653
  have htrace : WordTrace (prefixWord ++ tailWord_5029653) baseStart_5029653 baseEnd_5029653 := by
    simpa [prefixWord, tailWord_5029653, baseEnd_5029653] using wordTrace_append hprefix tailTrace_5029653
  have hstable : (prefixWord ++ tailWord_5029653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029653).length < 2 ^ (prefixWord ++ tailWord_5029653).sum := by decide
  have hdescent : baseEnd_5029653 < baseStart_5029653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029666 : List Nat := [3, 3, 1, 1, 2, 1, 2, 2, 2, 2, 4]
def baseStart_5029666 : Nat := 118140960795 + 5029666 * 2 ^ 59
def prefixEnd_5029666 : Nat := 4983230072969 + 3 ^ 40 * 5029666 * 2
def baseEnd_5029666 : Nat := 2582636189576823642343993

theorem tailTrace_5029666 : CollatzResearch.WordTrace tailWord_5029666 prefixEnd_5029666 2582636189576823642343993 := by
  unfold tailWord_5029666
  simp only [CollatzResearch.WordTrace]
  refine ⟨45861747449096638852385213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122297993197591036939693901 45861747449096638852385213)
  ·
    refine ⟨17198155293411239569644455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45861747449096638852385213 17198155293411239569644455)
    ·
      refine ⟨25797232940116859354466683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17198155293411239569644455 25797232940116859354466683)
      ·
        refine ⟨38695849410175289031700025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25797232940116859354466683 38695849410175289031700025)
        ·
          refine ⟨29021887057631466773775019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38695849410175289031700025 29021887057631466773775019)
          ·
            refine ⟨43532830586447200160662529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29021887057631466773775019 43532830586447200160662529)
            ·
              refine ⟨32649622939835400120496897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43532830586447200160662529 32649622939835400120496897)
              ·
                refine ⟨24487217204876550090372673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32649622939835400120496897 24487217204876550090372673)
                ·
                  refine ⟨18365412903657412567779505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24487217204876550090372673 18365412903657412567779505)
                  ·
                    refine ⟨13774059677743059425834629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18365412903657412567779505 13774059677743059425834629)
                    ·
                      refine ⟨2582636189576823642343993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13774059677743059425834629 2582636189576823642343993)
                      ·
                        rfl

theorem cell23_5029666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_5029666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029666 prefixEnd_5029666 := by exact prefixLift 5029666
  have htrace : WordTrace (prefixWord ++ tailWord_5029666) baseStart_5029666 baseEnd_5029666 := by
    simpa [prefixWord, tailWord_5029666, baseEnd_5029666] using wordTrace_append hprefix tailTrace_5029666
  have hstable : (prefixWord ++ tailWord_5029666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029666).length < 2 ^ (prefixWord ++ tailWord_5029666).sum := by decide
  have hdescent : baseEnd_5029666 < baseStart_5029666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029739 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 6]
def baseStart_5029739 : Nat := 118140960795 + 5029739 * 2 ^ 59
def prefixEnd_5029739 : Nat := 4983230072969 + 3 ^ 40 * 5029739 * 2
def baseEnd_5029739 : Nat := 2582673673664601856731157

theorem tailTrace_5029739 : CollatzResearch.WordTrace tailWord_5029739 prefixEnd_5029739 2582673673664601856731157 := by
  unfold tailWord_5029739
  simp only [CollatzResearch.WordTrace]
  refine ⟨183449652325122088876948271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122299768216748059251298847 183449652325122088876948271)
  ·
    refine ⟨275174478487683133315422407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183449652325122088876948271 275174478487683133315422407)
    ·
      refine ⟨412761717731524699973133611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275174478487683133315422407 412761717731524699973133611)
      ·
        refine ⟨619142576597287049959700417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412761717731524699973133611 619142576597287049959700417)
        ·
          refine ⟨464356932447965287469775313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 619142576597287049959700417 464356932447965287469775313)
          ·
            refine ⟨348267699335973965602331485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 464356932447965287469775313 348267699335973965602331485)
            ·
              refine ⟨130600387250990237100874307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 348267699335973965602331485 130600387250990237100874307)
              ·
                refine ⟨195900580876485355651311461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130600387250990237100874307 195900580876485355651311461)
                ·
                  refine ⟨36731358914341004184620899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 195900580876485355651311461 36731358914341004184620899)
                  ·
                    refine ⟨55097038371511506276931349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36731358914341004184620899 55097038371511506276931349)
                    ·
                      refine ⟨2582673673664601856731157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55097038371511506276931349 2582673673664601856731157)
                      ·
                        rfl

theorem cell23_5029739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 6].length) (baseStart_5029739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029739 prefixEnd_5029739 := by exact prefixLift 5029739
  have htrace : WordTrace (prefixWord ++ tailWord_5029739) baseStart_5029739 baseEnd_5029739 := by
    simpa [prefixWord, tailWord_5029739, baseEnd_5029739] using wordTrace_append hprefix tailTrace_5029739
  have hstable : (prefixWord ++ tailWord_5029739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029739).length < 2 ^ (prefixWord ++ tailWord_5029739).sum := by decide
  have hdescent : baseEnd_5029739 < baseStart_5029739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029779 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 1, 11]
def baseStart_5029779 : Nat := 118140960795 + 5029779 * 2 ^ 59
def prefixEnd_5029779 : Nat := 4983230072969 + 3 ^ 40 * 5029779 * 2
def baseEnd_5029779 : Nat := 860898070963593900076991

theorem tailTrace_5029779 : CollatzResearch.WordTrace tailWord_5029779 prefixEnd_5029779 860898070963593900076991 := by
  unfold tailWord_5029779
  simp only [CollatzResearch.WordTrace]
  refine ⟨183451111244977175708404391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122300740829984783805602927 183451111244977175708404391)
  ·
    refine ⟨275176666867465763562606587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183451111244977175708404391 275176666867465763562606587)
    ·
      refine ⟨412765000301198645343909881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275176666867465763562606587 412765000301198645343909881)
      ·
        refine ⟨309573750225898984007932411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412765000301198645343909881 309573750225898984007932411)
        ·
          refine ⟨464360625338848476011898617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309573750225898984007932411 464360625338848476011898617)
          ·
            refine ⟨348270469004136357008923963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 464360625338848476011898617 348270469004136357008923963)
            ·
              refine ⟨522405703506204535513385945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348270469004136357008923963 522405703506204535513385945)
              ·
                refine ⟨391804277629653401635039459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 522405703506204535513385945 391804277629653401635039459)
                ·
                  refine ⟨587706416444480102452559189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 391804277629653401635039459 587706416444480102452559189)
                  ·
                    refine ⟨860898070963593900076991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 587706416444480102452559189 860898070963593900076991)
                    ·
                      rfl

theorem cell23_5029779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 11].length) (baseStart_5029779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029779 prefixEnd_5029779 := by exact prefixLift 5029779
  have htrace : WordTrace (prefixWord ++ tailWord_5029779) baseStart_5029779 baseEnd_5029779 := by
    simpa [prefixWord, tailWord_5029779, baseEnd_5029779] using wordTrace_append hprefix tailTrace_5029779
  have hstable : (prefixWord ++ tailWord_5029779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029779).length < 2 ^ (prefixWord ++ tailWord_5029779).sum := by decide
  have hdescent : baseEnd_5029779 < baseStart_5029779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029780 : List Nat := [2, 4, 2, 1, 1, 3, 1, 2, 2, 2, 3]
def baseStart_5029780 : Nat := 118140960795 + 5029780 * 2 ^ 59
def prefixEnd_5029780 : Nat := 4983230072969 + 3 ^ 40 * 5029780 * 2
def baseEnd_5029780 : Nat := 2582694726371436196318469

theorem tailTrace_5029780 : CollatzResearch.WordTrace tailWord_5029780 prefixEnd_5029780 2582694726371436196318469 := by
  unfold tailWord_5029780
  simp only [CollatzResearch.WordTrace]
  refine ⟨91725573858986776439595397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122300765145315701919460529 91725573858986776439595397)
  ·
    refine ⟨17198545098560020582424137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91725573858986776439595397 17198545098560020582424137)
    ·
      refine ⟨12898908823920015436818103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17198545098560020582424137 12898908823920015436818103)
      ·
        refine ⟨19348363235880023155227155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12898908823920015436818103 19348363235880023155227155)
        ·
          refine ⟨29022544853820034732840733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19348363235880023155227155 29022544853820034732840733)
          ·
            refine ⟨10883454320182513024815275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29022544853820034732840733 10883454320182513024815275)
            ·
              refine ⟨16325181480273769537222913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10883454320182513024815275 16325181480273769537222913)
              ·
                refine ⟨12243886110205327152917185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16325181480273769537222913 12243886110205327152917185)
                ·
                  refine ⟨9182914582653995364687889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12243886110205327152917185 9182914582653995364687889)
                  ·
                    refine ⟨6887185936990496523515917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9182914582653995364687889 6887185936990496523515917)
                    ·
                      refine ⟨2582694726371436196318469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6887185936990496523515917 2582694726371436196318469)
                      ·
                        rfl

theorem cell23_5029780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_5029780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029780 prefixEnd_5029780 := by exact prefixLift 5029780
  have htrace : WordTrace (prefixWord ++ tailWord_5029780) baseStart_5029780 baseEnd_5029780 := by
    simpa [prefixWord, tailWord_5029780, baseEnd_5029780] using wordTrace_append hprefix tailTrace_5029780
  have hstable : (prefixWord ++ tailWord_5029780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029780).length < 2 ^ (prefixWord ++ tailWord_5029780).sum := by decide
  have hdescent : baseEnd_5029780 < baseStart_5029780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029813 : List Nat := [1, 3, 3, 2, 1, 3, 1, 1, 3, 5]
def baseStart_5029813 : Nat := 118140960795 + 5029813 * 2 ^ 59
def prefixEnd_5029813 : Nat := 4983230072969 + 3 ^ 40 * 5029813 * 2
def baseEnd_5029813 : Nat := 860903890411011522401939

theorem tailTrace_5029813 : CollatzResearch.WordTrace tailWord_5029813 prefixEnd_5029813 860903890411011522401939 := by
  unfold tailWord_5029813
  simp only [CollatzResearch.WordTrace]
  refine ⟨183452351326853999515142093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122301567551235999676761395 183452351326853999515142093)
  ·
    refine ⟨68794631747570249818178285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183452351326853999515142093 68794631747570249818178285)
    ·
      refine ⟨25797986905338843681816857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68794631747570249818178285 25797986905338843681816857)
      ·
        refine ⟨19348490179004132761362643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25797986905338843681816857 19348490179004132761362643)
        ·
          refine ⟨29022735268506199142043965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19348490179004132761362643 29022735268506199142043965)
          ·
            refine ⟨10883525725689824678266487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29022735268506199142043965 10883525725689824678266487)
            ·
              refine ⟨16325288588534737017399731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10883525725689824678266487 16325288588534737017399731)
              ·
                refine ⟨24487932882802105526099597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16325288588534737017399731 24487932882802105526099597)
                ·
                  refine ⟨9182974831050789572287349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24487932882802105526099597 9182974831050789572287349)
                  ·
                    refine ⟨860903890411011522401939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9182974831050789572287349 860903890411011522401939)
                    ·
                      rfl

theorem cell23_5029813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_5029813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029813 prefixEnd_5029813 := by exact prefixLift 5029813
  have htrace : WordTrace (prefixWord ++ tailWord_5029813) baseStart_5029813 baseEnd_5029813 := by
    simpa [prefixWord, tailWord_5029813, baseEnd_5029813] using wordTrace_append hprefix tailTrace_5029813
  have hstable : (prefixWord ++ tailWord_5029813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029813).length < 2 ^ (prefixWord ++ tailWord_5029813).sum := by decide
  have hdescent : baseEnd_5029813 < baseStart_5029813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029870 : List Nat := [4, 1, 2, 1, 3, 1, 2, 1, 3, 2, 3]
def baseStart_5029870 : Nat := 118140960795 + 5029870 * 2 ^ 59
def prefixEnd_5029870 : Nat := 4983230072969 + 3 ^ 40 * 5029870 * 2
def baseEnd_5029870 : Nat := 2582740939630340844193055

theorem tailTrace_5029870 : CollatzResearch.WordTrace tailWord_5029870 prefixEnd_5029870 2582740939630340844193055 := by
  unfold tailWord_5029870
  simp only [CollatzResearch.WordTrace]
  refine ⟨22931803785955937281245883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122302953525098332166644709 22931803785955937281245883)
  ·
    refine ⟨34397705678933905921868825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22931803785955937281245883 34397705678933905921868825)
    ·
      refine ⟨25798279259200429441401619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34397705678933905921868825 25798279259200429441401619)
      ·
        refine ⟨38697418888800644162102429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25798279259200429441401619 38697418888800644162102429)
        ·
          refine ⟨14511532083300241560788411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38697418888800644162102429 14511532083300241560788411)
          ·
            refine ⟨21767298124950362341182617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14511532083300241560788411 21767298124950362341182617)
            ·
              refine ⟨16325473593712771755886963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21767298124950362341182617 16325473593712771755886963)
              ·
                refine ⟨24488210390569157633830445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16325473593712771755886963 24488210390569157633830445)
                ·
                  refine ⟨9183078896463434112686417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24488210390569157633830445 9183078896463434112686417)
                  ·
                    refine ⟨6887309172347575584514813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9183078896463434112686417 6887309172347575584514813)
                    ·
                      refine ⟨2582740939630340844193055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6887309172347575584514813 2582740939630340844193055)
                      ·
                        rfl

theorem cell23_5029870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_5029870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029870 prefixEnd_5029870 := by exact prefixLift 5029870
  have htrace : WordTrace (prefixWord ++ tailWord_5029870) baseStart_5029870 baseEnd_5029870 := by
    simpa [prefixWord, tailWord_5029870, baseEnd_5029870] using wordTrace_append hprefix tailTrace_5029870
  have hstable : (prefixWord ++ tailWord_5029870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029870).length < 2 ^ (prefixWord ++ tailWord_5029870).sum := by decide
  have hdescent : baseEnd_5029870 < baseStart_5029870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029883 : List Nat := [1, 1, 1, 1, 1, 3, 6, 2, 1, 3, 3]
def baseStart_5029883 : Nat := 118140960795 + 5029883 * 2 ^ 59
def prefixEnd_5029883 : Nat := 4983230072969 + 3 ^ 40 * 5029883 * 2
def baseEnd_5029883 : Nat := 2582747614878849293330495

theorem tailTrace_5029883 : CollatzResearch.WordTrace tailWord_5029883 prefixEnd_5029883 2582747614878849293330495 := by
  unfold tailWord_5029883
  simp only [CollatzResearch.WordTrace]
  refine ⟨183454904436600401470190303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122303269624400267646793535 183454904436600401470190303)
  ·
    refine ⟨275182356654900602205285455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183454904436600401470190303 275182356654900602205285455)
    ·
      refine ⟨412773534982350903307928183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275182356654900602205285455 412773534982350903307928183)
      ·
        refine ⟨619160302473526354961892275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412773534982350903307928183 619160302473526354961892275)
        ·
          refine ⟨928740453710289532442838413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619160302473526354961892275 928740453710289532442838413)
          ·
            refine ⟨348277670141358574666064405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 928740453710289532442838413 348277670141358574666064405)
            ·
              refine ⟨16325515787876183187471769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 348277670141358574666064405 16325515787876183187471769)
              ·
                refine ⟨12244136840907137390603827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16325515787876183187471769 12244136840907137390603827)
                ·
                  refine ⟨18366205261360706085905741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12244136840907137390603827 18366205261360706085905741)
                  ·
                    refine ⟨6887326973010264782214653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18366205261360706085905741 6887326973010264782214653)
                    ·
                      refine ⟨2582747614878849293330495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6887326973010264782214653 2582747614878849293330495)
                      ·
                        rfl

theorem cell23_5029883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 3, 3].length) (baseStart_5029883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029883 prefixEnd_5029883 := by exact prefixLift 5029883
  have htrace : WordTrace (prefixWord ++ tailWord_5029883) baseStart_5029883 baseEnd_5029883 := by
    simpa [prefixWord, tailWord_5029883, baseEnd_5029883] using wordTrace_append hprefix tailTrace_5029883
  have hstable : (prefixWord ++ tailWord_5029883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029883).length < 2 ^ (prefixWord ++ tailWord_5029883).sum := by decide
  have hdescent : baseEnd_5029883 < baseStart_5029883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029884 : List Nat := [2, 2, 2, 1, 2, 2, 4, 3, 1, 2, 2]
def baseStart_5029884 : Nat := 118140960795 + 5029884 * 2 ^ 59
def prefixEnd_5029884 : Nat := 4983230072969 + 3 ^ 40 * 5029884 * 2
def baseEnd_5029884 : Nat := 2582748128359503789417991

theorem tailTrace_5029884 : CollatzResearch.WordTrace tailWord_5029884 prefixEnd_5029884 2582748128359503789417991 := by
  unfold tailWord_5029884
  simp only [CollatzResearch.WordTrace]
  refine ⟨91727470454798389320488353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122303293939731185760651137 91727470454798389320488353)
  ·
    refine ⟨68795602841098791990366265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91727470454798389320488353 68795602841098791990366265)
    ·
      refine ⟨51596702130824093992774699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68795602841098791990366265 51596702130824093992774699)
      ·
        refine ⟨77395053196236140989162049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51596702130824093992774699 77395053196236140989162049)
        ·
          refine ⟨58046289897177105741871537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77395053196236140989162049 58046289897177105741871537)
          ·
            refine ⟨43534717422882829306403653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58046289897177105741871537 43534717422882829306403653)
            ·
              refine ⟨8162759516790530494950685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43534717422882829306403653 8162759516790530494950685)
              ·
                refine ⟨3061034818796448935606507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8162759516790530494950685 3061034818796448935606507)
                ·
                  refine ⟨4591552228194673403409761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3061034818796448935606507 4591552228194673403409761)
                  ·
                    refine ⟨3443664171146005052557321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4591552228194673403409761 3443664171146005052557321)
                    ·
                      refine ⟨2582748128359503789417991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3443664171146005052557321 2582748128359503789417991)
                      ·
                        rfl

theorem cell23_5029884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 3, 1, 2, 2].length) (baseStart_5029884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029884 prefixEnd_5029884 := by exact prefixLift 5029884
  have htrace : WordTrace (prefixWord ++ tailWord_5029884) baseStart_5029884 baseEnd_5029884 := by
    simpa [prefixWord, tailWord_5029884, baseEnd_5029884] using wordTrace_append hprefix tailTrace_5029884
  have hstable : (prefixWord ++ tailWord_5029884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029884).length < 2 ^ (prefixWord ++ tailWord_5029884).sum := by decide
  have hdescent : baseEnd_5029884 < baseStart_5029884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029900 : List Nat := [2, 2, 1, 2, 3, 1, 3, 1, 4, 1, 3]
def baseStart_5029900 : Nat := 118140960795 + 5029900 * 2 ^ 59
def prefixEnd_5029900 : Nat := 4983230072969 + 3 ^ 40 * 5029900 * 2
def baseEnd_5029900 : Nat := 2582756344049975726817917

theorem tailTrace_5029900 : CollatzResearch.WordTrace tailWord_5029900 prefixEnd_5029900 2582756344049975726817917 := by
  unfold tailWord_5029900
  simp only [CollatzResearch.WordTrace]
  refine ⟨91727762238769406686779577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122303682985025875582372769 91727762238769406686779577)
  ·
    refine ⟨68795821679077055015084683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91727762238769406686779577 68795821679077055015084683)
    ·
      refine ⟨103193732518615582522627025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68795821679077055015084683 103193732518615582522627025)
      ·
        refine ⟨77395299388961686891970269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103193732518615582522627025 77395299388961686891970269)
        ·
          refine ⟨29023237270860632584488851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77395299388961686891970269 29023237270860632584488851)
          ·
            refine ⟨43534855906290948876733277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29023237270860632584488851 43534855906290948876733277)
            ·
              refine ⟨16325570964859105828774979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43534855906290948876733277 16325570964859105828774979)
              ·
                refine ⟨24488356447288658743162469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16325570964859105828774979 24488356447288658743162469)
                ·
                  refine ⟨4591566833866623514342963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24488356447288658743162469 4591566833866623514342963)
                  ·
                    refine ⟨6887350250799935271514445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4591566833866623514342963 6887350250799935271514445)
                    ·
                      refine ⟨2582756344049975726817917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6887350250799935271514445 2582756344049975726817917)
                      ·
                        rfl

theorem cell23_5029900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_5029900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029900 prefixEnd_5029900 := by exact prefixLift 5029900
  have htrace : WordTrace (prefixWord ++ tailWord_5029900) baseStart_5029900 baseEnd_5029900 := by
    simpa [prefixWord, tailWord_5029900, baseEnd_5029900] using wordTrace_append hprefix tailTrace_5029900
  have hstable : (prefixWord ++ tailWord_5029900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029900).length < 2 ^ (prefixWord ++ tailWord_5029900).sum := by decide
  have hdescent : baseEnd_5029900 < baseStart_5029900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029917 : List Nat := [1, 4, 2, 2, 2, 3, 1, 1, 1, 3, 3]
def baseStart_5029917 : Nat := 118140960795 + 5029917 * 2 ^ 59
def prefixEnd_5029917 : Nat := 4983230072969 + 3 ^ 40 * 5029917 * 2
def baseEnd_5029917 : Nat := 2582765073221102160305339

theorem tailTrace_5029917 : CollatzResearch.WordTrace tailWord_5029917 prefixEnd_5029917 2582765073221102160305339 := by
  unfold tailWord_5029917
  simp only [CollatzResearch.WordTrace]
  refine ⟨183456144518477225276928005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122304096345651483517952003 183456144518477225276928005)
  ·
    refine ⟨34398027097214479739424001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183456144518477225276928005 34398027097214479739424001)
    ·
      refine ⟨25798520322910859804568001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34398027097214479739424001 25798520322910859804568001)
      ·
        refine ⟨19348890242183144853426001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25798520322910859804568001 19348890242183144853426001)
        ·
          refine ⟨14511667681637358640069501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19348890242183144853426001 14511667681637358640069501)
          ·
            refine ⟨5441875380614009490026063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14511667681637358640069501 5441875380614009490026063)
            ·
              refine ⟨8162813070921014235039095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5441875380614009490026063 8162813070921014235039095)
              ·
                refine ⟨12244219606381521352558643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8162813070921014235039095 12244219606381521352558643)
                ·
                  refine ⟨18366329409572282028837965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12244219606381521352558643 18366329409572282028837965)
                  ·
                    refine ⟨6887373528589605760814237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18366329409572282028837965 6887373528589605760814237)
                    ·
                      refine ⟨2582765073221102160305339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6887373528589605760814237 2582765073221102160305339)
                      ·
                        rfl

theorem cell23_5029917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_5029917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029917 prefixEnd_5029917 := by exact prefixLift 5029917
  have htrace : WordTrace (prefixWord ++ tailWord_5029917) baseStart_5029917 baseEnd_5029917 := by
    simpa [prefixWord, tailWord_5029917, baseEnd_5029917] using wordTrace_append hprefix tailTrace_5029917
  have hstable : (prefixWord ++ tailWord_5029917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029917).length < 2 ^ (prefixWord ++ tailWord_5029917).sum := by decide
  have hdescent : baseEnd_5029917 < baseStart_5029917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5029957 : List Nat := [1, 3, 1, 1, 1, 3, 1, 6, 2, 2, 2]
def baseStart_5029957 : Nat := 118140960795 + 5029957 * 2 ^ 59
def prefixEnd_5029957 : Nat := 4983230072969 + 3 ^ 40 * 5029957 * 2
def baseEnd_5029957 : Nat := 2582785612447282003805155

theorem tailTrace_5029957 : CollatzResearch.WordTrace tailWord_5029957 prefixEnd_5029957 2582785612447282003805155 := by
  unfold tailWord_5029957
  simp only [CollatzResearch.WordTrace]
  refine ⟨183457603438332312108384125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122305068958888208072256083 183457603438332312108384125)
  ·
    refine ⟨68796601289374617040644047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183457603438332312108384125 68796601289374617040644047)
    ·
      refine ⟨103194901934061925560966071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68796601289374617040644047 103194901934061925560966071)
      ·
        refine ⟨154792352901092888341449107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103194901934061925560966071 154792352901092888341449107)
        ·
          refine ⟨232188529351639332512173661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154792352901092888341449107 232188529351639332512173661)
          ·
            refine ⟨87070698506864749692065123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232188529351639332512173661 87070698506864749692065123)
            ·
              refine ⟨130606047760297124538097685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87070698506864749692065123 130606047760297124538097685)
              ·
                refine ⟨6122158488763927712723329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 130606047760297124538097685 6122158488763927712723329)
                ·
                  refine ⟨4591618866572945784542497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6122158488763927712723329 4591618866572945784542497)
                  ·
                    refine ⟨3443714149929709338406873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4591618866572945784542497 3443714149929709338406873)
                    ·
                      refine ⟨2582785612447282003805155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3443714149929709338406873 2582785612447282003805155)
                      ·
                        rfl

theorem cell23_5029957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 2, 2, 2].length) (baseStart_5029957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5029957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5029957 prefixEnd_5029957 := by exact prefixLift 5029957
  have htrace : WordTrace (prefixWord ++ tailWord_5029957) baseStart_5029957 baseEnd_5029957 := by
    simpa [prefixWord, tailWord_5029957, baseEnd_5029957] using wordTrace_append hprefix tailTrace_5029957
  have hstable : (prefixWord ++ tailWord_5029957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5029957).length < 2 ^ (prefixWord ++ tailWord_5029957).sum := by decide
  have hdescent : baseEnd_5029957 < baseStart_5029957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5029957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030047 : List Nat := [1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 4]
def baseStart_5030047 : Nat := 118140960795 + 5030047 * 2 ^ 59
def prefixEnd_5030047 : Nat := 4983230072969 + 3 ^ 40 * 5030047 * 2
def baseEnd_5030047 : Nat := 2582831825706186651679741

theorem tailTrace_5030047 : CollatzResearch.WordTrace tailWord_5030047 prefixEnd_5030047 2582831825706186651679741 := by
  unfold tailWord_5030047
  simp only [CollatzResearch.WordTrace]
  refine ⟨183460886008006257479160395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122307257338670838319440263 183460886008006257479160395)
  ·
    refine ⟨275191329012009386218740593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183460886008006257479160395 275191329012009386218740593)
    ·
      refine ⟨206393496759007039664055445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275191329012009386218740593 206393496759007039664055445)
      ·
        refine ⟨9674695160578454984252599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 206393496759007039664055445 9674695160578454984252599)
        ·
          refine ⟨14512042740867682476378899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9674695160578454984252599 14512042740867682476378899)
          ·
            refine ⟨21768064111301523714568349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14512042740867682476378899 21768064111301523714568349)
            ·
              refine ⟨8163024041738071392963131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21768064111301523714568349 8163024041738071392963131)
              ·
                refine ⟨12244536062607107089444697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8163024041738071392963131 12244536062607107089444697)
                ·
                  refine ⟨9183402046955330317083523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12244536062607107089444697 9183402046955330317083523)
                  ·
                    refine ⟨13775103070432995475625285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9183402046955330317083523 13775103070432995475625285)
                    ·
                      refine ⟨2582831825706186651679741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13775103070432995475625285 2582831825706186651679741)
                      ·
                        rfl

theorem cell23_5030047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_5030047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030047 prefixEnd_5030047 := by exact prefixLift 5030047
  have htrace : WordTrace (prefixWord ++ tailWord_5030047) baseStart_5030047 baseEnd_5030047 := by
    simpa [prefixWord, tailWord_5030047, baseEnd_5030047] using wordTrace_append hprefix tailTrace_5030047
  have hstable : (prefixWord ++ tailWord_5030047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030047).length < 2 ^ (prefixWord ++ tailWord_5030047).sum := by decide
  have hdescent : baseEnd_5030047 < baseStart_5030047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030053 : List Nat := [1, 3, 1, 2, 1, 3, 2, 2, 8]
def baseStart_5030053 : Nat := 118140960795 + 5030053 * 2 ^ 59
def prefixEnd_5030053 : Nat := 4983230072969 + 3 ^ 40 * 5030053 * 2
def baseEnd_5030053 : Nat := 286981656287790403133857

theorem tailTrace_5030053 : CollatzResearch.WordTrace tailWord_5030053 prefixEnd_5030053 286981656287790403133857 := by
  unfold tailWord_5030053
  simp only [CollatzResearch.WordTrace]
  refine ⟨183461104845984520503878813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122307403230656347002585875 183461104845984520503878813)
  ·
    refine ⟨68797914317244195188954555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183461104845984520503878813 68797914317244195188954555)
    ·
      refine ⟨103196871475866292783431833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68797914317244195188954555 103196871475866292783431833)
      ·
        refine ⟨77397653606899719587573875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103196871475866292783431833 77397653606899719587573875)
        ·
          refine ⟨116096480410349579381360813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77397653606899719587573875 116096480410349579381360813)
          ·
            refine ⟨43536180153881092268010305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116096480410349579381360813 43536180153881092268010305)
            ·
              refine ⟨32652135115410819201007729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43536180153881092268010305 32652135115410819201007729)
              ·
                refine ⟨24489101336558114400755797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32652135115410819201007729 24489101336558114400755797)
                ·
                  refine ⟨286981656287790403133857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24489101336558114400755797 286981656287790403133857)
                  ·
                    rfl

theorem cell23_5030053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 8].length) (baseStart_5030053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030053 prefixEnd_5030053 := by exact prefixLift 5030053
  have htrace : WordTrace (prefixWord ++ tailWord_5030053) baseStart_5030053 baseEnd_5030053 := by
    simpa [prefixWord, tailWord_5030053, baseEnd_5030053] using wordTrace_append hprefix tailTrace_5030053
  have hstable : (prefixWord ++ tailWord_5030053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030053).length < 2 ^ (prefixWord ++ tailWord_5030053).sum := by decide
  have hdescent : baseEnd_5030053 < baseStart_5030053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030073 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 1, 1, 8]
def baseStart_5030073 : Nat := 118140960795 + 5030073 * 2 ^ 59
def prefixEnd_5030073 : Nat := 4983230072969 + 3 ^ 40 * 5030073 * 2
def baseEnd_5030073 : Nat := 2582845176203203549954621

theorem tailTrace_5030073 : CollatzResearch.WordTrace tailWord_5030073 prefixEnd_5030073 2582845176203203549954621 := by
  unfold tailWord_5030073
  simp only [CollatzResearch.WordTrace]
  refine ⟨183461834305912063919606873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122307889537274709279737915 183461834305912063919606873)
  ·
    refine ⟨137596375729434047939705155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183461834305912063919606873 137596375729434047939705155)
    ·
      refine ⟨206394563594151071909557733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137596375729434047939705155 206394563594151071909557733)
      ·
        refine ⟨38698980673903325983042075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 206394563594151071909557733 38698980673903325983042075)
        ·
          refine ⟨58048471010854988974563113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38698980673903325983042075 58048471010854988974563113)
          ·
            refine ⟨43536353258141241730922335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58048471010854988974563113 43536353258141241730922335)
            ·
              refine ⟨65304529887211862596383503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43536353258141241730922335 65304529887211862596383503)
              ·
                refine ⟨97956794830817793894575255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65304529887211862596383503 97956794830817793894575255)
                ·
                  refine ⟨146935192246226690841862883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97956794830817793894575255 146935192246226690841862883)
                  ·
                    refine ⟨220402788369340036262794325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 146935192246226690841862883 220402788369340036262794325)
                    ·
                      refine ⟨2582845176203203549954621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 220402788369340036262794325 2582845176203203549954621)
                      ·
                        rfl

theorem cell23_5030073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_5030073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030073 prefixEnd_5030073 := by exact prefixLift 5030073
  have htrace : WordTrace (prefixWord ++ tailWord_5030073) baseStart_5030073 baseEnd_5030073 := by
    simpa [prefixWord, tailWord_5030073, baseEnd_5030073] using wordTrace_append hprefix tailTrace_5030073
  have hstable : (prefixWord ++ tailWord_5030073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030073).length < 2 ^ (prefixWord ++ tailWord_5030073).sum := by decide
  have hdescent : baseEnd_5030073 < baseStart_5030073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030097 : List Nat := [1, 2, 2, 1, 2, 2, 4, 2, 3, 1, 3]
def baseStart_5030097 : Nat := 118140960795 + 5030097 * 2 ^ 59
def prefixEnd_5030097 : Nat := 4983230072969 + 3 ^ 40 * 5030097 * 2
def baseEnd_5030097 : Nat := 2582857499738911456054511

theorem tailTrace_5030097 : CollatzResearch.WordTrace tailWord_5030097 prefixEnd_5030097 2582857499738911456054511 := by
  unfold tailWord_5030097
  simp only [CollatzResearch.WordTrace]
  refine ⟨183462709657825116018480545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122308473105216744012320363 183462709657825116018480545)
  ·
    refine ⟨137597032243368837013860409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183462709657825116018480545 137597032243368837013860409)
    ·
      refine ⟨103197774182526627760395307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137597032243368837013860409 103197774182526627760395307)
      ·
        refine ⟨154796661273789941640592961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103197774182526627760395307 154796661273789941640592961)
        ·
          refine ⟨116097495955342456230444721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154796661273789941640592961 116097495955342456230444721)
          ·
            refine ⟨87073121966506842172833541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116097495955342456230444721 87073121966506842172833541)
            ·
              refine ⟨16326210368720032907406289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 87073121966506842172833541 16326210368720032907406289)
              ·
                refine ⟨12244657776540024680554717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16326210368720032907406289 12244657776540024680554717)
                ·
                  refine ⟨4591746666202509255208019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12244657776540024680554717 4591746666202509255208019)
                  ·
                    refine ⟨6887619999303763882812029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4591746666202509255208019 6887619999303763882812029)
                    ·
                      refine ⟨2582857499738911456054511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6887619999303763882812029 2582857499738911456054511)
                      ·
                        rfl

theorem cell23_5030097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 3, 1, 3].length) (baseStart_5030097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030097 prefixEnd_5030097 := by exact prefixLift 5030097
  have htrace : WordTrace (prefixWord ++ tailWord_5030097) baseStart_5030097 baseEnd_5030097 := by
    simpa [prefixWord, tailWord_5030097, baseEnd_5030097] using wordTrace_append hprefix tailTrace_5030097
  have hstable : (prefixWord ++ tailWord_5030097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030097).length < 2 ^ (prefixWord ++ tailWord_5030097).sum := by decide
  have hdescent : baseEnd_5030097 < baseStart_5030097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030117 : List Nat := [1, 3, 1, 4, 2, 1, 2, 3, 1, 5]
def baseStart_5030117 : Nat := 118140960795 + 5030117 * 2 ^ 59
def prefixEnd_5030117 : Nat := 4983230072969 + 3 ^ 40 * 5030117 * 2
def baseEnd_5030117 : Nat := 860955923117333792601473

theorem tailTrace_5030117 : CollatzResearch.WordTrace tailWord_5030117 prefixEnd_5030117 860955923117333792601473 := by
  unfold tailWord_5030117
  simp only [CollatzResearch.WordTrace]
  refine ⟨183463439117752659434208605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122308959411835106289472403 183463439117752659434208605)
  ·
    refine ⟨68798789669157247287828227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183463439117752659434208605 68798789669157247287828227)
    ·
      refine ⟨103198184503735870931742341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68798789669157247287828227 103198184503735870931742341)
      ·
        refine ⟨19349659594450475799701689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103198184503735870931742341 19349659594450475799701689)
        ·
          refine ⟨14512244695837856849776267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19349659594450475799701689 14512244695837856849776267)
          ·
            refine ⟨21768367043756785274664401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14512244695837856849776267 21768367043756785274664401)
            ·
              refine ⟨16326275282817588955998301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21768367043756785274664401 16326275282817588955998301)
              ·
                refine ⟨6122353231056595858499363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16326275282817588955998301 6122353231056595858499363)
                ·
                  refine ⟨9183529846584893787749045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6122353231056595858499363 9183529846584893787749045)
                  ·
                    refine ⟨860955923117333792601473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9183529846584893787749045 860955923117333792601473)
                    ·
                      rfl

theorem cell23_5030117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 5].length) (baseStart_5030117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030117 prefixEnd_5030117 := by exact prefixLift 5030117
  have htrace : WordTrace (prefixWord ++ tailWord_5030117) baseStart_5030117 baseEnd_5030117 := by
    simpa [prefixWord, tailWord_5030117, baseEnd_5030117] using wordTrace_append hprefix tailTrace_5030117
  have hstable : (prefixWord ++ tailWord_5030117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030117).length < 2 ^ (prefixWord ++ tailWord_5030117).sum := by decide
  have hdescent : baseEnd_5030117 < baseStart_5030117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030131 : List Nat := [1, 1, 1, 2, 2, 4, 5, 2, 1, 1, 3]
def baseStart_5030131 : Nat := 118140960795 + 5030131 * 2 ^ 59
def prefixEnd_5030131 : Nat := 4983230072969 + 3 ^ 40 * 5030131 * 2
def baseEnd_5030131 : Nat := 2582874958081164323029355

theorem tailTrace_5030131 : CollatzResearch.WordTrace tailWord_5030131 prefixEnd_5030131 2582874958081164323029355 := by
  unfold tailWord_5030131
  simp only [CollatzResearch.WordTrace]
  refine ⟨183463949739701939825218247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122309299826467959883478831 183463949739701939825218247)
  ·
    refine ⟨275195924609552909737827371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183463949739701939825218247 275195924609552909737827371)
    ·
      refine ⟨412793886914329364606741057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275195924609552909737827371 412793886914329364606741057)
      ·
        refine ⟨309595415185747023455055793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412793886914329364606741057 309595415185747023455055793)
        ·
          refine ⟨232196561389310267591291845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309595415185747023455055793 232196561389310267591291845)
          ·
            refine ⟨43536855260495675173367221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 232196561389310267591291845 43536855260495675173367221)
            ·
              refine ⟨4081580180671469547503177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43536855260495675173367221 4081580180671469547503177)
              ·
                refine ⟨3061185135503602160627383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4081580180671469547503177 3061185135503602160627383)
                ·
                  refine ⟨4591777703255403240941075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3061185135503602160627383 4591777703255403240941075)
                  ·
                    refine ⟨6887666554883104861411613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4591777703255403240941075 6887666554883104861411613)
                    ·
                      refine ⟨2582874958081164323029355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6887666554883104861411613 2582874958081164323029355)
                      ·
                        rfl

theorem cell23_5030131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 2, 1, 1, 3].length) (baseStart_5030131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030131 prefixEnd_5030131 := by exact prefixLift 5030131
  have htrace : WordTrace (prefixWord ++ tailWord_5030131) baseStart_5030131 baseEnd_5030131 := by
    simpa [prefixWord, tailWord_5030131, baseEnd_5030131] using wordTrace_append hprefix tailTrace_5030131
  have hstable : (prefixWord ++ tailWord_5030131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030131).length < 2 ^ (prefixWord ++ tailWord_5030131).sum := by decide
  have hdescent : baseEnd_5030131 < baseStart_5030131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030147 : List Nat := [1, 1, 1, 3, 2, 3, 3, 3, 2, 4]
def baseStart_5030147 : Nat := 118140960795 + 5030147 * 2 ^ 59
def prefixEnd_5030147 : Nat := 4983230072969 + 3 ^ 40 * 5030147 * 2
def baseEnd_5030147 : Nat := 860961057923878753476427

theorem tailTrace_5030147 : CollatzResearch.WordTrace tailWord_5030147 prefixEnd_5030147 860961057923878753476427 := by
  unfold tailWord_5030147
  simp only [CollatzResearch.WordTrace]
  refine ⟨183464533307643974557800695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122309688871762649705200463 183464533307643974557800695)
  ·
    refine ⟨275196799961465961836701043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183464533307643974557800695 275196799961465961836701043)
    ·
      refine ⟨412795199942198942755051565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275196799961465961836701043 412795199942198942755051565)
      ·
        refine ⟨154798199978324603533144337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 412795199942198942755051565 154798199978324603533144337)
        ·
          refine ⟨116098649983743452649858253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154798199978324603533144337 116098649983743452649858253)
          ·
            refine ⟨43536993743903794743696845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116098649983743452649858253 43536993743903794743696845)
            ·
              refine ⟨16326372653963923028886317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43536993743903794743696845 16326372653963923028886317)
              ·
                refine ⟨6122389745236471135832369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16326372653963923028886317 6122389745236471135832369)
                ·
                  refine ⟨4591792308927353351874277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6122389745236471135832369 4591792308927353351874277)
                  ·
                    refine ⟨860961057923878753476427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4591792308927353351874277 860961057923878753476427)
                    ·
                      rfl

theorem cell23_5030147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 2, 4].length) (baseStart_5030147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030147 prefixEnd_5030147 := by exact prefixLift 5030147
  have htrace : WordTrace (prefixWord ++ tailWord_5030147) baseStart_5030147 baseEnd_5030147 := by
    simpa [prefixWord, tailWord_5030147, baseEnd_5030147] using wordTrace_append hprefix tailTrace_5030147
  have hstable : (prefixWord ++ tailWord_5030147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030147).length < 2 ^ (prefixWord ++ tailWord_5030147).sum := by decide
  have hdescent : baseEnd_5030147 < baseStart_5030147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030151 : List Nat := [1, 1, 4, 5, 1, 2, 1, 2, 1, 5]
def baseStart_5030151 : Nat := 118140960795 + 5030151 * 2 ^ 59
def prefixEnd_5030151 : Nat := 4983230072969 + 3 ^ 40 * 5030151 * 2
def baseEnd_5030151 : Nat := 860961742564751414926421

theorem tailTrace_5030151 : CollatzResearch.WordTrace tailWord_5030151 prefixEnd_5030151 860961742564751414926421 := by
  unfold tailWord_5030151
  simp only [CollatzResearch.WordTrace]
  refine ⟨183464679199629483240946307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122309786133086322160630871 183464679199629483240946307)
  ·
    refine ⟨275197018799444224861419461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183464679199629483240946307 275197018799444224861419461)
    ·
      refine ⟨51599441024895792161516149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 275197018799444224861419461 51599441024895792161516149)
      ·
        refine ⟨4837447596083980515142139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51599441024895792161516149 4837447596083980515142139)
        ·
          refine ⟨7256171394125970772713209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4837447596083980515142139 7256171394125970772713209)
          ·
            refine ⟨5442128545594478079534907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7256171394125970772713209 5442128545594478079534907)
            ·
              refine ⟨8163192818391717119302361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5442128545594478079534907 8163192818391717119302361)
              ·
                refine ⟨6122394613793787839476771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8163192818391717119302361 6122394613793787839476771)
                ·
                  refine ⟨9183591920690681759215157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6122394613793787839476771 9183591920690681759215157)
                  ·
                    refine ⟨860961742564751414926421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9183591920690681759215157 860961742564751414926421)
                    ·
                      rfl

theorem cell23_5030151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_5030151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030151 prefixEnd_5030151 := by exact prefixLift 5030151
  have htrace : WordTrace (prefixWord ++ tailWord_5030151) baseStart_5030151 baseEnd_5030151 := by
    simpa [prefixWord, tailWord_5030151, baseEnd_5030151] using wordTrace_append hprefix tailTrace_5030151
  have hstable : (prefixWord ++ tailWord_5030151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030151).length < 2 ^ (prefixWord ++ tailWord_5030151).sum := by decide
  have hdescent : baseEnd_5030151 < baseStart_5030151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030154 : List Nat := [3, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2]
def baseStart_5030154 : Nat := 118140960795 + 5030154 * 2 ^ 59
def prefixEnd_5030154 : Nat := 4983230072969 + 3 ^ 40 * 5030154 * 2
def baseEnd_5030154 : Nat := 2582886768136217733041749

theorem tailTrace_5030154 : CollatzResearch.WordTrace tailWord_5030154 prefixEnd_5030154 2582886768136217733041749 := by
  unfold tailWord_5030154
  simp only [CollatzResearch.WordTrace]
  refine ⟨45866197154654653688326379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122309859079079076502203677 45866197154654653688326379)
  ·
    refine ⟨68799295731981980532489569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45866197154654653688326379 68799295731981980532489569)
    ·
      refine ⟨51599471798986485399367177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68799295731981980532489569 51599471798986485399367177)
      ·
        refine ⟨38699603849239864049525383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51599471798986485399367177 38699603849239864049525383)
        ·
          refine ⟨58049405773859796074288075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38699603849239864049525383 58049405773859796074288075)
          ·
            refine ⟨87074108660789694111432113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58049405773859796074288075 87074108660789694111432113)
            ·
              refine ⟨65305581495592270583574085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87074108660789694111432113 65305581495592270583574085)
              ·
                refine ⟨12244796530423550734420141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65305581495592270583574085 12244796530423550734420141)
                ·
                  refine ⟨4591798698908831525407553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12244796530423550734420141 4591798698908831525407553)
                  ·
                    refine ⟨3443849024181623644055665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4591798698908831525407553 3443849024181623644055665)
                    ·
                      refine ⟨2582886768136217733041749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3443849024181623644055665 2582886768136217733041749)
                      ·
                        rfl

theorem cell23_5030154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_5030154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030154 prefixEnd_5030154 := by exact prefixLift 5030154
  have htrace : WordTrace (prefixWord ++ tailWord_5030154) baseStart_5030154 baseEnd_5030154 := by
    simpa [prefixWord, tailWord_5030154, baseEnd_5030154] using wordTrace_append hprefix tailTrace_5030154
  have hstable : (prefixWord ++ tailWord_5030154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030154).length < 2 ^ (prefixWord ++ tailWord_5030154).sum := by decide
  have hdescent : baseEnd_5030154 < baseStart_5030154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030167 : List Nat := [1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 4]
def baseStart_5030167 : Nat := 118140960795 + 5030167 * 2 ^ 59
def prefixEnd_5030167 : Nat := 4983230072969 + 3 ^ 40 * 5030167 * 2
def baseEnd_5030167 : Nat := 2582893443384726182179189

theorem tailTrace_5030167 : CollatzResearch.WordTrace tailWord_5030167 prefixEnd_5030167 2582893443384726182179189 := by
  unfold tailWord_5030167
  simp only [CollatzResearch.WordTrace]
  refine ⟨183465262767571517973528755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122310175178381011982352503 183465262767571517973528755)
  ·
    refine ⟨275197894151357276960293133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183465262767571517973528755 275197894151357276960293133)
    ·
      refine ⟨103199210306758978860109925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275197894151357276960293133 103199210306758978860109925)
      ·
        refine ⟨19349851932517308536270611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103199210306758978860109925 19349851932517308536270611)
        ·
          refine ⟨29024777898775962804405917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19349851932517308536270611 29024777898775962804405917)
          ·
            refine ⟨10884291712040986051652219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29024777898775962804405917 10884291712040986051652219)
            ·
              refine ⟨16326437568061479077478329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10884291712040986051652219 16326437568061479077478329)
              ·
                refine ⟨12244828176046109308108747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16326437568061479077478329 12244828176046109308108747)
                ·
                  refine ⟨18367242264069163962163121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12244828176046109308108747 18367242264069163962163121)
                  ·
                    refine ⟨13775431698051872971622341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18367242264069163962163121 13775431698051872971622341)
                    ·
                      refine ⟨2582893443384726182179189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13775431698051872971622341 2582893443384726182179189)
                      ·
                        rfl

theorem cell23_5030167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_5030167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030167 prefixEnd_5030167 := by exact prefixLift 5030167
  have htrace : WordTrace (prefixWord ++ tailWord_5030167) baseStart_5030167 baseEnd_5030167 := by
    simpa [prefixWord, tailWord_5030167, baseEnd_5030167] using wordTrace_append hprefix tailTrace_5030167
  have hstable : (prefixWord ++ tailWord_5030167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030167).length < 2 ^ (prefixWord ++ tailWord_5030167).sum := by decide
  have hdescent : baseEnd_5030167 < baseStart_5030167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030188 : List Nat := [2, 2, 1, 1, 1, 3, 6, 2, 1, 2, 2]
def baseStart_5030188 : Nat := 118140960795 + 5030188 * 2 ^ 59
def prefixEnd_5030188 : Nat := 4983230072969 + 3 ^ 40 * 5030188 * 2
def baseEnd_5030188 : Nat := 2582904226478470600016593

theorem tailTrace_5030188 : CollatzResearch.WordTrace tailWord_5030188 prefixEnd_5030188 2582904226478470600016593 := by
  unfold tailWord_5030188
  simp only [CollatzResearch.WordTrace]
  refine ⟨91733014350247719280021609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122310685800330292373362145 91733014350247719280021609)
  ·
    refine ⟨68799760762685789460016207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91733014350247719280021609 68799760762685789460016207)
    ·
      refine ⟨103199641144028684190024311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68799760762685789460016207 103199641144028684190024311)
      ·
        refine ⟨154799461716043026285036467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103199641144028684190024311 154799461716043026285036467)
        ·
          refine ⟨232199192574064539427554701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154799461716043026285036467 232199192574064539427554701)
          ·
            refine ⟨87074697215274202285333013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232199192574064539427554701 87074697215274202285333013)
            ·
              refine ⟨4081626431965978232124985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 87074697215274202285333013 4081626431965978232124985)
              ·
                refine ⟨3061219823974483674093739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4081626431965978232124985 3061219823974483674093739)
                ·
                  refine ⟨4591829735961725511140609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3061219823974483674093739 4591829735961725511140609)
                  ·
                    refine ⟨3443872301971294133355457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4591829735961725511140609 3443872301971294133355457)
                    ·
                      refine ⟨2582904226478470600016593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3443872301971294133355457 2582904226478470600016593)
                      ·
                        rfl

theorem cell23_5030188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2, 1, 2, 2].length) (baseStart_5030188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030188 prefixEnd_5030188 := by exact prefixLift 5030188
  have htrace : WordTrace (prefixWord ++ tailWord_5030188) baseStart_5030188 baseEnd_5030188 := by
    simpa [prefixWord, tailWord_5030188, baseEnd_5030188] using wordTrace_append hprefix tailTrace_5030188
  have hstable : (prefixWord ++ tailWord_5030188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030188).length < 2 ^ (prefixWord ++ tailWord_5030188).sum := by decide
  have hdescent : baseEnd_5030188 < baseStart_5030188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030194 : List Nat := [3, 2, 1, 1, 6, 1, 1, 8]
def baseStart_5030194 : Nat := 118140960795 + 5030194 * 2 ^ 59
def prefixEnd_5030194 : Nat := 4983230072969 + 3 ^ 40 * 5030194 * 2
def baseEnd_5030194 : Nat := 95663233606014725057095

theorem tailTrace_5030194 : CollatzResearch.WordTrace tailWord_5030194 prefixEnd_5030194 95663233606014725057095 := by
  unfold tailWord_5030194
  simp only [CollatzResearch.WordTrace]
  refine ⟨45866561884618425396190409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122310831692315801056507757 45866561884618425396190409)
  ·
    refine ⟨34399921413463819047142807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45866561884618425396190409 34399921413463819047142807)
    ·
      refine ⟨51599882120195728570714211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34399921413463819047142807 51599882120195728570714211)
      ·
        refine ⟨77399823180293592856071317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51599882120195728570714211 77399823180293592856071317)
        ·
          refine ⟨3628116711576262165128343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 77399823180293592856071317 3628116711576262165128343)
          ·
            refine ⟨5442175067364393247692515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3628116711576262165128343 5442175067364393247692515)
            ·
              refine ⟨8163262601046589871538773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5442175067364393247692515 8163262601046589871538773)
              ·
                refine ⟨95663233606014725057095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8163262601046589871538773 95663233606014725057095)
                ·
                  rfl

theorem cell23_5030194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 8].length) (baseStart_5030194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030194 prefixEnd_5030194 := by exact prefixLift 5030194
  have htrace : WordTrace (prefixWord ++ tailWord_5030194) baseStart_5030194 baseEnd_5030194 := by
    simpa [prefixWord, tailWord_5030194, baseEnd_5030194] using wordTrace_append hprefix tailTrace_5030194
  have hstable : (prefixWord ++ tailWord_5030194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030194).length < 2 ^ (prefixWord ++ tailWord_5030194).sum := by decide
  have hdescent : baseEnd_5030194 < baseStart_5030194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030204 : List Nat := [2, 2, 2, 2, 1, 2, 1, 5, 2, 1, 3]
def baseStart_5030204 : Nat := 118140960795 + 5030204 * 2 ^ 59
def prefixEnd_5030204 : Nat := 4983230072969 + 3 ^ 40 * 5030204 * 2
def baseEnd_5030204 : Nat := 2582912442168942537416519

theorem tailTrace_5030204 : CollatzResearch.WordTrace tailWord_5030204 prefixEnd_5030204 2582912442168942537416519 := by
  unfold tailWord_5030204
  simp only [CollatzResearch.WordTrace]
  refine ⟨91733306134218736646312833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122311074845624982195083777 91733306134218736646312833)
  ·
    refine ⟨68799979600664052484734625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91733306134218736646312833 68799979600664052484734625)
    ·
      refine ⟨51599984700498039363550969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68799979600664052484734625 51599984700498039363550969)
      ·
        refine ⟨38699988525373529522663227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51599984700498039363550969 38699988525373529522663227)
        ·
          refine ⟨58049982788060294283994841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38699988525373529522663227 58049982788060294283994841)
          ·
            refine ⟨43537487091045220712996131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58049982788060294283994841 43537487091045220712996131)
            ·
              refine ⟨65306230636567831069494197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43537487091045220712996131 65306230636567831069494197)
              ·
                refine ⟨6122459122178234162765081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65306230636567831069494197 6122459122178234162765081)
                ·
                  refine ⟨4591844341633675622073811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6122459122178234162765081 4591844341633675622073811)
                  ·
                    refine ⟨6887766512450513433110717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4591844341633675622073811 6887766512450513433110717)
                    ·
                      refine ⟨2582912442168942537416519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6887766512450513433110717 2582912442168942537416519)
                      ·
                        rfl

theorem cell23_5030204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_5030204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030204 prefixEnd_5030204 := by exact prefixLift 5030204
  have htrace : WordTrace (prefixWord ++ tailWord_5030204) baseStart_5030204 baseEnd_5030204 := by
    simpa [prefixWord, tailWord_5030204, baseEnd_5030204] using wordTrace_append hprefix tailTrace_5030204
  have hstable : (prefixWord ++ tailWord_5030204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030204).length < 2 ^ (prefixWord ++ tailWord_5030204).sum := by decide
  have hdescent : baseEnd_5030204 < baseStart_5030204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030220 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 1, 8]
def baseStart_5030220 : Nat := 118140960795 + 5030220 * 2 ^ 59
def prefixEnd_5030220 : Nat := 4983230072969 + 3 ^ 40 * 5030220 * 2
def baseEnd_5030220 : Nat := 860973552619804824938815

theorem tailTrace_5030220 : CollatzResearch.WordTrace tailWord_5030220 prefixEnd_5030220 860973552619804824938815 := by
  unfold tailWord_5030220
  simp only [CollatzResearch.WordTrace]
  refine ⟨91733597918189754012604057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122311463890919672016805409 91733597918189754012604057)
  ·
    refine ⟨68800198438642315509453043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91733597918189754012604057 68800198438642315509453043)
    ·
      refine ⟨103200297657963473264179565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68800198438642315509453043 103200297657963473264179565)
      ·
        refine ⟨38700111621736302474067337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103200297657963473264179565 38700111621736302474067337)
        ·
          refine ⟨29025083716302226855550503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38700111621736302474067337 29025083716302226855550503)
          ·
            refine ⟨43537625574453340283325755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29025083716302226855550503 43537625574453340283325755)
            ·
              refine ⟨65306438361680010424988633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43537625574453340283325755 65306438361680010424988633)
              ·
                refine ⟨48979828771260007818741475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65306438361680010424988633 48979828771260007818741475)
                ·
                  refine ⟨73469743156890011728112213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48979828771260007818741475 73469743156890011728112213)
                  ·
                    refine ⟨860973552619804824938815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73469743156890011728112213 860973552619804824938815)
                    ·
                      rfl

theorem cell23_5030220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 1, 8].length) (baseStart_5030220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030220 prefixEnd_5030220 := by exact prefixLift 5030220
  have htrace : WordTrace (prefixWord ++ tailWord_5030220) baseStart_5030220 baseEnd_5030220 := by
    simpa [prefixWord, tailWord_5030220, baseEnd_5030220] using wordTrace_append hprefix tailTrace_5030220
  have hstable : (prefixWord ++ tailWord_5030220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030220).length < 2 ^ (prefixWord ++ tailWord_5030220).sum := by decide
  have hdescent : baseEnd_5030220 < baseStart_5030220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030227 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 3, 4, 2]
def baseStart_5030227 : Nat := 118140960795 + 5030227 * 2 ^ 59
def prefixEnd_5030227 : Nat := 4983230072969 + 3 ^ 40 * 5030227 * 2
def baseEnd_5030227 : Nat := 2582924252223995947428913

theorem tailTrace_5030227 : CollatzResearch.WordTrace tailWord_5030227 prefixEnd_5030227 2582924252223995947428913 := by
  unfold tailWord_5030227
  simp only [CollatzResearch.WordTrace]
  refine ⟨183467451147354148220712935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122311634098236098813808623 183467451147354148220712935)
  ·
    refine ⟨275201176721031222331069403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183467451147354148220712935 275201176721031222331069403)
    ·
      refine ⟨412801765081546833496604105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275201176721031222331069403 412801765081546833496604105)
      ·
        refine ⟨309601323811160125122453079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412801765081546833496604105 309601323811160125122453079)
        ·
          refine ⟨464401985716740187683679619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309601323811160125122453079 464401985716740187683679619)
          ·
            refine ⟨696602978575110281525519429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464401985716740187683679619 696602978575110281525519429)
            ·
              refine ⟨130613058482833177786034893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 696602978575110281525519429 130613058482833177786034893)
              ·
                refine ⟨48979896931062441669763085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130613058482833177786034893 48979896931062441669763085)
                ·
                  refine ⟨18367461349148415626161157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48979896931062441669763085 18367461349148415626161157)
                  ·
                    refine ⟨3443899002965327929905217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18367461349148415626161157 3443899002965327929905217)
                    ·
                      refine ⟨2582924252223995947428913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3443899002965327929905217 2582924252223995947428913)
                      ·
                        rfl

theorem cell23_5030227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 4, 2].length) (baseStart_5030227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030227 prefixEnd_5030227 := by exact prefixLift 5030227
  have htrace : WordTrace (prefixWord ++ tailWord_5030227) baseStart_5030227 baseEnd_5030227 := by
    simpa [prefixWord, tailWord_5030227, baseEnd_5030227] using wordTrace_append hprefix tailTrace_5030227
  have hstable : (prefixWord ++ tailWord_5030227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030227).length < 2 ^ (prefixWord ++ tailWord_5030227).sum := by decide
  have hdescent : baseEnd_5030227 < baseStart_5030227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030261 : List Nat := [1, 3, 4, 1, 2, 1, 3, 1, 1, 4, 2]
def baseStart_5030261 : Nat := 118140960795 + 5030261 * 2 ^ 59
def prefixEnd_5030261 : Nat := 4983230072969 + 3 ^ 40 * 5030261 * 2
def baseEnd_5030261 : Nat := 2582941710566248814403757

theorem tailTrace_5030261 : CollatzResearch.WordTrace tailWord_5030261 prefixEnd_5030261 2582941710566248814403757 := by
  unfold tailWord_5030261
  simp only [CollatzResearch.WordTrace]
  refine ⟨183468691229230972027450637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122312460819487314684967091 183468691229230972027450637)
  ·
    refine ⟨68800759210961614510293989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183468691229230972027450637 68800759210961614510293989)
    ·
      refine ⟨12900142352055302720680123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68800759210961614510293989 12900142352055302720680123)
      ·
        refine ⟨19350213528082954081020185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12900142352055302720680123 19350213528082954081020185)
        ·
          refine ⟨14512660146062215560765139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19350213528082954081020185 14512660146062215560765139)
          ·
            refine ⟨21768990219093323341147709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14512660146062215560765139 21768990219093323341147709)
            ·
              refine ⟨8163371332159996252930391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21768990219093323341147709 8163371332159996252930391)
              ·
                refine ⟨12245056998239994379395587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8163371332159996252930391 12245056998239994379395587)
                ·
                  refine ⟨18367585497359991569093381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12245056998239994379395587 18367585497359991569093381)
                  ·
                    refine ⟨3443922280754998419205009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18367585497359991569093381 3443922280754998419205009)
                    ·
                      refine ⟨2582941710566248814403757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3443922280754998419205009 2582941710566248814403757)
                      ·
                        rfl

theorem cell23_5030261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_5030261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030261 prefixEnd_5030261 := by exact prefixLift 5030261
  have htrace : WordTrace (prefixWord ++ tailWord_5030261) baseStart_5030261 baseEnd_5030261 := by
    simpa [prefixWord, tailWord_5030261, baseEnd_5030261] using wordTrace_append hprefix tailTrace_5030261
  have hstable : (prefixWord ++ tailWord_5030261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030261).length < 2 ^ (prefixWord ++ tailWord_5030261).sum := by decide
  have hdescent : baseEnd_5030261 < baseStart_5030261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030284 : List Nat := [2, 2, 1, 2, 1, 4, 3, 3, 5]
def baseStart_5030284 : Nat := 118140960795 + 5030284 * 2 ^ 59
def prefixEnd_5030284 : Nat := 4983230072969 + 3 ^ 40 * 5030284 * 2
def baseEnd_5030284 : Nat := 286994835624589136046239

theorem tailTrace_5030284 : CollatzResearch.WordTrace tailWord_5030284 prefixEnd_5030284 286994835624589136046239 := by
  unfold tailWord_5030284
  simp only [CollatzResearch.WordTrace]
  refine ⟨91734765054073823477768953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122313020072098431303691937 91734765054073823477768953)
  ·
    refine ⟨68801073790555367608326715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91734765054073823477768953 68801073790555367608326715)
    ·
      refine ⟨103201610685833051412490073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68801073790555367608326715 103201610685833051412490073)
      ·
        refine ⟨77401208014374788559367555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103201610685833051412490073 77401208014374788559367555)
        ·
          refine ⟨116101812021562182839051333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77401208014374788559367555 116101812021562182839051333)
          ·
            refine ⟨21769089754042909282322125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116101812021562182839051333 21769089754042909282322125)
            ·
              refine ⟨8163408657766090980870797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21769089754042909282322125 8163408657766090980870797)
              ·
                refine ⟨3061278246662284117826549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8163408657766090980870797 3061278246662284117826549)
                ·
                  refine ⟨286994835624589136046239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3061278246662284117826549 286994835624589136046239)
                  ·
                    rfl

theorem cell23_5030284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 3, 5].length) (baseStart_5030284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030284 prefixEnd_5030284 := by exact prefixLift 5030284
  have htrace : WordTrace (prefixWord ++ tailWord_5030284) baseStart_5030284 baseEnd_5030284 := by
    simpa [prefixWord, tailWord_5030284, baseEnd_5030284] using wordTrace_append hprefix tailTrace_5030284
  have hstable : (prefixWord ++ tailWord_5030284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030284).length < 2 ^ (prefixWord ++ tailWord_5030284).sum := by decide
  have hdescent : baseEnd_5030284 < baseStart_5030284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030297 : List Nat := [1, 2, 1, 2, 1, 4, 3, 2, 2, 5]
def baseStart_5030297 : Nat := 118140960795 + 5030297 * 2 ^ 59
def prefixEnd_5030297 : Nat := 4983230072969 + 3 ^ 40 * 5030297 * 2
def baseEnd_5030297 : Nat := 860986731956603557851197

theorem tailTrace_5030297 : CollatzResearch.WordTrace tailWord_5030297 prefixEnd_5030297 860986731956603557851197 := by
  unfold tailWord_5030297
  simp only [CollatzResearch.WordTrace]
  refine ⟨183470004257100550175761145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122313336171400366783840763 183470004257100550175761145)
  ·
    refine ⟨137602503192825412631820859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183470004257100550175761145 137602503192825412631820859)
    ·
      refine ⟨206403754789238118947731289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137602503192825412631820859 206403754789238118947731289)
      ·
        refine ⟨154802816091928589210798467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206403754789238118947731289 154802816091928589210798467)
        ·
          refine ⟨232204224137892883816197701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154802816091928589210798467 232204224137892883816197701)
          ·
            refine ⟨43538292025854915715537069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 232204224137892883816197701 43538292025854915715537069)
            ·
              refine ⟨16326859509695593393326401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43538292025854915715537069 16326859509695593393326401)
              ·
                refine ⟨12245144632271695044994801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16326859509695593393326401 12245144632271695044994801)
                ·
                  refine ⟨9183858474203771283746101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12245144632271695044994801 9183858474203771283746101)
                  ·
                    refine ⟨860986731956603557851197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9183858474203771283746101 860986731956603557851197)
                    ·
                      rfl

theorem cell23_5030297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 5].length) (baseStart_5030297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030297 prefixEnd_5030297 := by exact prefixLift 5030297
  have htrace : WordTrace (prefixWord ++ tailWord_5030297) baseStart_5030297 baseEnd_5030297 := by
    simpa [prefixWord, tailWord_5030297, baseEnd_5030297] using wordTrace_append hprefix tailTrace_5030297
  have hstable : (prefixWord ++ tailWord_5030297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030297).length < 2 ^ (prefixWord ++ tailWord_5030297).sum := by decide
  have hdescent : baseEnd_5030297 < baseStart_5030297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030301 : List Nat := [1, 4, 2, 1, 5, 1, 1, 1, 7]
def baseStart_5030301 : Nat := 118140960795 + 5030301 * 2 ^ 59
def prefixEnd_5030301 : Nat := 4983230072969 + 3 ^ 40 * 5030301 * 2
def baseEnd_5030301 : Nat := 286995805532492073100397

theorem tailTrace_5030301 : CollatzResearch.WordTrace tailWord_5030301 prefixEnd_5030301 286995805532492073100397 := by
  unfold tailWord_5030301
  simp only [CollatzResearch.WordTrace]
  refine ⟨183470150149086058858906757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122313433432724039239271171 183470150149086058858906757)
  ·
    refine ⟨34400653152953636036045017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183470150149086058858906757 34400653152953636036045017)
    ·
      refine ⟨25800489864715227027033763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34400653152953636036045017 25800489864715227027033763)
      ·
        refine ⟨38700734797072840540550645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25800489864715227027033763 38700734797072840540550645)
        ·
          refine ⟨3628193887225578800676623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38700734797072840540550645 3628193887225578800676623)
          ·
            refine ⟨5442290830838368201014935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3628193887225578800676623 5442290830838368201014935)
            ·
              refine ⟨8163436246257552301522403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5442290830838368201014935 8163436246257552301522403)
              ·
                refine ⟨12245154369386328452283605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8163436246257552301522403 12245154369386328452283605)
                ·
                  refine ⟨286995805532492073100397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12245154369386328452283605 286995805532492073100397)
                  ·
                    rfl

theorem cell23_5030301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 1, 7].length) (baseStart_5030301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030301 prefixEnd_5030301 := by exact prefixLift 5030301
  have htrace : WordTrace (prefixWord ++ tailWord_5030301) baseStart_5030301 baseEnd_5030301 := by
    simpa [prefixWord, tailWord_5030301, baseEnd_5030301] using wordTrace_append hprefix tailTrace_5030301
  have hstable : (prefixWord ++ tailWord_5030301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030301).length < 2 ^ (prefixWord ++ tailWord_5030301).sum := by decide
  have hdescent : baseEnd_5030301 < baseStart_5030301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030307 : List Nat := [1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 5]
def baseStart_5030307 : Nat := 118140960795 + 5030307 * 2 ^ 59
def prefixEnd_5030307 : Nat := 4983230072969 + 3 ^ 40 * 5030307 * 2
def baseEnd_5030307 : Nat := 2582965330676355634428545

theorem tailTrace_5030307 : CollatzResearch.WordTrace tailWord_5030307 prefixEnd_5030307 2582965330676355634428545 := by
  unfold tailWord_5030307
  simp only [CollatzResearch.WordTrace]
  refine ⟨183470368987064321883625175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122313579324709547922416783 183470368987064321883625175)
  ·
    refine ⟨275205553480596482825437763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183470368987064321883625175 275205553480596482825437763)
    ·
      refine ⟨412808330220894724238156645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275205553480596482825437763 412808330220894724238156645)
      ·
        refine ⟨77401561916417760794654371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 412808330220894724238156645 77401561916417760794654371)
        ·
          refine ⟨116102342874626641191981557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77401561916417760794654371 116102342874626641191981557)
          ·
            refine ⟨10884594644496247611748271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 116102342874626641191981557 10884594644496247611748271)
            ·
              refine ⟨16326891966744371417622407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10884594644496247611748271 16326891966744371417622407)
              ·
                refine ⟨24490337950116557126433611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16326891966744371417622407 24490337950116557126433611)
                ·
                  refine ⟨36735506925174835689650417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24490337950116557126433611 36735506925174835689650417)
                  ·
                    refine ⟨27551630193881126767237813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36735506925174835689650417 27551630193881126767237813)
                    ·
                      refine ⟨2582965330676355634428545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27551630193881126767237813 2582965330676355634428545)
                      ·
                        rfl

theorem cell23_5030307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_5030307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030307 prefixEnd_5030307 := by exact prefixLift 5030307
  have htrace : WordTrace (prefixWord ++ tailWord_5030307) baseStart_5030307 baseEnd_5030307 := by
    simpa [prefixWord, tailWord_5030307, baseEnd_5030307] using wordTrace_append hprefix tailTrace_5030307
  have hstable : (prefixWord ++ tailWord_5030307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030307).length < 2 ^ (prefixWord ++ tailWord_5030307).sum := by decide
  have hdescent : baseEnd_5030307 < baseStart_5030307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030312 : List Nat := [2, 1, 6, 1, 1, 3, 2, 1, 2, 2, 2]
def baseStart_5030312 : Nat := 118140960795 + 5030312 * 2 ^ 59
def prefixEnd_5030312 : Nat := 4983230072969 + 3 ^ 40 * 5030312 * 2
def baseEnd_5030312 : Nat := 2582967898079628114866023

theorem tailTrace_5030312 : CollatzResearch.WordTrace tailWord_5030312 prefixEnd_5030312 2582967898079628114866023 := by
  unfold tailWord_5030312
  simp only [CollatzResearch.WordTrace]
  refine ⟨91735275676023103868778595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122313700901364138491704793 91735275676023103868778595)
  ·
    refine ⟨137602913514034655803167893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91735275676023103868778595 137602913514034655803167893)
    ·
      refine ⟨6450136570970374490773495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 137602913514034655803167893 6450136570970374490773495)
      ·
        refine ⟨9675204856455561736160243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6450136570970374490773495 9675204856455561736160243)
        ·
          refine ⟨14512807284683342604240365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9675204856455561736160243 14512807284683342604240365)
          ·
            refine ⟨5442302731756253476590137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14512807284683342604240365 5442302731756253476590137)
            ·
              refine ⟨4081727048817190107442603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5442302731756253476590137 4081727048817190107442603)
              ·
                refine ⟨6122590573225785161163905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4081727048817190107442603 6122590573225785161163905)
                ·
                  refine ⟨4591942929919338870872929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6122590573225785161163905 4591942929919338870872929)
                  ·
                    refine ⟨3443957197439504153154697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4591942929919338870872929 3443957197439504153154697)
                    ·
                      refine ⟨2582967898079628114866023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3443957197439504153154697 2582967898079628114866023)
                      ·
                        rfl

theorem cell23_5030312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_5030312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030312 prefixEnd_5030312 := by exact prefixLift 5030312
  have htrace : WordTrace (prefixWord ++ tailWord_5030312) baseStart_5030312 baseEnd_5030312 := by
    simpa [prefixWord, tailWord_5030312, baseEnd_5030312] using wordTrace_append hprefix tailTrace_5030312
  have hstable : (prefixWord ++ tailWord_5030312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030312).length < 2 ^ (prefixWord ++ tailWord_5030312).sum := by decide
  have hdescent : baseEnd_5030312 < baseStart_5030312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030320 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 9]
def baseStart_5030320 : Nat := 118140960795 + 5030320 * 2 ^ 59
def prefixEnd_5030320 : Nat := 4983230072969 + 3 ^ 40 * 5030320 * 2
def baseEnd_5030320 : Nat := 2582972005924864083565985

theorem tailTrace_5030320 : CollatzResearch.WordTrace tailWord_5030320 prefixEnd_5030320 2582972005924864083565985 := by
  unfold tailWord_5030320
  simp only [CollatzResearch.WordTrace]
  refine ⟨91735421568008612551924207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122313895424011483402565609 91735421568008612551924207)
  ·
    refine ⟨137603132352012918827886311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91735421568008612551924207 137603132352012918827886311)
    ·
      refine ⟨206404698528019378241829467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137603132352012918827886311 206404698528019378241829467)
      ·
        refine ⟨309607047792029067362744201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206404698528019378241829467 309607047792029067362744201)
        ·
          refine ⟨232205285844021800522058151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309607047792029067362744201 232205285844021800522058151)
          ·
            refine ⟨348307928766032700783087227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232205285844021800522058151 348307928766032700783087227)
            ·
              refine ⟨522461893149049051174630841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348307928766032700783087227 522461893149049051174630841)
              ·
                refine ⟨391846419861786788380973131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 522461893149049051174630841 391846419861786788380973131)
                ·
                  refine ⟨587769629792680182571459697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 391846419861786788380973131 587769629792680182571459697)
                  ·
                    refine ⟨440827222344510136928594773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 587769629792680182571459697 440827222344510136928594773)
                    ·
                      refine ⟨2582972005924864083565985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 440827222344510136928594773 2582972005924864083565985)
                      ·
                        rfl

theorem cell23_5030320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 9].length) (baseStart_5030320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030320 prefixEnd_5030320 := by exact prefixLift 5030320
  have htrace : WordTrace (prefixWord ++ tailWord_5030320) baseStart_5030320 baseEnd_5030320 := by
    simpa [prefixWord, tailWord_5030320, baseEnd_5030320] using wordTrace_append hprefix tailTrace_5030320
  have hstable : (prefixWord ++ tailWord_5030320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030320).length < 2 ^ (prefixWord ++ tailWord_5030320).sum := by decide
  have hdescent : baseEnd_5030320 < baseStart_5030320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030334 : List Nat := [4, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4]
def baseStart_5030334 : Nat := 118140960795 + 5030334 * 2 ^ 59
def prefixEnd_5030334 : Nat := 4983230072969 + 3 ^ 40 * 5030334 * 2
def baseEnd_5030334 : Nat := 2582979194654027028790921

theorem tailTrace_5030334 : CollatzResearch.WordTrace tailWord_5030334 prefixEnd_5030334 2582979194654027028790921 := by
  unfold tailWord_5030334
  simp only [CollatzResearch.WordTrace]
  refine ⟨22933919219745813186857257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122314235838644336996572037 22933919219745813186857257)
  ·
    refine ⟨17200439414809359890142943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22933919219745813186857257 17200439414809359890142943)
    ·
      refine ⟨25800659122214039835214415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17200439414809359890142943 25800659122214039835214415)
      ·
        refine ⟨38700988683321059752821623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25800659122214039835214415 38700988683321059752821623)
        ·
          refine ⟨58051483024981589629232435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38700988683321059752821623 58051483024981589629232435)
          ·
            refine ⟨87077224537472384443848653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58051483024981589629232435 87077224537472384443848653)
            ·
              refine ⟨32653959201552144166443245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 87077224537472384443848653 32653959201552144166443245)
              ·
                refine ⟨12245234700582054062416217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32653959201552144166443245 12245234700582054062416217)
                ·
                  refine ⟨9183926025436540546812163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12245234700582054062416217 9183926025436540546812163)
                  ·
                    refine ⟨13775889038154810820218245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9183926025436540546812163 13775889038154810820218245)
                    ·
                      refine ⟨2582979194654027028790921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13775889038154810820218245 2582979194654027028790921)
                      ·
                        rfl

theorem cell23_5030334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_5030334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030334 prefixEnd_5030334 := by exact prefixLift 5030334
  have htrace : WordTrace (prefixWord ++ tailWord_5030334) baseStart_5030334 baseEnd_5030334 := by
    simpa [prefixWord, tailWord_5030334, baseEnd_5030334] using wordTrace_append hprefix tailTrace_5030334
  have hstable : (prefixWord ++ tailWord_5030334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030334).length < 2 ^ (prefixWord ++ tailWord_5030334).sum := by decide
  have hdescent : baseEnd_5030334 < baseStart_5030334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030361 : List Nat := [1, 2, 1, 2, 4, 1, 3, 4, 1, 4]
def baseStart_5030361 : Nat := 118140960795 + 5030361 * 2 ^ 59
def prefixEnd_5030361 : Nat := 4983230072969 + 3 ^ 40 * 5030361 * 2
def baseEnd_5030361 : Nat := 860997686210566141051099

theorem tailTrace_5030361 : CollatzResearch.WordTrace tailWord_5030361 prefixEnd_5030361 860997686210566141051099 := by
  unfold tailWord_5030361
  simp only [CollatzResearch.WordTrace]
  refine ⟨183472338528868689106090937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122314892352579126070727291 183472338528868689106090937)
  ·
    refine ⟨137604253896651516829568203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183472338528868689106090937 137604253896651516829568203)
    ·
      refine ⟨206406380844977275244352305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137604253896651516829568203 206406380844977275244352305)
      ·
        refine ⟨154804785633732956433264229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206406380844977275244352305 154804785633732956433264229)
        ·
          refine ⟨29025897306324929331237043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154804785633732956433264229 29025897306324929331237043)
          ·
            refine ⟨43538845959487393996855565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29025897306324929331237043 43538845959487393996855565)
            ·
              refine ⟨16327067234807772748820837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43538845959487393996855565 16327067234807772748820837)
              ·
                refine ⟨3061325106526457390403907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16327067234807772748820837 3061325106526457390403907)
                ·
                  refine ⟨4591987659789686085605861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3061325106526457390403907 4591987659789686085605861)
                  ·
                    refine ⟨860997686210566141051099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4591987659789686085605861 860997686210566141051099)
                    ·
                      rfl

theorem cell23_5030361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 4, 1, 4].length) (baseStart_5030361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030361 prefixEnd_5030361 := by exact prefixLift 5030361
  have htrace : WordTrace (prefixWord ++ tailWord_5030361) baseStart_5030361 baseEnd_5030361 := by
    simpa [prefixWord, tailWord_5030361, baseEnd_5030361] using wordTrace_append hprefix tailTrace_5030361
  have hstable : (prefixWord ++ tailWord_5030361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030361).length < 2 ^ (prefixWord ++ tailWord_5030361).sum := by decide
  have hdescent : baseEnd_5030361 < baseStart_5030361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030387 : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 3, 5]
def baseStart_5030387 : Nat := 118140960795 + 5030387 * 2 ^ 59
def prefixEnd_5030387 : Nat := 4983230072969 + 3 ^ 40 * 5030387 * 2
def baseEnd_5030387 : Nat := 861002136376238440476059

theorem tailTrace_5030387 : CollatzResearch.WordTrace tailWord_5030387 prefixEnd_5030387 861002136376238440476059 := by
  unfold tailWord_5030387
  simp only [CollatzResearch.WordTrace]
  refine ⟨183473286826774495546537415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122315524551182997031024943 183473286826774495546537415)
  ·
    refine ⟨275209930240161743319806123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183473286826774495546537415 275209930240161743319806123)
    ·
      refine ⟨412814895360242614979709185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275209930240161743319806123 412814895360242614979709185)
      ·
        refine ⟨309611171520181961234781889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412814895360242614979709185 309611171520181961234781889)
        ·
          refine ⟨232208378640136470926086417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309611171520181961234781889 232208378640136470926086417)
          ·
            refine ⟨174156283980102353194564813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232208378640136470926086417 174156283980102353194564813)
            ·
              refine ⟨65308606492538382447961805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174156283980102353194564813 65308606492538382447961805)
              ·
                refine ⟨24490727434701893417985677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65308606492538382447961805 24490727434701893417985677)
                ·
                  refine ⟨9184022788013210031744629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24490727434701893417985677 9184022788013210031744629)
                  ·
                    refine ⟨861002136376238440476059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9184022788013210031744629 861002136376238440476059)
                    ·
                      rfl

theorem cell23_5030387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 5].length) (baseStart_5030387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030387 prefixEnd_5030387 := by exact prefixLift 5030387
  have htrace : WordTrace (prefixWord ++ tailWord_5030387) baseStart_5030387 baseEnd_5030387 := by
    simpa [prefixWord, tailWord_5030387, baseEnd_5030387] using wordTrace_append hprefix tailTrace_5030387
  have hstable : (prefixWord ++ tailWord_5030387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030387).length < 2 ^ (prefixWord ++ tailWord_5030387).sum := by decide
  have hdescent : baseEnd_5030387 < baseStart_5030387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030444 : List Nat := [2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 3]
def baseStart_5030444 : Nat := 118140960795 + 5030444 * 2 ^ 59
def prefixEnd_5030444 : Nat := 4983230072969 + 3 ^ 40 * 5030444 * 2
def baseEnd_5030444 : Nat := 2583035677526021598415415

theorem tailTrace_5030444 : CollatzResearch.WordTrace tailWord_5030444 prefixEnd_5030444 2583035677526021598415415 := by
  unfold tailWord_5030444
  simp only [CollatzResearch.WordTrace]
  refine ⟨91737682893783997140681193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122316910525045329520908257 91737682893783997140681193)
  ·
    refine ⟨68803262170337997855510895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91737682893783997140681193 68803262170337997855510895)
    ·
      refine ⟨103204893255506996783266343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68803262170337997855510895 103204893255506996783266343)
      ·
        refine ⟨154807339883260495174899515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103204893255506996783266343 154807339883260495174899515)
        ·
          refine ⟨232211009824890742762349273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154807339883260495174899515 232211009824890742762349273)
          ·
            refine ⟨174158257368668057071761955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232211009824890742762349273 174158257368668057071761955)
            ·
              refine ⟨261237386053002085607642933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174158257368668057071761955 261237386053002085607642933)
              ·
                refine ⟨24491004942468945525716525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 261237386053002085607642933 24491004942468945525716525)
                ·
                  refine ⟨9184126853425854572143697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24491004942468945525716525 9184126853425854572143697)
                  ·
                    refine ⟨6888095140069390929107773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9184126853425854572143697 6888095140069390929107773)
                    ·
                      refine ⟨2583035677526021598415415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6888095140069390929107773 2583035677526021598415415)
                      ·
                        rfl

theorem cell23_5030444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 3].length) (baseStart_5030444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030444 prefixEnd_5030444 := by exact prefixLift 5030444
  have htrace : WordTrace (prefixWord ++ tailWord_5030444) baseStart_5030444 baseEnd_5030444 := by
    simpa [prefixWord, tailWord_5030444, baseEnd_5030444] using wordTrace_append hprefix tailTrace_5030444
  have hstable : (prefixWord ++ tailWord_5030444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030444).length < 2 ^ (prefixWord ++ tailWord_5030444).sum := by decide
  have hdescent : baseEnd_5030444 < baseStart_5030444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030461 : List Nat := [1, 4, 1, 3, 2, 2, 2, 1, 1, 1, 5]
def baseStart_5030461 : Nat := 118140960795 + 5030461 * 2 ^ 59
def prefixEnd_5030461 : Nat := 4983230072969 + 3 ^ 40 * 5030461 * 2
def baseEnd_5030461 : Nat := 2583044406697148031902837

theorem tailTrace_5030461 : CollatzResearch.WordTrace tailWord_5030461 prefixEnd_5030461 2583044406697148031902837 := by
  unfold tailWord_5030461
  simp only [CollatzResearch.WordTrace]
  refine ⟨183475985828506406184731237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122317323885670937456487491 183475985828506406184731237)
  ·
    refine ⟨34401747342844951159637107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183475985828506406184731237 34401747342844951159637107)
    ·
      refine ⟨51602621014267426739455661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34401747342844951159637107 51602621014267426739455661)
      ·
        refine ⟨19350982880350285027295873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51602621014267426739455661 19350982880350285027295873)
        ·
          refine ⟨14513237160262713770471905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19350982880350285027295873 14513237160262713770471905)
          ·
            refine ⟨10884927870197035327853929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14513237160262713770471905 10884927870197035327853929)
            ·
              refine ⟨8163695902647776495890447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10884927870197035327853929 8163695902647776495890447)
              ·
                refine ⟨12245543853971664743835671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8163695902647776495890447 12245543853971664743835671)
                ·
                  refine ⟨18368315780957497115753507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12245543853971664743835671 18368315780957497115753507)
                  ·
                    refine ⟨27552473671436245673630261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18368315780957497115753507 27552473671436245673630261)
                    ·
                      refine ⟨2583044406697148031902837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27552473671436245673630261 2583044406697148031902837)
                      ·
                        rfl

theorem cell23_5030461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_5030461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030461 prefixEnd_5030461 := by exact prefixLift 5030461
  have htrace : WordTrace (prefixWord ++ tailWord_5030461) baseStart_5030461 baseEnd_5030461 := by
    simpa [prefixWord, tailWord_5030461, baseEnd_5030461] using wordTrace_append hprefix tailTrace_5030461
  have hstable : (prefixWord ++ tailWord_5030461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030461).length < 2 ^ (prefixWord ++ tailWord_5030461).sum := by decide
  have hdescent : baseEnd_5030461 < baseStart_5030461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030507 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 3, 8]
def baseStart_5030507 : Nat := 118140960795 + 5030507 * 2 ^ 59
def prefixEnd_5030507 : Nat := 4983230072969 + 3 ^ 40 * 5030507 * 2
def baseEnd_5030507 : Nat := 861022675602418283975875

theorem tailTrace_5030507 : CollatzResearch.WordTrace tailWord_5030507 prefixEnd_5030507 861022675602418283975875 := by
  unfold tailWord_5030507
  simp only [CollatzResearch.WordTrace]
  refine ⟨183477663586339756040905775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122318442390893170693937183 183477663586339756040905775)
  ·
    refine ⟨275216495379509634061358663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183477663586339756040905775 275216495379509634061358663)
    ·
      refine ⟨412824743069264451092037995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275216495379509634061358663 412824743069264451092037995)
      ·
        refine ⟨619237114603896676638056993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412824743069264451092037995 619237114603896676638056993)
        ·
          refine ⟨464427835952922507478542745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 619237114603896676638056993 464427835952922507478542745)
          ·
            refine ⟨348320876964691880608907059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 464427835952922507478542745 348320876964691880608907059)
            ·
              refine ⟨522481315447037820913360589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348320876964691880608907059 522481315447037820913360589)
              ·
                refine ⟨195930493292639182842510221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 522481315447037820913360589 195930493292639182842510221)
                ·
                  refine ⟨73473934984739693565941333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 195930493292639182842510221 73473934984739693565941333)
                  ·
                    refine ⟨861022675602418283975875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73473934984739693565941333 861022675602418283975875)
                    ·
                      rfl

theorem cell23_5030507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 8].length) (baseStart_5030507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030507 prefixEnd_5030507 := by exact prefixLift 5030507
  have htrace : WordTrace (prefixWord ++ tailWord_5030507) baseStart_5030507 baseEnd_5030507 := by
    simpa [prefixWord, tailWord_5030507, baseEnd_5030507] using wordTrace_append hprefix tailTrace_5030507
  have hstable : (prefixWord ++ tailWord_5030507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030507).length < 2 ^ (prefixWord ++ tailWord_5030507).sum := by decide
  have hdescent : baseEnd_5030507 < baseStart_5030507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030525 : List Nat := [1, 4, 1, 1, 5, 1, 2, 2, 2, 1, 3]
def baseStart_5030525 : Nat := 118140960795 + 5030525 * 2 ^ 59
def prefixEnd_5030525 : Nat := 4983230072969 + 3 ^ 40 * 5030525 * 2
def baseEnd_5030525 : Nat := 2583077269459035781502543

theorem tailTrace_5030525 : CollatzResearch.WordTrace tailWord_5030525 prefixEnd_5030525 2583077269459035781502543 := by
  unfold tailWord_5030525
  simp only [CollatzResearch.WordTrace]
  refine ⟨183478320100274545115061029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122318880066849696743374019 183478320100274545115061029)
  ·
    refine ⟨34402185018801477209073943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183478320100274545115061029 34402185018801477209073943)
    ·
      refine ⟨51603277528202215813610915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34402185018801477209073943 51603277528202215813610915)
      ·
        refine ⟨77404916292303323720416373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51603277528202215813610915 77404916292303323720416373)
        ·
          refine ⟨7256710902403436598789035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77404916292303323720416373 7256710902403436598789035)
          ·
            refine ⟨10885066353605154898183553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7256710902403436598789035 10885066353605154898183553)
            ·
              refine ⟨8163799765203866173637665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10885066353605154898183553 8163799765203866173637665)
              ·
                refine ⟨6122849823902899630228249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8163799765203866173637665 6122849823902899630228249)
                ·
                  refine ⟨4592137367927174722671187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6122849823902899630228249 4592137367927174722671187)
                  ·
                    refine ⟨6888206051890762084006781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4592137367927174722671187 6888206051890762084006781)
                    ·
                      refine ⟨2583077269459035781502543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6888206051890762084006781 2583077269459035781502543)
                      ·
                        rfl

theorem cell23_5030525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_5030525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030525 prefixEnd_5030525 := by exact prefixLift 5030525
  have htrace : WordTrace (prefixWord ++ tailWord_5030525) baseStart_5030525 baseEnd_5030525 := by
    simpa [prefixWord, tailWord_5030525, baseEnd_5030525] using wordTrace_append hprefix tailTrace_5030525
  have hstable : (prefixWord ++ tailWord_5030525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030525).length < 2 ^ (prefixWord ++ tailWord_5030525).sum := by decide
  have hdescent : baseEnd_5030525 < baseStart_5030525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030624 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 5]
def baseStart_5030624 : Nat := 118140960795 + 5030624 * 2 ^ 59
def prefixEnd_5030624 : Nat := 4983230072969 + 3 ^ 40 * 5030624 * 2
def baseEnd_5030624 : Nat := 2583128104043830894164587

theorem tailTrace_5030624 : CollatzResearch.WordTrace tailWord_5030624 prefixEnd_5030624 2583128104043830894164587 := by
  unfold tailWord_5030624
  simp only [CollatzResearch.WordTrace]
  refine ⟨91740965463457942511457463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122321287284610590015276617 91740965463457942511457463)
  ·
    refine ⟨137611448195186913767186195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91740965463457942511457463 137611448195186913767186195)
    ·
      refine ⟨206417172292780370650779293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137611448195186913767186195 206417172292780370650779293)
      ·
        refine ⟨77406439609792638994042235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206417172292780370650779293 77406439609792638994042235)
        ·
          refine ⟨116109659414688958491063353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77406439609792638994042235 116109659414688958491063353)
          ·
            refine ⟨87082244561016718868297515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116109659414688958491063353 87082244561016718868297515)
            ·
              refine ⟨130623366841525078302446273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87082244561016718868297515 130623366841525078302446273)
              ·
                refine ⟨97967525131143808726834705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130623366841525078302446273 97967525131143808726834705)
                ·
                  refine ⟨73475643848357856545126029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97967525131143808726834705 73475643848357856545126029)
                  ·
                    refine ⟨27553366443134196204422261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73475643848357856545126029 27553366443134196204422261)
                    ·
                      refine ⟨2583128104043830894164587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27553366443134196204422261 2583128104043830894164587)
                      ·
                        rfl

theorem cell23_5030624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_5030624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030624 prefixEnd_5030624 := by exact prefixLift 5030624
  have htrace : WordTrace (prefixWord ++ tailWord_5030624) baseStart_5030624 baseEnd_5030624 := by
    simpa [prefixWord, tailWord_5030624, baseEnd_5030624] using wordTrace_append hprefix tailTrace_5030624
  have hstable : (prefixWord ++ tailWord_5030624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030624).length < 2 ^ (prefixWord ++ tailWord_5030624).sum := by decide
  have hdescent : baseEnd_5030624 < baseStart_5030624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030638 : List Nat := [4, 1, 2, 1, 1, 4, 1, 2, 2, 1, 4]
def baseStart_5030638 : Nat := 118140960795 + 5030638 * 2 ^ 59
def prefixEnd_5030638 : Nat := 4983230072969 + 3 ^ 40 * 5030638 * 2
def baseEnd_5030638 : Nat := 2583135292772993839389523

theorem tailTrace_5030638 : CollatzResearch.WordTrace tailWord_5030638 prefixEnd_5030638 2583135292772993839389523 := by
  unfold tailWord_5030638
  simp only [CollatzResearch.WordTrace]
  refine ⟨22935305193608145676740571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122321627699243443609283045 22935305193608145676740571)
  ·
    refine ⟨34402957790412218515110857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22935305193608145676740571 34402957790412218515110857)
    ·
      refine ⟨25802218342809163886333143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34402957790412218515110857 25802218342809163886333143)
      ·
        refine ⟨38703327514213745829499715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25802218342809163886333143 38703327514213745829499715)
        ·
          refine ⟨58054991271320618744249573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38703327514213745829499715 58054991271320618744249573)
          ·
            refine ⟨10885310863372616014546795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58054991271320618744249573 10885310863372616014546795)
            ·
              refine ⟨16327966295058924021820193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10885310863372616014546795 16327966295058924021820193)
              ·
                refine ⟨12245974721294193016365145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16327966295058924021820193 12245974721294193016365145)
                ·
                  refine ⟨9184481040970644762273859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12245974721294193016365145 9184481040970644762273859)
                  ·
                    refine ⟨13776721561455967143410789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9184481040970644762273859 13776721561455967143410789)
                    ·
                      refine ⟨2583135292772993839389523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13776721561455967143410789 2583135292772993839389523)
                      ·
                        rfl

theorem cell23_5030638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_5030638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030638 prefixEnd_5030638 := by exact prefixLift 5030638
  have htrace : WordTrace (prefixWord ++ tailWord_5030638) baseStart_5030638 baseEnd_5030638 := by
    simpa [prefixWord, tailWord_5030638, baseEnd_5030638] using wordTrace_append hprefix tailTrace_5030638
  have hstable : (prefixWord ++ tailWord_5030638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030638).length < 2 ^ (prefixWord ++ tailWord_5030638).sum := by decide
  have hdescent : baseEnd_5030638 < baseStart_5030638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030711 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 4]
def baseStart_5030711 : Nat := 118140960795 + 5030711 * 2 ^ 59
def prefixEnd_5030711 : Nat := 4983230072969 + 3 ^ 40 * 5030711 * 2
def baseEnd_5030711 : Nat := 2583172776860772053776687

theorem tailTrace_5030711 : CollatzResearch.WordTrace tailWord_5030711 prefixEnd_5030711 2583172776860772053776687 := by
  unfold tailWord_5030711
  simp only [CollatzResearch.WordTrace]
  refine ⟨183485104077600698881331987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122323402718400465920887991 183485104077600698881331987)
  ·
    refine ⟨275227656116401048321997981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183485104077600698881331987 275227656116401048321997981)
    ·
      refine ⟨103210371043650393120749243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275227656116401048321997981 103210371043650393120749243)
      ·
        refine ⟨154815556565475589681123865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103210371043650393120749243 154815556565475589681123865)
        ·
          refine ⟨116111667424106692260842899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154815556565475589681123865 116111667424106692260842899)
          ·
            refine ⟨174167501136160038391264349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116111667424106692260842899 174167501136160038391264349)
            ·
              refine ⟨65312812926060014396724131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174167501136160038391264349 65312812926060014396724131)
              ·
                refine ⟨97969219389090021595086197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65312812926060014396724131 97969219389090021595086197)
                ·
                  refine ⟨9184614317727189524539331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97969219389090021595086197 9184614317727189524539331)
                  ·
                    refine ⟨13776921476590784286808997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9184614317727189524539331 13776921476590784286808997)
                    ·
                      refine ⟨2583172776860772053776687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13776921476590784286808997 2583172776860772053776687)
                      ·
                        rfl

theorem cell23_5030711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_5030711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030711 prefixEnd_5030711 := by exact prefixLift 5030711
  have htrace : WordTrace (prefixWord ++ tailWord_5030711) baseStart_5030711 baseEnd_5030711 := by
    simpa [prefixWord, tailWord_5030711, baseEnd_5030711] using wordTrace_append hprefix tailTrace_5030711
  have hstable : (prefixWord ++ tailWord_5030711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030711).length < 2 ^ (prefixWord ++ tailWord_5030711).sum := by decide
  have hdescent : baseEnd_5030711 < baseStart_5030711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030726 : List Nat := [6, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3]
def baseStart_5030726 : Nat := 118140960795 + 5030726 * 2 ^ 59
def prefixEnd_5030726 : Nat := 4983230072969 + 3 ^ 40 * 5030726 * 2
def baseEnd_5030726 : Nat := 2583180479070589495089119

theorem tailTrace_5030726 : CollatzResearch.WordTrace tailWord_5030726 prefixEnd_5030726 2583180479070589495089119 := by
  unfold tailWord_5030726
  simp only [CollatzResearch.WordTrace]
  refine ⟨5733926599142073638847751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 122323767448364237628752021 5733926599142073638847751)
  ·
    refine ⟨8600889898713110458271627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5733926599142073638847751 8600889898713110458271627)
    ·
      refine ⟨12901334848069665687407441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8600889898713110458271627 12901334848069665687407441)
      ·
        refine ⟨9676001136052249265555581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12901334848069665687407441 9676001136052249265555581)
        ·
          refine ⟨3628500426019593474583343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9676001136052249265555581 3628500426019593474583343)
          ·
            refine ⟨5442750639029390211875015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3628500426019593474583343 5442750639029390211875015)
            ·
              refine ⟨8164125958544085317812523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5442750639029390211875015 8164125958544085317812523)
              ·
                refine ⟨12246188937816127976718785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8164125958544085317812523 12246188937816127976718785)
                ·
                  refine ⟨9184641703362095982539089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12246188937816127976718785 9184641703362095982539089)
                  ·
                    refine ⟨6888481277521571986904317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9184641703362095982539089 6888481277521571986904317)
                    ·
                      refine ⟨2583180479070589495089119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6888481277521571986904317 2583180479070589495089119)
                      ·
                        rfl

theorem cell23_5030726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_5030726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030726 prefixEnd_5030726 := by exact prefixLift 5030726
  have htrace : WordTrace (prefixWord ++ tailWord_5030726) baseStart_5030726 baseEnd_5030726 := by
    simpa [prefixWord, tailWord_5030726, baseEnd_5030726] using wordTrace_append hprefix tailTrace_5030726
  have hstable : (prefixWord ++ tailWord_5030726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030726).length < 2 ^ (prefixWord ++ tailWord_5030726).sum := by decide
  have hdescent : baseEnd_5030726 < baseStart_5030726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030728 : List Nat := [2, 1, 3, 1, 1, 3, 2, 4, 1, 1, 4]
def baseStart_5030728 : Nat := 118140960795 + 5030728 * 2 ^ 59
def prefixEnd_5030728 : Nat := 4983230072969 + 3 ^ 40 * 5030728 * 2
def baseEnd_5030728 : Nat := 2583181506031898487264109

theorem tailTrace_5030728 : CollatzResearch.WordTrace tailWord_5030728 prefixEnd_5030728 2583181506031898487264109 := by
  unfold tailWord_5030728
  simp only [CollatzResearch.WordTrace]
  refine ⟨91742862059269555392350419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122323816079026073856467225 91742862059269555392350419)
  ·
    refine ⟨137614293088904333088525629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91742862059269555392350419 137614293088904333088525629)
    ·
      refine ⟨51605359908339124908197111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137614293088904333088525629 51605359908339124908197111)
      ·
        refine ⟨77408039862508687362295667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51605359908339124908197111 77408039862508687362295667)
        ·
          refine ⟨116112059793763031043443501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77408039862508687362295667 116112059793763031043443501)
          ·
            refine ⟨43542022422661136641291313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 116112059793763031043443501 43542022422661136641291313)
            ·
              refine ⟨32656516816995852480968485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43542022422661136641291313 32656516816995852480968485)
              ·
                refine ⟨6123096903186722340181591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32656516816995852480968485 6123096903186722340181591)
                ·
                  refine ⟨9184645354780083510272387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6123096903186722340181591 9184645354780083510272387)
                  ·
                    refine ⟨13776968032170125265408581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9184645354780083510272387 13776968032170125265408581)
                    ·
                      refine ⟨2583181506031898487264109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13776968032170125265408581 2583181506031898487264109)
                      ·
                        rfl

theorem cell23_5030728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_5030728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030728 prefixEnd_5030728 := by exact prefixLift 5030728
  have htrace : WordTrace (prefixWord ++ tailWord_5030728) baseStart_5030728 baseEnd_5030728 := by
    simpa [prefixWord, tailWord_5030728, baseEnd_5030728] using wordTrace_append hprefix tailTrace_5030728
  have hstable : (prefixWord ++ tailWord_5030728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030728).length < 2 ^ (prefixWord ++ tailWord_5030728).sum := by decide
  have hdescent : baseEnd_5030728 < baseStart_5030728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030732 : List Nat := [2, 2, 1, 3, 3, 3, 1, 1, 2, 3, 2]
def baseStart_5030732 : Nat := 118140960795 + 5030732 * 2 ^ 59
def prefixEnd_5030732 : Nat := 4983230072969 + 3 ^ 40 * 5030732 * 2
def baseEnd_5030732 : Nat := 2583183559954516471614091

theorem tailTrace_5030732 : CollatzResearch.WordTrace tailWord_5030732 prefixEnd_5030732 2583183559954516471614091 := by
  unfold tailWord_5030732
  simp only [CollatzResearch.WordTrace]
  refine ⟨91742935005262309733923225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122323913340349746311897633 91742935005262309733923225)
  ·
    refine ⟨68807201253946732300442419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91742935005262309733923225 68807201253946732300442419)
    ·
      refine ⟨103210801880920098450663629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68807201253946732300442419 103210801880920098450663629)
      ·
        refine ⟨38704050705345036918998861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103210801880920098450663629 38704050705345036918998861)
        ·
          refine ⟨14514019014504388844624573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38704050705345036918998861 14514019014504388844624573)
          ·
            refine ⟨5442757130439145816734215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14514019014504388844624573 5442757130439145816734215)
            ·
              refine ⟨8164135695658718725101323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5442757130439145816734215 8164135695658718725101323)
              ·
                refine ⟨12246203543488078087651985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8164135695658718725101323 12246203543488078087651985)
                ·
                  refine ⟨9184652657616058565738989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12246203543488078087651985 9184652657616058565738989)
                  ·
                    refine ⟨3444244746606021962152121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9184652657616058565738989 3444244746606021962152121)
                    ·
                      refine ⟨2583183559954516471614091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3444244746606021962152121 2583183559954516471614091)
                      ·
                        rfl

theorem cell23_5030732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_5030732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030732 prefixEnd_5030732 := by exact prefixLift 5030732
  have htrace : WordTrace (prefixWord ++ tailWord_5030732) baseStart_5030732 baseEnd_5030732 := by
    simpa [prefixWord, tailWord_5030732, baseEnd_5030732] using wordTrace_append hprefix tailTrace_5030732
  have hstable : (prefixWord ++ tailWord_5030732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030732).length < 2 ^ (prefixWord ++ tailWord_5030732).sum := by decide
  have hdescent : baseEnd_5030732 < baseStart_5030732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030738 : List Nat := [3, 2, 2, 1, 1, 2, 2, 2, 4, 4]
def baseStart_5030738 : Nat := 118140960795 + 5030738 * 2 ^ 59
def prefixEnd_5030738 : Nat := 4983230072969 + 3 ^ 40 * 5030738 * 2
def baseEnd_5030738 : Nat := 861062213612814482713021

theorem tailTrace_5030738 : CollatzResearch.WordTrace tailWord_5030738 prefixEnd_5030738 861062213612814482713021 := by
  unfold tailWord_5030738
  simp only [CollatzResearch.WordTrace]
  refine ⟨45871522212125720623141217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122324059232335254995043245 45871522212125720623141217)
  ·
    refine ⟨34403641659094290467355913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45871522212125720623141217 34403641659094290467355913)
    ·
      refine ⟨25802731244320717850516935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34403641659094290467355913 25802731244320717850516935)
      ·
        refine ⟨38704096866481076775775403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25802731244320717850516935 38704096866481076775775403)
        ·
          refine ⟨58056145299721615163663105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38704096866481076775775403 58056145299721615163663105)
          ·
            refine ⟨43542108974791211372747329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58056145299721615163663105 43542108974791211372747329)
            ·
              refine ⟨32656581731093408529560497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43542108974791211372747329 32656581731093408529560497)
              ·
                refine ⟨24492436298320056397170373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32656581731093408529560497 24492436298320056397170373)
                ·
                  refine ⟨4592331805935010574469445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24492436298320056397170373 4592331805935010574469445)
                  ·
                    refine ⟨861062213612814482713021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4592331805935010574469445 861062213612814482713021)
                    ·
                      rfl

theorem cell23_5030738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_5030738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030738 prefixEnd_5030738 := by exact prefixLift 5030738
  have htrace : WordTrace (prefixWord ++ tailWord_5030738) baseStart_5030738 baseEnd_5030738 := by
    simpa [prefixWord, tailWord_5030738, baseEnd_5030738] using wordTrace_append hprefix tailTrace_5030738
  have hstable : (prefixWord ++ tailWord_5030738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030738).length < 2 ^ (prefixWord ++ tailWord_5030738).sum := by decide
  have hdescent : baseEnd_5030738 < baseStart_5030738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030745 : List Nat := [1, 2, 1, 2, 2, 4, 4, 1, 1, 1, 4]
def baseStart_5030745 : Nat := 118140960795 + 5030745 * 2 ^ 59
def prefixEnd_5030745 : Nat := 4983230072969 + 3 ^ 40 * 5030745 * 2
def baseEnd_5030745 : Nat := 2583190235203024920751531

theorem tailTrace_5030745 : CollatzResearch.WordTrace tailWord_5030745 prefixEnd_5030745 2583190235203024920751531 := by
  unfold tailWord_5030745
  simp only [CollatzResearch.WordTrace]
  refine ⟨183486344159477522688069689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122324229439651681792046459 183486344159477522688069689)
  ·
    refine ⟨137614758119608142016052267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183486344159477522688069689 137614758119608142016052267)
    ·
      refine ⟨206422137179412213024078401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137614758119608142016052267 206422137179412213024078401)
      ·
        refine ⟨154816602884559159768058801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206422137179412213024078401 154816602884559159768058801)
        ·
          refine ⟨116112452163419369826044101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154816602884559159768058801 116112452163419369826044101)
          ·
            refine ⟨21771084780641131842383269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 116112452163419369826044101 21771084780641131842383269)
            ·
              refine ⟨4082078396370212220446863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21771084780641131842383269 4082078396370212220446863)
              ·
                refine ⟨6123117594555318330670295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4082078396370212220446863 6123117594555318330670295)
                ·
                  refine ⟨9184676391832977496005443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6123117594555318330670295 9184676391832977496005443)
                  ·
                    refine ⟨13777014587749466244008165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9184676391832977496005443 13777014587749466244008165)
                    ·
                      refine ⟨2583190235203024920751531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13777014587749466244008165 2583190235203024920751531)
                      ·
                        rfl

theorem cell23_5030745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 1, 1, 4].length) (baseStart_5030745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030745 prefixEnd_5030745 := by exact prefixLift 5030745
  have htrace : WordTrace (prefixWord ++ tailWord_5030745) baseStart_5030745 baseEnd_5030745 := by
    simpa [prefixWord, tailWord_5030745, baseEnd_5030745] using wordTrace_append hprefix tailTrace_5030745
  have hstable : (prefixWord ++ tailWord_5030745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030745).length < 2 ^ (prefixWord ++ tailWord_5030745).sum := by decide
  have hdescent : baseEnd_5030745 < baseStart_5030745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030755 : List Nat := [1, 1, 1, 5, 3, 1, 3, 2, 2, 4]
def baseStart_5030755 : Nat := 118140960795 + 5030755 * 2 ^ 59
def prefixEnd_5030755 : Nat := 4983230072969 + 3 ^ 40 * 5030755 * 2
def baseEnd_5030755 : Nat := 861065123336523293875495

theorem tailTrace_5030755 : CollatzResearch.WordTrace tailWord_5030755 prefixEnd_5030755 861065123336523293875495 := by
  unfold tailWord_5030755
  simp only [CollatzResearch.WordTrace]
  refine ⟨183486708889441294395933719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122324472592960862930622479 183486708889441294395933719)
  ·
    refine ⟨275230063334161941593900579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183486708889441294395933719 275230063334161941593900579)
    ·
      refine ⟨412845095001242912390850869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275230063334161941593900579 412845095001242912390850869)
      ·
        refine ⟨38704227656366523036642269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 412845095001242912390850869 38704227656366523036642269)
        ·
          refine ⟨14514085371137446138740851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38704227656366523036642269 14514085371137446138740851)
          ·
            refine ⟨21771128056706169208111277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14514085371137446138740851 21771128056706169208111277)
            ·
              refine ⟨8164173021264813453041729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21771128056706169208111277 8164173021264813453041729)
              ·
                refine ⟨6123129765948610089781297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8164173021264813453041729 6123129765948610089781297)
                ·
                  refine ⟨4592347324461457567335973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6123129765948610089781297 4592347324461457567335973)
                  ·
                    refine ⟨861065123336523293875495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4592347324461457567335973 861065123336523293875495)
                    ·
                      rfl

theorem cell23_5030755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 2, 4].length) (baseStart_5030755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030755 prefixEnd_5030755 := by exact prefixLift 5030755
  have htrace : WordTrace (prefixWord ++ tailWord_5030755) baseStart_5030755 baseEnd_5030755 := by
    simpa [prefixWord, tailWord_5030755, baseEnd_5030755] using wordTrace_append hprefix tailTrace_5030755
  have hstable : (prefixWord ++ tailWord_5030755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030755).length < 2 ^ (prefixWord ++ tailWord_5030755).sum := by decide
  have hdescent : baseEnd_5030755 < baseStart_5030755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030761 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 2, 7, 3]
def baseStart_5030761 : Nat := 118140960795 + 5030761 * 2 ^ 59
def prefixEnd_5030761 : Nat := 4983230072969 + 3 ^ 40 * 5030761 * 2
def baseEnd_5030761 : Nat := 2583198450893496858151457

theorem tailTrace_5030761 : CollatzResearch.WordTrace tailWord_5030761 prefixEnd_5030761 2583198450893496858151457 := by
  unfold tailWord_5030761
  simp only [CollatzResearch.WordTrace]
  refine ⟨183486927727419557420652137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122324618484946371613768091 183486927727419557420652137)
  ·
    refine ⟨137615195795564668065489103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183486927727419557420652137 137615195795564668065489103)
    ·
      refine ⟨206422793693347002098233655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137615195795564668065489103 206422793693347002098233655)
      ·
        refine ⟨309634190540020503147350483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206422793693347002098233655 309634190540020503147350483)
        ·
          refine ⟨464451285810030754721025725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309634190540020503147350483 464451285810030754721025725)
          ·
            refine ⟨174169232178761533020384647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 464451285810030754721025725 174169232178761533020384647)
            ·
              refine ⟨261253848268142299530576971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174169232178761533020384647 261253848268142299530576971)
              ·
                refine ⟨391880772402213449295865457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261253848268142299530576971 391880772402213449295865457)
                ·
                  refine ⟨293910579301660086971899093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 391880772402213449295865457 293910579301660086971899093)
                  ·
                    refine ⟨6888529202382658288403885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 293910579301660086971899093 6888529202382658288403885)
                    ·
                      refine ⟨2583198450893496858151457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6888529202382658288403885 2583198450893496858151457)
                      ·
                        rfl

theorem cell23_5030761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 7, 3].length) (baseStart_5030761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030761 prefixEnd_5030761 := by exact prefixLift 5030761
  have htrace : WordTrace (prefixWord ++ tailWord_5030761) baseStart_5030761 baseEnd_5030761 := by
    simpa [prefixWord, tailWord_5030761, baseEnd_5030761] using wordTrace_append hprefix tailTrace_5030761
  have hstable : (prefixWord ++ tailWord_5030761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030761).length < 2 ^ (prefixWord ++ tailWord_5030761).sum := by decide
  have hdescent : baseEnd_5030761 < baseStart_5030761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030781 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 2, 7]
def baseStart_5030781 : Nat := 118140960795 + 5030781 * 2 ^ 59
def prefixEnd_5030781 : Nat := 4983230072969 + 3 ^ 40 * 5030781 * 2
def baseEnd_5030781 : Nat := 861069573502195593300455

theorem tailTrace_5030781 : CollatzResearch.WordTrace tailWord_5030781 prefixEnd_5030781 861069573502195593300455 := by
  unfold tailWord_5030781
  simp only [CollatzResearch.WordTrace]
  refine ⟨183487657187347100836380197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122325104791564733890920131 183487657187347100836380197)
  ·
    refine ⟨34403935722627581406821287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183487657187347100836380197 34403935722627581406821287)
    ·
      refine ⟨51605903583941372110231931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34403935722627581406821287 51605903583941372110231931)
      ·
        refine ⟨77408855375912058165347897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51605903583941372110231931 77408855375912058165347897)
        ·
          refine ⟨58056641531934043624010923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77408855375912058165347897 58056641531934043624010923)
          ·
            refine ⟨87084962297901065436016385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58056641531934043624010923 87084962297901065436016385)
            ·
              refine ⟨65313721723425799077012289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87084962297901065436016385 65313721723425799077012289)
              ·
                refine ⟨48985291292569349307759217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65313721723425799077012289 48985291292569349307759217)
                ·
                  refine ⟨36738968469427011980819413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48985291292569349307759217 36738968469427011980819413)
                  ·
                    refine ⟨861069573502195593300455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36738968469427011980819413 861069573502195593300455)
                    ·
                      rfl

theorem cell23_5030781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_5030781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030781 prefixEnd_5030781 := by exact prefixLift 5030781
  have htrace : WordTrace (prefixWord ++ tailWord_5030781) baseStart_5030781 baseEnd_5030781 := by
    simpa [prefixWord, tailWord_5030781, baseEnd_5030781] using wordTrace_append hprefix tailTrace_5030781
  have hstable : (prefixWord ++ tailWord_5030781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030781).length < 2 ^ (prefixWord ++ tailWord_5030781).sum := by decide
  have hdescent : baseEnd_5030781 < baseStart_5030781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030801 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 4]
def baseStart_5030801 : Nat := 118140960795 + 5030801 * 2 ^ 59
def prefixEnd_5030801 : Nat := 4983230072969 + 3 ^ 40 * 5030801 * 2
def baseEnd_5030801 : Nat := 2583218990119676701651273

theorem tailTrace_5030801 : CollatzResearch.WordTrace tailWord_5030801 prefixEnd_5030801 2583218990119676701651273 := by
  unfold tailWord_5030801
  simp only [CollatzResearch.WordTrace]
  refine ⟨183488386647274644252108257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122325591098183096168072171 183488386647274644252108257)
  ·
    refine ⟨137616289985455983189081193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183488386647274644252108257 137616289985455983189081193)
    ·
      refine ⟨103212217489091987391810895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137616289985455983189081193 103212217489091987391810895)
      ·
        refine ⟨154818326233637981087716343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103212217489091987391810895 154818326233637981087716343)
        ·
          refine ⟨232227489350456971631574515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154818326233637981087716343 232227489350456971631574515)
          ·
            refine ⟨348341234025685457447361773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232227489350456971631574515 348341234025685457447361773)
            ·
              refine ⟨130627962759632046542760665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 348341234025685457447361773 130627962759632046542760665)
              ·
                refine ⟨97970972069724034907070499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130627962759632046542760665 97970972069724034907070499)
                ·
                  refine ⟨146956458104586052360605749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97970972069724034907070499 146956458104586052360605749)
                  ·
                    refine ⟨13777167947304942408806789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 146956458104586052360605749 13777167947304942408806789)
                    ·
                      refine ⟨2583218990119676701651273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13777167947304942408806789 2583218990119676701651273)
                      ·
                        rfl

theorem cell23_5030801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_5030801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030801 prefixEnd_5030801 := by exact prefixLift 5030801
  have htrace : WordTrace (prefixWord ++ tailWord_5030801) baseStart_5030801 baseEnd_5030801 := by
    simpa [prefixWord, tailWord_5030801, baseEnd_5030801] using wordTrace_append hprefix tailTrace_5030801
  have hstable : (prefixWord ++ tailWord_5030801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030801).length < 2 ^ (prefixWord ++ tailWord_5030801).sum := by decide
  have hdescent : baseEnd_5030801 < baseStart_5030801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030835 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 6, 2, 2]
def baseStart_5030835 : Nat := 118140960795 + 5030835 * 2 ^ 59
def prefixEnd_5030835 : Nat := 4983230072969 + 3 ^ 40 * 5030835 * 2
def baseEnd_5030835 : Nat := 2583236448461929568626117

theorem tailTrace_5030835 : CollatzResearch.WordTrace tailWord_5030835 prefixEnd_5030835 2583236448461929568626117 := by
  unfold tailWord_5030835
  simp only [CollatzResearch.WordTrace]
  refine ⟨183489626729151468058845959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122326417819434312039230639 183489626729151468058845959)
  ·
    refine ⟨275234440093727202088268939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183489626729151468058845959 275234440093727202088268939)
    ·
      refine ⟨412851660140590803132403409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275234440093727202088268939 412851660140590803132403409)
      ·
        refine ⟨309638745105443102349302557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412851660140590803132403409 309638745105443102349302557)
        ·
          refine ⟨116114529414541163380988459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 309638745105443102349302557 116114529414541163380988459)
          ·
            refine ⟨174171794121811745071482689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116114529414541163380988459 174171794121811745071482689)
            ·
              refine ⟨130628845591358808803612017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174171794121811745071482689 130628845591358808803612017)
              ·
                refine ⟨97971634193519106602709013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130628845591358808803612017 97971634193519106602709013)
                ·
                  refine ⟨4592420352821208122001985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 97971634193519106602709013 4592420352821208122001985)
                  ·
                    refine ⟨3444315264615906091501489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4592420352821208122001985 3444315264615906091501489)
                    ·
                      refine ⟨2583236448461929568626117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3444315264615906091501489 2583236448461929568626117)
                      ·
                        rfl

theorem cell23_5030835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 6, 2, 2].length) (baseStart_5030835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030835 prefixEnd_5030835 := by exact prefixLift 5030835
  have htrace : WordTrace (prefixWord ++ tailWord_5030835) baseStart_5030835 baseEnd_5030835 := by
    simpa [prefixWord, tailWord_5030835, baseEnd_5030835] using wordTrace_append hprefix tailTrace_5030835
  have hstable : (prefixWord ++ tailWord_5030835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030835).length < 2 ^ (prefixWord ++ tailWord_5030835).sum := by decide
  have hdescent : baseEnd_5030835 < baseStart_5030835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030882 : List Nat := [3, 3, 3, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_5030882 : Nat := 118140960795 + 5030882 * 2 ^ 59
def prefixEnd_5030882 : Nat := 4983230072969 + 3 ^ 40 * 5030882 * 2
def baseEnd_5030882 : Nat := 2583260582052690884738401

theorem tailTrace_5030882 : CollatzResearch.WordTrace tailWord_5030882 prefixEnd_5030882 2583260582052690884738401 := by
  unfold tailWord_5030882
  simp only [CollatzResearch.WordTrace]
  refine ⟨45872835239995298771451725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122327560639987463390537933 45872835239995298771451725)
  ·
    refine ⟨17202313214998237039294397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45872835239995298771451725 17202313214998237039294397)
    ·
      refine ⟨6450867455624338889735399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17202313214998237039294397 6450867455624338889735399)
      ·
        refine ⟨9676301183436508334603099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6450867455624338889735399 9676301183436508334603099)
        ·
          refine ⟨14514451775154762501904649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9676301183436508334603099 14514451775154762501904649)
          ·
            refine ⟨10885838831366071876428487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14514451775154762501904649 10885838831366071876428487)
            ·
              refine ⟨16328758247049107814642731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10885838831366071876428487 16328758247049107814642731)
              ·
                refine ⟨24493137370573661721964097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16328758247049107814642731 24493137370573661721964097)
                ·
                  refine ⟨18369853027930246291473073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24493137370573661721964097 18369853027930246291473073)
                  ·
                    refine ⟨13777389770947684718604805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18369853027930246291473073 13777389770947684718604805)
                    ·
                      refine ⟨2583260582052690884738401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13777389770947684718604805 2583260582052690884738401)
                      ·
                        rfl

theorem cell23_5030882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_5030882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030882 prefixEnd_5030882 := by exact prefixLift 5030882
  have htrace : WordTrace (prefixWord ++ tailWord_5030882) baseStart_5030882 baseEnd_5030882 := by
    simpa [prefixWord, tailWord_5030882, baseEnd_5030882] using wordTrace_append hprefix tailTrace_5030882
  have hstable : (prefixWord ++ tailWord_5030882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030882).length < 2 ^ (prefixWord ++ tailWord_5030882).sum := by decide
  have hdescent : baseEnd_5030882 < baseStart_5030882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030888 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 4, 5]
def baseStart_5030888 : Nat := 118140960795 + 5030888 * 2 ^ 59
def prefixEnd_5030888 : Nat := 4983230072969 + 3 ^ 40 * 5030888 * 2
def baseEnd_5030888 : Nat := 861087887645539287087791

theorem tailTrace_5030888 : CollatzResearch.WordTrace tailWord_5030888 prefixEnd_5030888 861087887645539287087791 := by
  unfold tailWord_5030888
  simp only [CollatzResearch.WordTrace]
  refine ⟨91745779898979729055262659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122327706531972972073683545 91745779898979729055262659)
  ·
    refine ⟨137618669848469593582893989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91745779898979729055262659 137618669848469593582893989)
    ·
      refine ⟨25803500596588048796792623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137618669848469593582893989 25803500596588048796792623)
      ·
        refine ⟨38705250894882073195188935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25803500596588048796792623 38705250894882073195188935)
        ·
          refine ⟨58057876342323109792783403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38705250894882073195188935 58057876342323109792783403)
          ·
            refine ⟨87086814513484664689175105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58057876342323109792783403 87086814513484664689175105)
            ·
              refine ⟨65315110885113498516881329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87086814513484664689175105 65315110885113498516881329)
              ·
                refine ⟨48986333163835123887660997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65315110885113498516881329 48986333163835123887660997)
                ·
                  refine ⟨9184937468219085728936437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48986333163835123887660997 9184937468219085728936437)
                  ·
                    refine ⟨861087887645539287087791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9184937468219085728936437 861087887645539287087791)
                    ·
                      rfl

theorem cell23_5030888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_5030888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030888 prefixEnd_5030888 := by exact prefixLift 5030888
  have htrace : WordTrace (prefixWord ++ tailWord_5030888) baseStart_5030888 baseEnd_5030888 := by
    simpa [prefixWord, tailWord_5030888, baseEnd_5030888] using wordTrace_append hprefix tailTrace_5030888
  have hstable : (prefixWord ++ tailWord_5030888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030888).length < 2 ^ (prefixWord ++ tailWord_5030888).sum := by decide
  have hdescent : baseEnd_5030888 < baseStart_5030888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030928 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 3]
def baseStart_5030928 : Nat := 118140960795 + 5030928 * 2 ^ 59
def prefixEnd_5030928 : Nat := 4983230072969 + 3 ^ 40 * 5030928 * 2
def baseEnd_5030928 : Nat := 2583284202162797704763189

theorem tailTrace_5030928 : CollatzResearch.WordTrace tailWord_5030928 prefixEnd_5030928 2583284202162797704763189 := by
  unfold tailWord_5030928
  simp only [CollatzResearch.WordTrace]
  refine ⟨91746509358907272470990719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122328679145209696627987625 91746509358907272470990719)
  ·
    refine ⟨137619764038360908706486079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91746509358907272470990719 137619764038360908706486079)
    ·
      refine ⟨206429646057541363059729119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137619764038360908706486079 206429646057541363059729119)
      ·
        refine ⟨309644469086312044589593679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206429646057541363059729119 309644469086312044589593679)
        ·
          refine ⟨464466703629468066884390519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309644469086312044589593679 464466703629468066884390519)
          ·
            refine ⟨696700055444202100326585779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464466703629468066884390519 696700055444202100326585779)
            ·
              refine ⟨1045050083166303150489878669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 696700055444202100326585779 1045050083166303150489878669)
              ·
                refine ⟨391893781187363681433704501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1045050083166303150489878669 391893781187363681433704501)
                ·
                  refine ⟨36740041986315345134409797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 391893781187363681433704501 36740041986315345134409797)
                  ·
                    refine ⟨6888757872434127212701837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36740041986315345134409797 6888757872434127212701837)
                    ·
                      refine ⟨2583284202162797704763189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6888757872434127212701837 2583284202162797704763189)
                      ·
                        rfl

theorem cell23_5030928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 3].length) (baseStart_5030928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030928 prefixEnd_5030928 := by exact prefixLift 5030928
  have htrace : WordTrace (prefixWord ++ tailWord_5030928) baseStart_5030928 baseEnd_5030928 := by
    simpa [prefixWord, tailWord_5030928, baseEnd_5030928] using wordTrace_append hprefix tailTrace_5030928
  have hstable : (prefixWord ++ tailWord_5030928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030928).length < 2 ^ (prefixWord ++ tailWord_5030928).sum := by decide
  have hdescent : baseEnd_5030928 < baseStart_5030928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030938 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 2, 1, 6]
def baseStart_5030938 : Nat := 118140960795 + 5030938 * 2 ^ 59
def prefixEnd_5030938 : Nat := 4983230072969 + 3 ^ 40 * 5030938 * 2
def baseEnd_5030938 : Nat := 2583289336969342665638143

theorem tailTrace_5030938 : CollatzResearch.WordTrace tailWord_5030938 prefixEnd_5030938 2583289336969342665638143 := by
  unfold tailWord_5030938
  simp only [CollatzResearch.WordTrace]
  refine ⟨45873345861944579162461367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122328922298518877766563645 45873345861944579162461367)
  ·
    refine ⟨68810018792916868743692051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45873345861944579162461367 68810018792916868743692051)
    ·
      refine ⟨103215028189375303115538077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68810018792916868743692051 103215028189375303115538077)
      ·
        refine ⟨38705635571015738668326779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103215028189375303115538077 38705635571015738668326779)
        ·
          refine ⟨58058453356523608002490169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38705635571015738668326779 58058453356523608002490169)
          ·
            refine ⟨43543840017392706001867627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58058453356523608002490169 43543840017392706001867627)
            ·
              refine ⟨65315760026089059002801441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43543840017392706001867627 65315760026089059002801441)
              ·
                refine ⟨48986820019566794252101081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65315760026089059002801441 48986820019566794252101081)
                ·
                  refine ⟨36740115014675095689075811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48986820019566794252101081 36740115014675095689075811)
                  ·
                    refine ⟨55110172522012643533613717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36740115014675095689075811 55110172522012643533613717)
                    ·
                      refine ⟨2583289336969342665638143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55110172522012643533613717 2583289336969342665638143)
                      ·
                        rfl

theorem cell23_5030938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_5030938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030938 prefixEnd_5030938 := by exact prefixLift 5030938
  have htrace : WordTrace (prefixWord ++ tailWord_5030938) baseStart_5030938 baseEnd_5030938 := by
    simpa [prefixWord, tailWord_5030938, baseEnd_5030938] using wordTrace_append hprefix tailTrace_5030938
  have hstable : (prefixWord ++ tailWord_5030938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030938).length < 2 ^ (prefixWord ++ tailWord_5030938).sum := by decide
  have hdescent : baseEnd_5030938 < baseStart_5030938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030945 : List Nat := [1, 2, 3, 2, 3, 1, 1, 2, 1, 4, 3]
def baseStart_5030945 : Nat := 118140960795 + 5030945 * 2 ^ 59
def prefixEnd_5030945 : Nat := 4983230072969 + 3 ^ 40 * 5030945 * 2
def baseEnd_5030945 : Nat := 2583292931333924138250611

theorem tailTrace_5030945 : CollatzResearch.WordTrace tailWord_5030945 prefixEnd_5030945 2583292931333924138250611 := by
  unfold tailWord_5030945
  simp only [CollatzResearch.WordTrace]
  refine ⟨183493638758752956845350289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122329092505835304563566859 183493638758752956845350289)
  ·
    refine ⟨137620229069064717634012717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183493638758752956845350289 137620229069064717634012717)
    ·
      refine ⟨51607585900899269112754769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137620229069064717634012717 51607585900899269112754769)
      ·
        refine ⟨38705689425674451834566077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51607585900899269112754769 38705689425674451834566077)
        ·
          refine ⟨14514633534627919437962279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38705689425674451834566077 14514633534627919437962279)
          ·
            refine ⟨21771950301941879156943419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14514633534627919437962279 21771950301941879156943419)
            ·
              refine ⟨32657925452912818735415129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21771950301941879156943419 32657925452912818735415129)
              ·
                refine ⟨24493444089684614051561347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32657925452912818735415129 24493444089684614051561347)
                ·
                  refine ⟨36740166134526921077342021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24493444089684614051561347 36740166134526921077342021)
                  ·
                    refine ⟨6888781150223797702001629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36740166134526921077342021 6888781150223797702001629)
                    ·
                      refine ⟨2583292931333924138250611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6888781150223797702001629 2583292931333924138250611)
                      ·
                        rfl

theorem cell23_5030945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_5030945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030945 prefixEnd_5030945 := by exact prefixLift 5030945
  have htrace : WordTrace (prefixWord ++ tailWord_5030945) baseStart_5030945 baseEnd_5030945 := by
    simpa [prefixWord, tailWord_5030945, baseEnd_5030945] using wordTrace_append hprefix tailTrace_5030945
  have hstable : (prefixWord ++ tailWord_5030945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030945).length < 2 ^ (prefixWord ++ tailWord_5030945).sum := by decide
  have hdescent : baseEnd_5030945 < baseStart_5030945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030969 : List Nat := [1, 2, 1, 5, 2, 1, 3, 3, 1, 4]
def baseStart_5030969 : Nat := 118140960795 + 5030969 * 2 ^ 59
def prefixEnd_5030969 : Nat := 4983230072969 + 3 ^ 40 * 5030969 * 2
def baseEnd_5030969 : Nat := 861101751623210681450167

theorem tailTrace_5030969 : CollatzResearch.WordTrace tailWord_5030969 prefixEnd_5030969 861101751623210681450167 := by
  unfold tailWord_5030969
  simp only [CollatzResearch.WordTrace]
  refine ⟨183494514110666008944223961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122329676073777339296149307 183494514110666008944223961)
  ·
    refine ⟨137620885582999506708167971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183494514110666008944223961 137620885582999506708167971)
    ·
      refine ⟨206431328374499260062251957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137620885582999506708167971 206431328374499260062251957)
      ·
        refine ⟨19352937035109305630836121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 206431328374499260062251957 19352937035109305630836121)
        ·
          refine ⟨14514702776331979223127091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19352937035109305630836121 14514702776331979223127091)
          ·
            refine ⟨21772054164497968834690637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14514702776331979223127091 21772054164497968834690637)
            ·
              refine ⟨8164520311686738313008989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21772054164497968834690637 8164520311686738313008989)
              ·
                refine ⟨3061695116882526867378371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8164520311686738313008989 3061695116882526867378371)
                ·
                  refine ⟨4592542675323790301067557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3061695116882526867378371 4592542675323790301067557)
                  ·
                    refine ⟨861101751623210681450167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4592542675323790301067557 861101751623210681450167)
                    ·
                      rfl

theorem cell23_5030969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 3, 1, 4].length) (baseStart_5030969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030969 prefixEnd_5030969 := by exact prefixLift 5030969
  have htrace : WordTrace (prefixWord ++ tailWord_5030969) baseStart_5030969 baseEnd_5030969 := by
    simpa [prefixWord, tailWord_5030969, baseEnd_5030969] using wordTrace_append hprefix tailTrace_5030969
  have hstable : (prefixWord ++ tailWord_5030969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030969).length < 2 ^ (prefixWord ++ tailWord_5030969).sum := by decide
  have hdescent : baseEnd_5030969 < baseStart_5030969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030982 : List Nat := [6, 1, 1, 1, 1, 2, 2, 1, 8]
def baseStart_5030982 : Nat := 118140960795 + 5030982 * 2 ^ 59
def prefixEnd_5030982 : Nat := 4983230072969 + 3 ^ 40 * 5030982 * 2
def baseEnd_5030982 : Nat := 287034658902015610387549

theorem tailTrace_5030982 : CollatzResearch.WordTrace tailWord_5030982 prefixEnd_5030982 287034658902015610387549 := by
  unfold tailWord_5030982
  simp only [CollatzResearch.WordTrace]
  refine ⟨5734218383113091005138975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 122329992173079274776298133 5734218383113091005138975)
  ·
    refine ⟨8601327574669636507708463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5734218383113091005138975 8601327574669636507708463)
    ·
      refine ⟨12901991362004454761562695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8601327574669636507708463 12901991362004454761562695)
      ·
        refine ⟨19352987043006682142344043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12901991362004454761562695 19352987043006682142344043)
        ·
          refine ⟨29029480564510023213516065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19352987043006682142344043 29029480564510023213516065)
          ·
            refine ⟨21772110423382517410137049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29029480564510023213516065 21772110423382517410137049)
            ·
              refine ⟨16329082817536888057602787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21772110423382517410137049 16329082817536888057602787)
              ·
                refine ⟨24493624226305332086404181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16329082817536888057602787 24493624226305332086404181)
                ·
                  refine ⟨287034658902015610387549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24493624226305332086404181 287034658902015610387549)
                  ·
                    rfl

theorem cell23_5030982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_5030982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030982 prefixEnd_5030982 := by exact prefixLift 5030982
  have htrace : WordTrace (prefixWord ++ tailWord_5030982) baseStart_5030982 baseEnd_5030982 := by
    simpa [prefixWord, tailWord_5030982, baseEnd_5030982] using wordTrace_append hprefix tailTrace_5030982
  have hstable : (prefixWord ++ tailWord_5030982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030982).length < 2 ^ (prefixWord ++ tailWord_5030982).sum := by decide
  have hdescent : baseEnd_5030982 < baseStart_5030982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030985 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 3, 5, 2]
def baseStart_5030985 : Nat := 118140960795 + 5030985 * 2 ^ 59
def prefixEnd_5030985 : Nat := 4983230072969 + 3 ^ 40 * 5030985 * 2
def baseEnd_5030985 : Nat := 2583313470560103981750427

theorem tailTrace_5030985 : CollatzResearch.WordTrace tailWord_5030985 prefixEnd_5030985 2583313470560103981750427 := by
  unfold tailWord_5030985
  simp only [CollatzResearch.WordTrace]
  refine ⟨183495097678608043676806409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122330065119072029117870939 183495097678608043676806409)
  ·
    refine ⟨137621323258956032757604807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183495097678608043676806409 137621323258956032757604807)
    ·
      refine ⟨206431984888434049136407211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137621323258956032757604807 206431984888434049136407211)
      ·
        refine ⟨309647977332651073704610817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206431984888434049136407211 309647977332651073704610817)
        ·
          refine ⟨232235982999488305278458113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309647977332651073704610817 232235982999488305278458113)
          ·
            refine ⟨174176987249616228958843585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232235982999488305278458113 174176987249616228958843585)
            ·
              refine ⟨130632740437212171719132689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174176987249616228958843585 130632740437212171719132689)
              ·
                refine ⟨97974555327909128789349517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130632740437212171719132689 97974555327909128789349517)
                ·
                  refine ⟨36740458247965923296006069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97974555327909128789349517 36740458247965923296006069)
                  ·
                    refine ⟨3444417960746805309000569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36740458247965923296006069 3444417960746805309000569)
                    ·
                      refine ⟨2583313470560103981750427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3444417960746805309000569 2583313470560103981750427)
                      ·
                        rfl

theorem cell23_5030985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 5, 2].length) (baseStart_5030985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030985 prefixEnd_5030985 := by exact prefixLift 5030985
  have htrace : WordTrace (prefixWord ++ tailWord_5030985) baseStart_5030985 baseEnd_5030985 := by
    simpa [prefixWord, tailWord_5030985, baseEnd_5030985] using wordTrace_append hprefix tailTrace_5030985
  have hstable : (prefixWord ++ tailWord_5030985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030985).length < 2 ^ (prefixWord ++ tailWord_5030985).sum := by decide
  have hdescent : baseEnd_5030985 < baseStart_5030985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5030988 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 2, 1, 7]
def baseStart_5030988 : Nat := 118140960795 + 5030988 * 2 ^ 59
def prefixEnd_5030988 : Nat := 4983230072969 + 3 ^ 40 * 5030988 * 2
def baseEnd_5030988 : Nat := 2583315011002067470012913

theorem tailTrace_5030988 : CollatzResearch.WordTrace tailWord_5030988 prefixEnd_5030988 2583315011002067470012913 := by
  unfold tailWord_5030988
  simp only [CollatzResearch.WordTrace]
  refine ⟨91747603548798587594582809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122330138065064783459443745 91747603548798587594582809)
  ·
    refine ⟨68810702661598940695937107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91747603548798587594582809 68810702661598940695937107)
    ·
      refine ⟨103216053992398411043905661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68810702661598940695937107 103216053992398411043905661)
      ·
        refine ⟨38706020247149404141464623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103216053992398411043905661 38706020247149404141464623)
        ·
          refine ⟨58059030370724106212196935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38706020247149404141464623 58059030370724106212196935)
          ·
            refine ⟨87088545556086159318295403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58059030370724106212196935 87088545556086159318295403)
            ·
              refine ⟨130632818334129238977443105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87088545556086159318295403 130632818334129238977443105)
              ·
                refine ⟨97974613750596929233082329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130632818334129238977443105 97974613750596929233082329)
                ·
                  refine ⟨73480960312947696924811747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97974613750596929233082329 73480960312947696924811747)
                  ·
                    refine ⟨110221440469421545387217621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73480960312947696924811747 110221440469421545387217621)
                    ·
                      refine ⟨2583315011002067470012913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 110221440469421545387217621 2583315011002067470012913)
                      ·
                        rfl

theorem cell23_5030988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_5030988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5030988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5030988 prefixEnd_5030988 := by exact prefixLift 5030988
  have htrace : WordTrace (prefixWord ++ tailWord_5030988) baseStart_5030988 baseEnd_5030988 := by
    simpa [prefixWord, tailWord_5030988, baseEnd_5030988] using wordTrace_append hprefix tailTrace_5030988
  have hstable : (prefixWord ++ tailWord_5030988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5030988).length < 2 ^ (prefixWord ++ tailWord_5030988).sum := by decide
  have hdescent : baseEnd_5030988 < baseStart_5030988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5030988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5031025 : List Nat := [1, 2, 2, 2, 1, 1, 2, 4, 4, 4]
def baseStart_5031025 : Nat := 118140960795 + 5031025 * 2 ^ 59
def prefixEnd_5031025 : Nat := 4983230072969 + 3 ^ 40 * 5031025 * 2
def baseEnd_5031025 : Nat := 861111336595427941750081

theorem tailTrace_5031025 : CollatzResearch.WordTrace tailWord_5031025 prefixEnd_5031025 861111336595427941750081 := by
  unfold tailWord_5031025
  simp only [CollatzResearch.WordTrace]
  refine ⟨183496556598463130508262529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122331037732308753672175019 183496556598463130508262529)
  ·
    refine ⟨137622417448847347881196897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183496556598463130508262529 137622417448847347881196897)
    ·
      refine ⟨103216813086635510910897673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137622417448847347881196897 103216813086635510910897673)
      ·
        refine ⟨77412609814976633183173255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103216813086635510910897673 77412609814976633183173255)
        ·
          refine ⟨116118914722464949774759883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77412609814976633183173255 116118914722464949774759883)
          ·
            refine ⟨174178372083697424662139825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116118914722464949774759883 174178372083697424662139825)
            ·
              refine ⟨130633779062773068496604869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174178372083697424662139825 130633779062773068496604869)
              ·
                refine ⟨24493833574269950343113413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130633779062773068496604869 24493833574269950343113413)
                ·
                  refine ⟨4592593795175615689333765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24493833574269950343113413 4592593795175615689333765)
                  ·
                    refine ⟨861111336595427941750081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4592593795175615689333765 861111336595427941750081)
                    ·
                      rfl

theorem cell23_5031025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 4, 4].length) (baseStart_5031025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5031025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5031025 prefixEnd_5031025 := by exact prefixLift 5031025
  have htrace : WordTrace (prefixWord ++ tailWord_5031025) baseStart_5031025 baseEnd_5031025 := by
    simpa [prefixWord, tailWord_5031025, baseEnd_5031025] using wordTrace_append hprefix tailTrace_5031025
  have hstable : (prefixWord ++ tailWord_5031025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5031025).length < 2 ^ (prefixWord ++ tailWord_5031025).sum := by decide
  have hdescent : baseEnd_5031025 < baseStart_5031025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5031025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
