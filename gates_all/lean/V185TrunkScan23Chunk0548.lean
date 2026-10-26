import V185TrunkScan23Chunk0547

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3239359 : List Nat := [1, 1, 2, 2, 2, 1, 1, 8, 5]
def baseStart_3239359 : Nat := 118140960795 + 3239359 * 2 ^ 59
def prefixEnd_3239359 : Nat := 4983230072969 + 3 ^ 40 * 3239359 * 2
def baseEnd_3239359 : Nat := 184816464385321858523885

theorem tailTrace_3239359 : CollatzResearch.WordTrace tailWord_3239359 prefixEnd_3239359 184816464385321858523885 := by
  unfold tailWord_3239359
  simp only [CollatzResearch.WordTrace]
  refine ⟨118149129071363056316745131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78766086047575370877830087 118149129071363056316745131)
  ·
    refine ⟨177223693607044584475117697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118149129071363056316745131 177223693607044584475117697)
    ·
      refine ⟨132917770205283438356338273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177223693607044584475117697 132917770205283438356338273)
      ·
        refine ⟨99688327653962578767253705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132917770205283438356338273 99688327653962578767253705)
        ·
          refine ⟨74766245740471934075440279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99688327653962578767253705 74766245740471934075440279)
          ·
            refine ⟨112149368610707901113160419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74766245740471934075440279 112149368610707901113160419)
            ·
              refine ⟨168224052916061851669740629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112149368610707901113160419 168224052916061851669740629)
              ·
                refine ⟨1971375620110099824254773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 168224052916061851669740629 1971375620110099824254773)
                ·
                  refine ⟨184816464385321858523885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1971375620110099824254773 184816464385321858523885)
                  ·
                    rfl

theorem cell23_3239359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 8, 5].length) (baseStart_3239359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239359 prefixEnd_3239359 := by exact prefixLift 3239359
  have htrace : WordTrace (prefixWord ++ tailWord_3239359) baseStart_3239359 baseEnd_3239359 := by
    simpa [prefixWord, tailWord_3239359, baseEnd_3239359] using wordTrace_append hprefix tailTrace_3239359
  have hstable : (prefixWord ++ tailWord_3239359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239359).length < 2 ^ (prefixWord ++ tailWord_3239359).sum := by decide
  have hdescent : baseEnd_3239359 < baseStart_3239359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239370 : List Nat := [3, 1, 2, 1, 2, 3, 4, 1, 2, 2, 2]
def baseStart_3239370 : Nat := 118140960795 + 3239370 * 2 ^ 59
def prefixEnd_3239370 : Nat := 4983230072969 + 3 ^ 40 * 3239370 * 2
def baseEnd_3239370 : Nat := 1663353827755096183677415

theorem tailTrace_3239370 : CollatzResearch.WordTrace tailWord_3239370 prefixEnd_3239370 1663353827755096183677415 := by
  unfold tailWord_3239370
  simp only [CollatzResearch.WordTrace]
  refine ⟨29537382568580801298848891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78766353516215470130263709 29537382568580801298848891)
  ·
    refine ⟨44306073852871201948273337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29537382568580801298848891 44306073852871201948273337)
    ·
      refine ⟨33229555389653401461205003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44306073852871201948273337 33229555389653401461205003)
      ·
        refine ⟨49844333084480102191807505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33229555389653401461205003 49844333084480102191807505)
        ·
          refine ⟨37383249813360076643855629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49844333084480102191807505 37383249813360076643855629)
          ·
            refine ⟨14018718680010028741445861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37383249813360076643855629 14018718680010028741445861)
            ·
              refine ⟨2628509752501880389021099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14018718680010028741445861 2628509752501880389021099)
              ·
                refine ⟨3942764628752820583531649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2628509752501880389021099 3942764628752820583531649)
                ·
                  refine ⟨2957073471564615437648737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3942764628752820583531649 2957073471564615437648737)
                  ·
                    refine ⟨2217805103673461578236553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2957073471564615437648737 2217805103673461578236553)
                    ·
                      refine ⟨1663353827755096183677415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2217805103673461578236553 1663353827755096183677415)
                      ·
                        rfl

theorem cell23_3239370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 2, 2, 2].length) (baseStart_3239370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239370 prefixEnd_3239370 := by exact prefixLift 3239370
  have htrace : WordTrace (prefixWord ++ tailWord_3239370) baseStart_3239370 baseEnd_3239370 := by
    simpa [prefixWord, tailWord_3239370, baseEnd_3239370] using wordTrace_append hprefix tailTrace_3239370
  have hstable : (prefixWord ++ tailWord_3239370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239370).length < 2 ^ (prefixWord ++ tailWord_3239370).sum := by decide
  have hdescent : baseEnd_3239370 < baseStart_3239370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239399 : List Nat := [1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 5]
def baseStart_3239399 : Nat := 118140960795 + 3239399 * 2 ^ 59
def prefixEnd_3239399 : Nat := 4983230072969 + 3 ^ 40 * 3239399 * 2
def baseEnd_3239399 : Nat := 1663368718694076570214781

theorem tailTrace_3239399 : CollatzResearch.WordTrace tailWord_3239399 prefixEnd_3239399 1663368718694076570214781 := by
  unfold tailWord_3239399
  simp only [CollatzResearch.WordTrace]
  refine ⟨118150587991218143148201251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78767058660812095432134167 118150587991218143148201251)
  ·
    refine ⟨177225881986827214722301877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118150587991218143148201251 177225881986827214722301877)
    ·
      refine ⟨16614926436265051380215801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177225881986827214722301877 16614926436265051380215801)
      ·
        refine ⟨12461194827198788535161851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16614926436265051380215801 12461194827198788535161851)
        ·
          refine ⟨18691792240798182802742777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12461194827198788535161851 18691792240798182802742777)
          ·
            refine ⟨14018844180598637102057083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18691792240798182802742777 14018844180598637102057083)
            ·
              refine ⟨21028266270897955653085625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14018844180598637102057083 21028266270897955653085625)
              ·
                refine ⟨15771199703173466739814219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21028266270897955653085625 15771199703173466739814219)
                ·
                  refine ⟨23656799554760200109721329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15771199703173466739814219 23656799554760200109721329)
                  ·
                    refine ⟨17742599666070150082290997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23656799554760200109721329 17742599666070150082290997)
                    ·
                      refine ⟨1663368718694076570214781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17742599666070150082290997 1663368718694076570214781)
                      ·
                        rfl

theorem cell23_3239399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_3239399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239399 prefixEnd_3239399 := by exact prefixLift 3239399
  have htrace : WordTrace (prefixWord ++ tailWord_3239399) baseStart_3239399 baseEnd_3239399 := by
    simpa [prefixWord, tailWord_3239399, baseEnd_3239399] using wordTrace_append hprefix tailTrace_3239399
  have hstable : (prefixWord ++ tailWord_3239399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239399).length < 2 ^ (prefixWord ++ tailWord_3239399).sum := by decide
  have hdescent : baseEnd_3239399 < baseStart_3239399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239410 : List Nat := [3, 2, 1, 4, 1, 3, 2, 2, 5]
def baseStart_3239410 : Nat := 118140960795 + 3239410 * 2 ^ 59
def prefixEnd_3239410 : Nat := 4983230072969 + 3 ^ 40 * 3239410 * 2
def baseEnd_3239410 : Nat := 184819374109030669686359

theorem tailTrace_3239410 : CollatzResearch.WordTrace tailWord_3239410 prefixEnd_3239410 184819374109030669686359 := by
  unfold tailWord_3239410
  simp only [CollatzResearch.WordTrace]
  refine ⟨29537747298544573006712921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78767326129452194684567789 29537747298544573006712921)
  ·
    refine ⟨22153310473908429755034691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29537747298544573006712921 22153310473908429755034691)
    ·
      refine ⟨33229965710862644632552037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22153310473908429755034691 33229965710862644632552037)
      ·
        refine ⟨6230618570786745868603507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33229965710862644632552037 6230618570786745868603507)
        ·
          refine ⟨9345927856180118802905261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6230618570786745868603507 9345927856180118802905261)
          ·
            refine ⟨3504722946067544551089473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9345927856180118802905261 3504722946067544551089473)
            ·
              refine ⟨2628542209550658413317105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3504722946067544551089473 2628542209550658413317105)
              ·
                refine ⟨1971406657162993809987829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2628542209550658413317105 1971406657162993809987829)
                ·
                  refine ⟨184819374109030669686359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1971406657162993809987829 184819374109030669686359)
                  ·
                    rfl

theorem cell23_3239410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 2, 5].length) (baseStart_3239410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239410 prefixEnd_3239410 := by exact prefixLift 3239410
  have htrace : WordTrace (prefixWord ++ tailWord_3239410) baseStart_3239410 baseEnd_3239410 := by
    simpa [prefixWord, tailWord_3239410, baseEnd_3239410] using wordTrace_append hprefix tailTrace_3239410
  have hstable : (prefixWord ++ tailWord_3239410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239410).length < 2 ^ (prefixWord ++ tailWord_3239410).sum := by decide
  have hdescent : baseEnd_3239410 < baseStart_3239410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239413 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 2, 5, 2]
def baseStart_3239413 : Nat := 118140960795 + 3239413 * 2 ^ 59
def prefixEnd_3239413 : Nat := 4983230072969 + 3 ^ 40 * 3239413 * 2
def baseEnd_3239413 : Nat := 1663375907423239515439717

theorem tailTrace_3239413 : CollatzResearch.WordTrace tailWord_3239413 prefixEnd_3239413 1663375907423239515439717 := by
  unfold tailWord_3239413
  simp only [CollatzResearch.WordTrace]
  refine ⟨118151098613167423539210893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78767399075444949026140595 118151098613167423539210893)
  ·
    refine ⟨44306661979937783827204085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118151098613167423539210893 44306661979937783827204085)
    ·
      refine ⟨4153749560619167233800383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44306661979937783827204085 4153749560619167233800383)
      ·
        refine ⟨6230624340928750850700575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4153749560619167233800383 6230624340928750850700575)
        ·
          refine ⟨9345936511393126276050863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6230624340928750850700575 9345936511393126276050863)
          ·
            refine ⟨14018904767089689414076295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9345936511393126276050863 14018904767089689414076295)
            ·
              refine ⟨21028357150634534121114443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14018904767089689414076295 21028357150634534121114443)
              ·
                refine ⟨31542535725951801181671665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21028357150634534121114443 31542535725951801181671665)
                ·
                  refine ⟨23656901794463850886253749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31542535725951801181671665 23656901794463850886253749)
                  ·
                    refine ⟨2217834543230986020586289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23656901794463850886253749 2217834543230986020586289)
                    ·
                      refine ⟨1663375907423239515439717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2217834543230986020586289 1663375907423239515439717)
                      ·
                        rfl

theorem cell23_3239413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_3239413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239413 prefixEnd_3239413 := by exact prefixLift 3239413
  have htrace : WordTrace (prefixWord ++ tailWord_3239413) baseStart_3239413 baseEnd_3239413 := by
    simpa [prefixWord, tailWord_3239413, baseEnd_3239413] using wordTrace_append hprefix tailTrace_3239413
  have hstable : (prefixWord ++ tailWord_3239413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239413).length < 2 ^ (prefixWord ++ tailWord_3239413).sum := by decide
  have hdescent : baseEnd_3239413 < baseStart_3239413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239429 : List Nat := [1, 3, 1, 1, 2, 2, 1, 4, 1, 4, 3]
def baseStart_3239429 : Nat := 118140960795 + 3239429 * 2 ^ 59
def prefixEnd_3239429 : Nat := 4983230072969 + 3 ^ 40 * 3239429 * 2
def baseEnd_3239429 : Nat := 1663384123113711452839643

theorem tailTrace_3239429 : CollatzResearch.WordTrace tailWord_3239429 prefixEnd_3239429 1663384123113711452839643 := by
  unfold tailWord_3239429
  simp only [CollatzResearch.WordTrace]
  refine ⟨118151682181109458271793341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78767788120739638847862227 118151682181109458271793341)
  ·
    refine ⟨44306880817916046851922503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118151682181109458271793341 44306880817916046851922503)
    ·
      refine ⟨66460321226874070277883755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44306880817916046851922503 66460321226874070277883755)
      ·
        refine ⟨99690481840311105416825633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66460321226874070277883755 99690481840311105416825633)
        ·
          refine ⟨74767861380233329062619225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99690481840311105416825633 74767861380233329062619225)
          ·
            refine ⟨56075896035174996796964419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74767861380233329062619225 56075896035174996796964419)
            ·
              refine ⟨84113844052762495195446629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56075896035174996796964419 84113844052762495195446629)
              ·
                refine ⟨15771345759892967849146243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84113844052762495195446629 15771345759892967849146243)
                ·
                  refine ⟨23657018639839451773719365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15771345759892967849146243 23657018639839451773719365)
                  ·
                    refine ⟨4435690994969897207572381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23657018639839451773719365 4435690994969897207572381)
                    ·
                      refine ⟨1663384123113711452839643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4435690994969897207572381 1663384123113711452839643)
                      ·
                        rfl

theorem cell23_3239429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 4, 3].length) (baseStart_3239429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239429 prefixEnd_3239429 := by exact prefixLift 3239429
  have htrace : WordTrace (prefixWord ++ tailWord_3239429) baseStart_3239429 baseEnd_3239429 := by
    simpa [prefixWord, tailWord_3239429, baseEnd_3239429] using wordTrace_append hprefix tailTrace_3239429
  have hstable : (prefixWord ++ tailWord_3239429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239429).length < 2 ^ (prefixWord ++ tailWord_3239429).sum := by decide
  have hdescent : baseEnd_3239429 < baseStart_3239429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239470 : List Nat := [4, 1, 3, 1, 2, 1, 2, 4, 1, 4]
def baseStart_3239470 : Nat := 118140960795 + 3239470 * 2 ^ 59
def prefixEnd_3239470 : Nat := 4983230072969 + 3 ^ 40 * 3239470 * 2
def baseEnd_3239470 : Nat := 554468391940181930808985

theorem tailTrace_3239470 : CollatzResearch.WordTrace tailWord_3239470 prefixEnd_3239470 554468391940181930808985 := by
  unfold tailWord_3239470
  simp only [CollatzResearch.WordTrace]
  refine ⟨14769147196745115284254483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78768785049307281516023909 14769147196745115284254483)
  ·
    refine ⟨22153720795117672926381725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14769147196745115284254483 22153720795117672926381725)
    ·
      refine ⟨8307645298169127347393147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22153720795117672926381725 8307645298169127347393147)
      ·
        refine ⟨12461467947253691021089721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8307645298169127347393147 12461467947253691021089721)
        ·
          refine ⟨9346100960440268265817291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12461467947253691021089721 9346100960440268265817291)
          ·
            refine ⟨14019151440660402398725937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9346100960440268265817291 14019151440660402398725937)
            ·
              refine ⟨10514363580495301799044453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14019151440660402398725937 10514363580495301799044453)
              ·
                refine ⟨1971443171342869087320835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10514363580495301799044453 1971443171342869087320835)
                ·
                  refine ⟨2957164757014303630981253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1971443171342869087320835 2957164757014303630981253)
                  ·
                    refine ⟨554468391940181930808985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2957164757014303630981253 554468391940181930808985)
                    ·
                      rfl

theorem cell23_3239470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_3239470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239470 prefixEnd_3239470 := by exact prefixLift 3239470
  have htrace : WordTrace (prefixWord ++ tailWord_3239470) baseStart_3239470 baseEnd_3239470 := by
    simpa [prefixWord, tailWord_3239470, baseEnd_3239470] using wordTrace_append hprefix tailTrace_3239470
  have hstable : (prefixWord ++ tailWord_3239470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239470).length < 2 ^ (prefixWord ++ tailWord_3239470).sum := by decide
  have hdescent : baseEnd_3239470 < baseStart_3239470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239509 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 3, 6]
def baseStart_3239509 : Nat := 118140960795 + 3239509 * 2 ^ 59
def prefixEnd_3239509 : Nat := 4983230072969 + 3 ^ 40 * 3239509 * 2
def baseEnd_3239509 : Nat := 554475067188690379946425

theorem tailTrace_3239509 : CollatzResearch.WordTrace tailWord_3239509 prefixEnd_3239509 554475067188690379946425 := by
  unfold tailWord_3239509
  simp only [CollatzResearch.WordTrace]
  refine ⟨118154600020819631934705581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78769733347213087956470387 118154600020819631934705581)
  ·
    refine ⟨44307975007807361975514593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118154600020819631934705581 44307975007807361975514593)
    ·
      refine ⟨33230981255855521481635945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44307975007807361975514593 33230981255855521481635945)
      ·
        refine ⟨24923235941891641111226959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33230981255855521481635945 24923235941891641111226959)
        ·
          refine ⟨37384853912837461666840439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24923235941891641111226959 37384853912837461666840439)
          ·
            refine ⟨56077280869256192500260659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37384853912837461666840439 56077280869256192500260659)
            ·
              refine ⟨84115921303884288750390989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56077280869256192500260659 84115921303884288750390989)
              ·
                refine ⟨31543470488956608281396621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84115921303884288750390989 31543470488956608281396621)
                ·
                  refine ⟨11828801433358728105523733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31543470488956608281396621 11828801433358728105523733)
                  ·
                    refine ⟨554475067188690379946425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11828801433358728105523733 554475067188690379946425)
                    ·
                      rfl

theorem cell23_3239509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_3239509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239509 prefixEnd_3239509 := by exact prefixLift 3239509
  have htrace : WordTrace (prefixWord ++ tailWord_3239509) baseStart_3239509 baseEnd_3239509 := by
    simpa [prefixWord, tailWord_3239509, baseEnd_3239509] using wordTrace_append hprefix tailTrace_3239509
  have hstable : (prefixWord ++ tailWord_3239509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239509).length < 2 ^ (prefixWord ++ tailWord_3239509).sum := by decide
  have hdescent : baseEnd_3239509 < baseStart_3239509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239529 : List Nat := [1, 2, 1, 1, 1, 4, 3, 2, 1, 1, 6]
def baseStart_3239529 : Nat := 118140960795 + 3239529 * 2 ^ 59
def prefixEnd_3239529 : Nat := 4983230072969 + 3 ^ 40 * 3239529 * 2
def baseEnd_3239529 : Nat := 1663435471179161061589183

theorem tailTrace_3239529 : CollatzResearch.WordTrace tailWord_3239529 prefixEnd_3239529 1663435471179161061589183 := by
  unfold tailWord_3239529
  simp only [CollatzResearch.WordTrace]
  refine ⟨118155329480747175350433641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78770219653831450233622427 118155329480747175350433641)
  ·
    refine ⟨88616497110560381512825231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118155329480747175350433641 88616497110560381512825231)
    ·
      refine ⟨132924745665840572269237847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88616497110560381512825231 132924745665840572269237847)
      ·
        refine ⟨199387118498760858403856771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132924745665840572269237847 199387118498760858403856771)
        ·
          refine ⟨299080677748141287605785157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199387118498760858403856771 299080677748141287605785157)
          ·
            refine ⟨56077627077776491426084717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 299080677748141287605785157 56077627077776491426084717)
            ·
              refine ⟨21029110154166184284781769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56077627077776491426084717 21029110154166184284781769)
              ·
                refine ⟨15771832615624638213586327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21029110154166184284781769 15771832615624638213586327)
                ·
                  refine ⟨23657748923436957320379491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15771832615624638213586327 23657748923436957320379491)
                  ·
                    refine ⟨35486623385155435980569237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23657748923436957320379491 35486623385155435980569237)
                    ·
                      refine ⟨1663435471179161061589183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35486623385155435980569237 1663435471179161061589183)
                      ·
                        rfl

theorem cell23_3239529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 1, 6].length) (baseStart_3239529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239529 prefixEnd_3239529 := by exact prefixLift 3239529
  have htrace : WordTrace (prefixWord ++ tailWord_3239529) baseStart_3239529 baseEnd_3239529 := by
    simpa [prefixWord, tailWord_3239529, baseEnd_3239529] using wordTrace_append hprefix tailTrace_3239529
  have hstable : (prefixWord ++ tailWord_3239529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239529).length < 2 ^ (prefixWord ++ tailWord_3239529).sum := by decide
  have hdescent : baseEnd_3239529 < baseStart_3239529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239536 : List Nat := [2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 5]
def baseStart_3239536 : Nat := 118140960795 + 3239536 * 2 ^ 59
def prefixEnd_3239536 : Nat := 4983230072969 + 3 ^ 40 * 3239536 * 2
def baseEnd_3239536 : Nat := 1663439065543742534201651

theorem tailTrace_3239536 : CollatzResearch.WordTrace tailWord_3239536 prefixEnd_3239536 1663439065543742534201651 := by
  unfold tailWord_3239536
  simp only [CollatzResearch.WordTrace]
  refine ⟨59077792395860907772969231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78770389861147877030625641 59077792395860907772969231)
  ·
    refine ⟨88616688593791361659453847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59077792395860907772969231 88616688593791361659453847)
    ·
      refine ⟨132925032890687042489180771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88616688593791361659453847 132925032890687042489180771)
      ·
        refine ⟨199387549336030563733771157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132925032890687042489180771 199387549336030563733771157)
        ·
          refine ⟨9346291375126432675020523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 199387549336030563733771157 9346291375126432675020523)
          ·
            refine ⟨14019437062689649012530785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9346291375126432675020523 14019437062689649012530785)
            ·
              refine ⟨10514577797017236759398089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14019437062689649012530785 10514577797017236759398089)
              ·
                refine ⟨7885933347762927569548567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10514577797017236759398089 7885933347762927569548567)
                ·
                  refine ⟨11828900021644391354322851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7885933347762927569548567 11828900021644391354322851)
                  ·
                    refine ⟨17743350032466587031484277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11828900021644391354322851 17743350032466587031484277)
                    ·
                      refine ⟨1663439065543742534201651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17743350032466587031484277 1663439065543742534201651)
                      ·
                        rfl

theorem cell23_3239536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 5].length) (baseStart_3239536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239536 prefixEnd_3239536 := by exact prefixLift 3239536
  have htrace : WordTrace (prefixWord ++ tailWord_3239536) baseStart_3239536 baseEnd_3239536 := by
    simpa [prefixWord, tailWord_3239536, baseEnd_3239536] using wordTrace_append hprefix tailTrace_3239536
  have hstable : (prefixWord ++ tailWord_3239536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239536).length < 2 ^ (prefixWord ++ tailWord_3239536).sum := by decide
  have hdescent : baseEnd_3239536 < baseStart_3239536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239553 : List Nat := [1, 2, 4, 2, 1, 3, 1, 1, 3, 2, 3]
def baseStart_3239553 : Nat := 118140960795 + 3239553 * 2 ^ 59
def prefixEnd_3239553 : Nat := 4983230072969 + 3 ^ 40 * 3239553 * 2
def baseEnd_3239553 : Nat := 1663447794714868967689073

theorem tailTrace_3239553 : CollatzResearch.WordTrace tailWord_3239553 prefixEnd_3239553 1663447794714868967689073 := by
  unfold tailWord_3239553
  simp only [CollatzResearch.WordTrace]
  refine ⟨118156204832660227449307313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78770803221773484966204875 118156204832660227449307313)
  ·
    refine ⟨88617153624495170586980485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118156204832660227449307313 88617153624495170586980485)
    ·
      refine ⟨16615716304592844485058841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88617153624495170586980485 16615716304592844485058841)
      ·
        refine ⟨12461787228444633363794131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16615716304592844485058841 12461787228444633363794131)
        ·
          refine ⟨18692680842666950045691197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12461787228444633363794131 18692680842666950045691197)
          ·
            refine ⟨7009755316000106267134199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18692680842666950045691197 7009755316000106267134199)
            ·
              refine ⟨10514632974000159400701299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7009755316000106267134199 10514632974000159400701299)
              ·
                refine ⟨15771949461000239101051949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10514632974000159400701299 15771949461000239101051949)
                ·
                  refine ⟨5914481047875089662894481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15771949461000239101051949 5914481047875089662894481)
                  ·
                    refine ⟨4435860785906317247170861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5914481047875089662894481 4435860785906317247170861)
                    ·
                      refine ⟨1663447794714868967689073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4435860785906317247170861 1663447794714868967689073)
                      ·
                        rfl

theorem cell23_3239553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_3239553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239553 prefixEnd_3239553 := by exact prefixLift 3239553
  have htrace : WordTrace (prefixWord ++ tailWord_3239553) baseStart_3239553 baseEnd_3239553 := by
    simpa [prefixWord, tailWord_3239553, baseEnd_3239553] using wordTrace_append hprefix tailTrace_3239553
  have hstable : (prefixWord ++ tailWord_3239553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239553).length < 2 ^ (prefixWord ++ tailWord_3239553).sum := by decide
  have hdescent : baseEnd_3239553 < baseStart_3239553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239570 : List Nat := [3, 2, 3, 1, 3, 2, 1, 1, 1, 1, 5]
def baseStart_3239570 : Nat := 118140960795 + 3239570 * 2 ^ 59
def prefixEnd_3239570 : Nat := 4983230072969 + 3 ^ 40 * 3239570 * 2
def baseEnd_3239570 : Nat := 1663456523885995401176495

theorem tailTrace_3239570 : CollatzResearch.WordTrace tailWord_3239570 prefixEnd_3239570 1663456523885995401176495 := by
  unfold tailWord_3239570
  simp only [CollatzResearch.WordTrace]
  refine ⟨29539206218399659838169041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78771216582399092901784109 29539206218399659838169041)
  ·
    refine ⟨22154404663799744878626781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29539206218399659838169041 22154404663799744878626781)
    ·
      refine ⟨8307901748924904329485043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22154404663799744878626781 8307901748924904329485043)
      ·
        refine ⟨12461852623387356494227565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8307901748924904329485043 12461852623387356494227565)
        ·
          refine ⟨4673194733770258685335337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12461852623387356494227565 4673194733770258685335337)
          ·
            refine ⟨3504896050327694014001503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4673194733770258685335337 3504896050327694014001503)
            ·
              refine ⟨5257344075491541021002255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3504896050327694014001503 5257344075491541021002255)
              ·
                refine ⟨7886016113237311531503383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5257344075491541021002255 7886016113237311531503383)
                ·
                  refine ⟨11829024169855967297255075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7886016113237311531503383 11829024169855967297255075)
                  ·
                    refine ⟨17743536254783950945882613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11829024169855967297255075 17743536254783950945882613)
                    ·
                      refine ⟨1663456523885995401176495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17743536254783950945882613 1663456523885995401176495)
                      ·
                        rfl

theorem cell23_3239570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_3239570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239570 prefixEnd_3239570 := by exact prefixLift 3239570
  have htrace : WordTrace (prefixWord ++ tailWord_3239570) baseStart_3239570 baseEnd_3239570 := by
    simpa [prefixWord, tailWord_3239570, baseEnd_3239570] using wordTrace_append hprefix tailTrace_3239570
  have hstable : (prefixWord ++ tailWord_3239570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239570).length < 2 ^ (prefixWord ++ tailWord_3239570).sum := by decide
  have hdescent : baseEnd_3239570 < baseStart_3239570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239584 : List Nat := [2, 1, 1, 4, 3, 1, 4, 2, 1, 2, 2]
def baseStart_3239584 : Nat := 118140960795 + 3239584 * 2 ^ 59
def prefixEnd_3239584 : Nat := 4983230072969 + 3 ^ 40 * 3239584 * 2
def baseEnd_3239584 : Nat := 1663463712615158346401431

theorem tailTrace_3239584 : CollatzResearch.WordTrace tailWord_3239584 prefixEnd_3239584 1663463712615158346401431 := by
  unfold tailWord_3239584
  simp only [CollatzResearch.WordTrace]
  refine ⟨59078667747773959871842903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78771556997031946495790537 59078667747773959871842903)
  ·
    refine ⟨88618001621660939807764355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59078667747773959871842903 88618001621660939807764355)
    ·
      refine ⟨132927002432491409711646533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88618001621660939807764355 132927002432491409711646533)
      ·
        refine ⟨24923812956092139320933725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132927002432491409711646533 24923812956092139320933725)
        ·
          refine ⟨9346429858534552245350147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24923812956092139320933725 9346429858534552245350147)
          ·
            refine ⟨14019644787801828368025221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9346429858534552245350147 14019644787801828368025221)
            ·
              refine ⟨2628683397712842819004729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14019644787801828368025221 2628683397712842819004729)
              ·
                refine ⟨1971512548284632114253547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2628683397712842819004729 1971512548284632114253547)
                ·
                  refine ⟨2957268822426948171380321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1971512548284632114253547 2957268822426948171380321)
                  ·
                    refine ⟨2217951616820211128535241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2957268822426948171380321 2217951616820211128535241)
                    ·
                      refine ⟨1663463712615158346401431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2217951616820211128535241 1663463712615158346401431)
                      ·
                        rfl

theorem cell23_3239584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_3239584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239584 prefixEnd_3239584 := by exact prefixLift 3239584
  have htrace : WordTrace (prefixWord ++ tailWord_3239584) baseStart_3239584 baseEnd_3239584 := by
    simpa [prefixWord, tailWord_3239584, baseEnd_3239584] using wordTrace_append hprefix tailTrace_3239584
  have hstable : (prefixWord ++ tailWord_3239584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239584).length < 2 ^ (prefixWord ++ tailWord_3239584).sum := by decide
  have hdescent : baseEnd_3239584 < baseStart_3239584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239618 : List Nat := [3, 5, 1, 2, 2, 1, 2, 1, 1, 1, 4]
def baseStart_3239618 : Nat := 118140960795 + 3239618 * 2 ^ 59
def prefixEnd_3239618 : Nat := 4983230072969 + 3 ^ 40 * 3239618 * 2
def baseEnd_3239618 : Nat := 1663481170957411213376275

theorem tailTrace_3239618 : CollatzResearch.WordTrace tailWord_3239618 prefixEnd_3239618 1663481170957411213376275 := by
  unfold tailWord_3239618
  simp only [CollatzResearch.WordTrace]
  refine ⟨29539643894356185887605877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78772383718283162366949005 29539643894356185887605877)
  ·
    refine ⟨2769341615095892426963051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29539643894356185887605877 2769341615095892426963051)
    ·
      refine ⟨4154012422643838640444577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2769341615095892426963051 4154012422643838640444577)
      ·
        refine ⟨3115509316982878980333433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4154012422643838640444577 3115509316982878980333433)
        ·
          refine ⟨2336631987737159235250075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3115509316982878980333433 2336631987737159235250075)
          ·
            refine ⟨3504947981605738852875113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2336631987737159235250075 3504947981605738852875113)
            ·
              refine ⟨2628710986204304139656335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3504947981605738852875113 2628710986204304139656335)
              ·
                refine ⟨3943066479306456209484503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2628710986204304139656335 3943066479306456209484503)
                ·
                  refine ⟨5914599718959684314226755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3943066479306456209484503 5914599718959684314226755)
                  ·
                    refine ⟨8871899578439526471340133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5914599718959684314226755 8871899578439526471340133)
                    ·
                      refine ⟨1663481170957411213376275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8871899578439526471340133 1663481170957411213376275)
                      ·
                        rfl

theorem cell23_3239618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_3239618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239618 prefixEnd_3239618 := by exact prefixLift 3239618
  have htrace : WordTrace (prefixWord ++ tailWord_3239618) baseStart_3239618 baseEnd_3239618 := by
    simpa [prefixWord, tailWord_3239618, baseEnd_3239618] using wordTrace_append hprefix tailTrace_3239618
  have hstable : (prefixWord ++ tailWord_3239618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239618).length < 2 ^ (prefixWord ++ tailWord_3239618).sum := by decide
  have hdescent : baseEnd_3239618 < baseStart_3239618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239623 : List Nat := [1, 1, 4, 1, 1, 1, 3, 4, 1, 4, 2]
def baseStart_3239623 : Nat := 118140960795 + 3239623 * 2 ^ 59
def prefixEnd_3239623 : Nat := 4983230072969 + 3 ^ 40 * 3239623 * 2
def baseEnd_3239623 : Nat := 1663483738360683693813751

theorem tailTrace_3239623 : CollatzResearch.WordTrace tailWord_3239623 prefixEnd_3239623 1663483738360683693813751 := by
  unfold tailWord_3239623
  simp only [CollatzResearch.WordTrace]
  refine ⟨118158757942406629404355523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78772505294937752936237015 118158757942406629404355523)
  ·
    refine ⟨177238136913609944106533285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118158757942406629404355523 177238136913609944106533285)
    ·
      refine ⟨33232150671301864519974991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177238136913609944106533285 33232150671301864519974991)
      ·
        refine ⟨49848226006952796779962487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33232150671301864519974991 49848226006952796779962487)
        ·
          refine ⟨74772339010429195169943731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49848226006952796779962487 74772339010429195169943731)
          ·
            refine ⟨112158508515643792754915597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74772339010429195169943731 112158508515643792754915597)
            ·
              refine ⟨42059440693366422283093349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112158508515643792754915597 42059440693366422283093349)
              ·
                refine ⟨7886145130006204178080003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42059440693366422283093349 7886145130006204178080003)
                ·
                  refine ⟨11829217695009306267120005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7886145130006204178080003 11829217695009306267120005)
                  ·
                    refine ⟨2217978317814244925085001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11829217695009306267120005 2217978317814244925085001)
                    ·
                      refine ⟨1663483738360683693813751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2217978317814244925085001 1663483738360683693813751)
                      ·
                        rfl

theorem cell23_3239623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 4, 2].length) (baseStart_3239623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239623 prefixEnd_3239623 := by exact prefixLift 3239623
  have htrace : WordTrace (prefixWord ++ tailWord_3239623) baseStart_3239623 baseEnd_3239623 := by
    simpa [prefixWord, tailWord_3239623, baseEnd_3239623] using wordTrace_append hprefix tailTrace_3239623
  have hstable : (prefixWord ++ tailWord_3239623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239623).length < 2 ^ (prefixWord ++ tailWord_3239623).sum := by decide
  have hdescent : baseEnd_3239623 < baseStart_3239623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239640 : List Nat := [2, 1, 2, 2, 3, 1, 3, 1, 4, 2, 2]
def baseStart_3239640 : Nat := 118140960795 + 3239640 * 2 ^ 59
def prefixEnd_3239640 : Nat := 4983230072969 + 3 ^ 40 * 3239640 * 2
def baseEnd_3239640 : Nat := 1663492467531810127301173

theorem tailTrace_3239640 : CollatzResearch.WordTrace tailWord_3239640 prefixEnd_3239640 1663492467531810127301173 := by
  unfold tailWord_3239640
  simp only [CollatzResearch.WordTrace]
  refine ⟨59079688991672520653862187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78772918655563360871816249 59079688991672520653862187)
  ·
    refine ⟨88619533487508780980793281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59079688991672520653862187 88619533487508780980793281)
    ·
      refine ⟨66464650115631585735594961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88619533487508780980793281 66464650115631585735594961)
      ·
        refine ⟨49848487586723689301696221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66464650115631585735594961 49848487586723689301696221)
        ·
          refine ⟨18693182845021383488136083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49848487586723689301696221 18693182845021383488136083)
          ·
            refine ⟨28039774267532075232204125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18693182845021383488136083 28039774267532075232204125)
            ·
              refine ⟨10514915350324528212076547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28039774267532075232204125 10514915350324528212076547)
              ·
                refine ⟨15772373025486792318114821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10514915350324528212076547 15772373025486792318114821)
                ·
                  refine ⟨2957319942278773559646529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15772373025486792318114821 2957319942278773559646529)
                  ·
                    refine ⟨2217989956709080169734897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2957319942278773559646529 2217989956709080169734897)
                    ·
                      refine ⟨1663492467531810127301173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2217989956709080169734897 1663492467531810127301173)
                      ·
                        rfl

theorem cell23_3239640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 4, 2, 2].length) (baseStart_3239640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239640 prefixEnd_3239640 := by exact prefixLift 3239640
  have htrace : WordTrace (prefixWord ++ tailWord_3239640) baseStart_3239640 baseEnd_3239640 := by
    simpa [prefixWord, tailWord_3239640, baseEnd_3239640] using wordTrace_append hprefix tailTrace_3239640
  have hstable : (prefixWord ++ tailWord_3239640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239640).length < 2 ^ (prefixWord ++ tailWord_3239640).sum := by decide
  have hdescent : baseEnd_3239640 < baseStart_3239640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239676 : List Nat := [2, 2, 2, 1, 3, 1, 1, 3, 1, 7]
def baseStart_3239676 : Nat := 118140960795 + 3239676 * 2 ^ 59
def prefixEnd_3239676 : Nat := 4983230072969 + 3 ^ 40 * 3239676 * 2
def baseEnd_3239676 : Nat := 554503650945123995483669

theorem tailTrace_3239676 : CollatzResearch.WordTrace tailWord_3239676 prefixEnd_3239676 554503650945123995483669 := by
  unfold tailWord_3239676
  simp only [CollatzResearch.WordTrace]
  refine ⟨59080345505607309728017441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78773794007476412970689921 59080345505607309728017441)
  ·
    refine ⟨44310259129205482296013081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59080345505607309728017441 44310259129205482296013081)
    ·
      refine ⟨33232694346904111722009811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44310259129205482296013081 33232694346904111722009811)
      ·
        refine ⟨49849041520356167583014717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33232694346904111722009811 49849041520356167583014717)
        ·
          refine ⟨18693390570133562843630519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49849041520356167583014717 18693390570133562843630519)
          ·
            refine ⟨28040085855200344265445779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18693390570133562843630519 28040085855200344265445779)
            ·
              refine ⟨42060128782800516398168669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28040085855200344265445779 42060128782800516398168669)
              ·
                refine ⟨15772548293550193649313251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42060128782800516398168669 15772548293550193649313251)
                ·
                  refine ⟨23658822440325290473969877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15772548293550193649313251 23658822440325290473969877)
                  ·
                    refine ⟨554503650945123995483669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23658822440325290473969877 554503650945123995483669)
                    ·
                      rfl

theorem cell23_3239676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_3239676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239676 prefixEnd_3239676 := by exact prefixLift 3239676
  have htrace : WordTrace (prefixWord ++ tailWord_3239676) baseStart_3239676 baseEnd_3239676 := by
    simpa [prefixWord, tailWord_3239676, baseEnd_3239676] using wordTrace_append hprefix tailTrace_3239676
  have hstable : (prefixWord ++ tailWord_3239676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239676).length < 2 ^ (prefixWord ++ tailWord_3239676).sum := by decide
  have hdescent : baseEnd_3239676 < baseStart_3239676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239703 : List Nat := [1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 5]
def baseStart_3239703 : Nat := 118140960795 + 3239703 * 2 ^ 59
def prefixEnd_3239703 : Nat := 4983230072969 + 3 ^ 40 * 3239703 * 2
def baseEnd_3239703 : Nat := 1663524816813043380813383

theorem tailTrace_3239703 : CollatzResearch.WordTrace tailWord_3239703 prefixEnd_3239703 1663524816813043380813383 := by
  unfold tailWord_3239703
  simp only [CollatzResearch.WordTrace]
  refine ⟨118161675782116803067267763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78774450521411202044845175 118161675782116803067267763)
  ·
    refine ⟨177242513673175204600901645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118161675782116803067267763 177242513673175204600901645)
    ·
      refine ⟨66465942627440701725338117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177242513673175204600901645 66465942627440701725338117)
      ·
        refine ⟨12462364242645131573500897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66465942627440701725338117 12462364242645131573500897)
        ·
          refine ⟨9346773181983848680125673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12462364242645131573500897 9346773181983848680125673)
          ·
            refine ⟨7010079886487886510094255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9346773181983848680125673 7010079886487886510094255)
            ·
              refine ⟨10515119829731829765141383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7010079886487886510094255 10515119829731829765141383)
              ·
                refine ⟨15772679744597744647712075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10515119829731829765141383 15772679744597744647712075)
                ·
                  refine ⟨23659019616896616971568113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15772679744597744647712075 23659019616896616971568113)
                  ·
                    refine ⟨17744264712672462728676085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23659019616896616971568113 17744264712672462728676085)
                    ·
                      refine ⟨1663524816813043380813383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17744264712672462728676085 1663524816813043380813383)
                      ·
                        rfl

theorem cell23_3239703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_3239703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239703 prefixEnd_3239703 := by exact prefixLift 3239703
  have htrace : WordTrace (prefixWord ++ tailWord_3239703) baseStart_3239703 baseEnd_3239703 := by
    simpa [prefixWord, tailWord_3239703, baseEnd_3239703] using wordTrace_append hprefix tailTrace_3239703
  have hstable : (prefixWord ++ tailWord_3239703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239703).length < 2 ^ (prefixWord ++ tailWord_3239703).sum := by decide
  have hdescent : baseEnd_3239703 < baseStart_3239703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239730 : List Nat := [3, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4]
def baseStart_3239730 : Nat := 118140960795 + 3239730 * 2 ^ 59
def prefixEnd_3239730 : Nat := 4983230072969 + 3 ^ 40 * 3239730 * 2
def baseEnd_3239730 : Nat := 1663538680790714775175759

theorem tailTrace_3239730 : CollatzResearch.WordTrace tailWord_3239730 prefixEnd_3239730 1663538680790714775175759 := by
  unfold tailWord_3239730
  simp only [CollatzResearch.WordTrace]
  refine ⟨29540665138254746669625161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78775107035345991119000429 29540665138254746669625161)
  ·
    refine ⟨22155498853691060002218871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29540665138254746669625161 22155498853691060002218871)
    ·
      refine ⟨33233248280536590003328307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22155498853691060002218871 33233248280536590003328307)
      ·
        refine ⟨49849872420804885004992461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33233248280536590003328307 49849872420804885004992461)
        ·
          refine ⟨18693702157801831876872173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49849872420804885004992461 18693702157801831876872173)
          ·
            refine ⟨7010138309175686953827065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18693702157801831876872173 7010138309175686953827065)
            ·
              refine ⟨5257603731881765215370299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7010138309175686953827065 5257603731881765215370299)
              ·
                refine ⟨7886405597822647823055449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5257603731881765215370299 7886405597822647823055449)
                ·
                  refine ⟨5914804198366985867291587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7886405597822647823055449 5914804198366985867291587)
                  ·
                    refine ⟨8872206297550478800937381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5914804198366985867291587 8872206297550478800937381)
                    ·
                      refine ⟨1663538680790714775175759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8872206297550478800937381 1663538680790714775175759)
                      ·
                        rfl

theorem cell23_3239730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_3239730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239730 prefixEnd_3239730 := by exact prefixLift 3239730
  have htrace : WordTrace (prefixWord ++ tailWord_3239730) baseStart_3239730 baseEnd_3239730 := by
    simpa [prefixWord, tailWord_3239730, baseEnd_3239730] using wordTrace_append hprefix tailTrace_3239730
  have hstable : (prefixWord ++ tailWord_3239730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239730).length < 2 ^ (prefixWord ++ tailWord_3239730).sum := by decide
  have hdescent : baseEnd_3239730 < baseStart_3239730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239753 : List Nat := [1, 2, 1, 1, 2, 4, 4, 2, 6]
def baseStart_3239753 : Nat := 118140960795 + 3239753 * 2 ^ 59
def prefixEnd_3239753 : Nat := 4983230072969 + 3 ^ 40 * 3239753 * 2
def baseEnd_3239753 : Nat := 184838943427307576132017

theorem tailTrace_3239753 : CollatzResearch.WordTrace tailWord_3239753 prefixEnd_3239753 184838943427307576132017 := by
  unfold tailWord_3239753
  simp only [CollatzResearch.WordTrace]
  refine ⟨118163499431935661606587913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78775666287957107737725275 118163499431935661606587913)
  ·
    refine ⟨88622624573951746204940935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118163499431935661606587913 88622624573951746204940935)
    ·
      refine ⟨132933936860927619307411403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88622624573951746204940935 132933936860927619307411403)
      ·
        refine ⟨199400905291391428961117105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132933936860927619307411403 199400905291391428961117105)
        ·
          refine ⟨149550678968543571720837829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199400905291391428961117105 149550678968543571720837829)
          ·
            refine ⟨28040752306601919697657093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149550678968543571720837829 28040752306601919697657093)
            ·
              refine ⟨5257641057487859943310705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28040752306601919697657093 5257641057487859943310705)
              ·
                refine ⟨3943230793115894957483029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5257641057487859943310705 3943230793115894957483029)
                ·
                  refine ⟨184838943427307576132017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3943230793115894957483029 184838943427307576132017)
                  ·
                    rfl

theorem cell23_3239753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 6].length) (baseStart_3239753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239753 prefixEnd_3239753 := by exact prefixLift 3239753
  have htrace : WordTrace (prefixWord ++ tailWord_3239753) baseStart_3239753 baseEnd_3239753 := by
    simpa [prefixWord, tailWord_3239753, baseEnd_3239753] using wordTrace_append hprefix tailTrace_3239753
  have hstable : (prefixWord ++ tailWord_3239753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239753).length < 2 ^ (prefixWord ++ tailWord_3239753).sum := by decide
  have hdescent : baseEnd_3239753 < baseStart_3239753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239783 : List Nat := [1, 1, 5, 1, 2, 1, 1, 3, 3, 5]
def baseStart_3239783 : Nat := 118140960795 + 3239783 * 2 ^ 59
def prefixEnd_3239783 : Nat := 4983230072969 + 3 ^ 40 * 3239783 * 2
def baseEnd_3239783 : Nat := 554521965088467689271005

theorem tailTrace_3239783 : CollatzResearch.WordTrace tailWord_3239783 prefixEnd_3239783 554521965088467689271005 := by
  unfold tailWord_3239783
  simp only [CollatzResearch.WordTrace]
  refine ⟨118164593621826976730180003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78776395747884651153453335 118164593621826976730180003)
  ·
    refine ⟨177246890432740465095270005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118164593621826976730180003 177246890432740465095270005)
    ·
      refine ⟨16616895978069418602681563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177246890432740465095270005 16616895978069418602681563)
      ·
        refine ⟨24925343967104127904022345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16616895978069418602681563 24925343967104127904022345)
        ·
          refine ⟨18694007975328095928016759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24925343967104127904022345 18694007975328095928016759)
          ·
            refine ⟨28041011962992143892025139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18694007975328095928016759 28041011962992143892025139)
            ·
              refine ⟨42061517944488215838037709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28041011962992143892025139 42061517944488215838037709)
              ·
                refine ⟨15773069229183080939264141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42061517944488215838037709 15773069229183080939264141)
                ·
                  refine ⟨5914900960943655352224053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15773069229183080939264141 5914900960943655352224053)
                  ·
                    refine ⟨554521965088467689271005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5914900960943655352224053 554521965088467689271005)
                    ·
                      rfl

theorem cell23_3239783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_3239783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239783 prefixEnd_3239783 := by exact prefixLift 3239783
  have htrace : WordTrace (prefixWord ++ tailWord_3239783) baseStart_3239783 baseEnd_3239783 := by
    simpa [prefixWord, tailWord_3239783, baseEnd_3239783] using wordTrace_append hprefix tailTrace_3239783
  have hstable : (prefixWord ++ tailWord_3239783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239783).length < 2 ^ (prefixWord ++ tailWord_3239783).sum := by decide
  have hdescent : baseEnd_3239783 < baseStart_3239783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239837 : List Nat := [1, 4, 2, 1, 2, 3, 2, 2, 1, 1, 4]
def baseStart_3239837 : Nat := 118140960795 + 3239837 * 2 ^ 59
def prefixEnd_3239837 : Nat := 4983230072969 + 3 ^ 40 * 3239837 * 2
def baseEnd_3239837 : Nat := 1663593623220745856537767

theorem tailTrace_3239837 : CollatzResearch.WordTrace tailWord_3239837 prefixEnd_3239837 1663593623220745856537767 := by
  unfold tailWord_3239837
  simp only [CollatzResearch.WordTrace]
  refine ⟨118166563163631343952645765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78777708775754229301763843 118166563163631343952645765)
  ·
    refine ⟨22156230593180876991121081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118166563163631343952645765 22156230593180876991121081)
    ·
      refine ⟨16617172944885657743340811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22156230593180876991121081 16617172944885657743340811)
      ·
        refine ⟨24925759417328486615011217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16617172944885657743340811 24925759417328486615011217)
        ·
          refine ⟨18694319562996364961258413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24925759417328486615011217 18694319562996364961258413)
          ·
            refine ⟨7010369836123636860471905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18694319562996364961258413 7010369836123636860471905)
            ·
              refine ⟨5257777377092727645353929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7010369836123636860471905 5257777377092727645353929)
              ·
                refine ⟨3943333032819545734015447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5257777377092727645353929 3943333032819545734015447)
                ·
                  refine ⟨5914999549229318601023171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3943333032819545734015447 5914999549229318601023171)
                  ·
                    refine ⟨8872499323843977901534757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5914999549229318601023171 8872499323843977901534757)
                    ·
                      refine ⟨1663593623220745856537767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8872499323843977901534757 1663593623220745856537767)
                      ·
                        rfl

theorem cell23_3239837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_3239837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239837 prefixEnd_3239837 := by exact prefixLift 3239837
  have htrace : WordTrace (prefixWord ++ tailWord_3239837) baseStart_3239837 baseEnd_3239837 := by
    simpa [prefixWord, tailWord_3239837, baseEnd_3239837] using wordTrace_append hprefix tailTrace_3239837
  have hstable : (prefixWord ++ tailWord_3239837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239837).length < 2 ^ (prefixWord ++ tailWord_3239837).sum := by decide
  have hdescent : baseEnd_3239837 < baseStart_3239837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239857 : List Nat := [1, 2, 2, 4, 2, 1, 2, 3, 1, 2, 3]
def baseStart_3239857 : Nat := 118140960795 + 3239857 * 2 ^ 59
def prefixEnd_3239857 : Nat := 4983230072969 + 3 ^ 40 * 3239857 * 2
def baseEnd_3239857 : Nat := 1663603892833835778287675

theorem tailTrace_3239857 : CollatzResearch.WordTrace tailWord_3239857 prefixEnd_3239857 1663603892833835778287675 := by
  unfold tailWord_3239857
  simp only [CollatzResearch.WordTrace]
  refine ⟨118167292623558887368373825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78778195082372591578915883 118167292623558887368373825)
  ·
    refine ⟨88625469467669165526280369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118167292623558887368373825 88625469467669165526280369)
    ·
      refine ⟨66469102100751874144710277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88625469467669165526280369 66469102100751874144710277)
      ·
        refine ⟨12462956643890976402133177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66469102100751874144710277 12462956643890976402133177)
        ·
          refine ⟨9347217482918232301599883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12462956643890976402133177 9347217482918232301599883)
          ·
            refine ⟨14020826224377348452399825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9347217482918232301599883 14020826224377348452399825)
            ·
              refine ⟨10515619668283011339299869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14020826224377348452399825 10515619668283011339299869)
              ·
                refine ⟨3943357375606129252237451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10515619668283011339299869 3943357375606129252237451)
                ·
                  refine ⟨5915036063409193878356177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3943357375606129252237451 5915036063409193878356177)
                  ·
                    refine ⟨4436277047556895408767133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5915036063409193878356177 4436277047556895408767133)
                    ·
                      refine ⟨1663603892833835778287675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4436277047556895408767133 1663603892833835778287675)
                      ·
                        rfl

theorem cell23_3239857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_3239857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239857 prefixEnd_3239857 := by exact prefixLift 3239857
  have htrace : WordTrace (prefixWord ++ tailWord_3239857) baseStart_3239857 baseEnd_3239857 := by
    simpa [prefixWord, tailWord_3239857, baseEnd_3239857] using wordTrace_append hprefix tailTrace_3239857
  have hstable : (prefixWord ++ tailWord_3239857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239857).length < 2 ^ (prefixWord ++ tailWord_3239857).sum := by decide
  have hdescent : baseEnd_3239857 < baseStart_3239857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239871 : List Nat := [1, 1, 2, 2, 2, 1, 7, 2, 1, 2, 2]
def baseStart_3239871 : Nat := 118140960795 + 3239871 * 2 ^ 59
def prefixEnd_3239871 : Nat := 4983230072969 + 3 ^ 40 * 3239871 * 2
def baseEnd_3239871 : Nat := 1663611081562998723512611

theorem tailTrace_3239871 : CollatzResearch.WordTrace tailWord_3239871 prefixEnd_3239871 1663611081562998723512611 := by
  unfold tailWord_3239871
  simp only [CollatzResearch.WordTrace]
  refine ⟨118167803245508167759383467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78778535497005445172922311 118167803245508167759383467)
  ·
    refine ⟨177251704868262251639075201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118167803245508167759383467 177251704868262251639075201)
    ·
      refine ⟨132938778651196688729306401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177251704868262251639075201 132938778651196688729306401)
      ·
        refine ⟨99704083988397516546979801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132938778651196688729306401 99704083988397516546979801)
        ·
          refine ⟨74778062991298137410234851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99704083988397516546979801 74778062991298137410234851)
          ·
            refine ⟨112167094486947206115352277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74778062991298137410234851 112167094486947206115352277)
            ·
              refine ⟨2628916277037825143328569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 112167094486947206115352277 2628916277037825143328569)
              ·
                refine ⟨1971687207778368857496427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2628916277037825143328569 1971687207778368857496427)
                ·
                  refine ⟨2957530811667553286244641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1971687207778368857496427 2957530811667553286244641)
                  ·
                    refine ⟨2218148108750664964683481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2957530811667553286244641 2218148108750664964683481)
                    ·
                      refine ⟨1663611081562998723512611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2218148108750664964683481 1663611081562998723512611)
                      ·
                        rfl

theorem cell23_3239871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 2, 1, 2, 2].length) (baseStart_3239871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239871 prefixEnd_3239871 := by exact prefixLift 3239871
  have htrace : WordTrace (prefixWord ++ tailWord_3239871) baseStart_3239871 baseEnd_3239871 := by
    simpa [prefixWord, tailWord_3239871, baseEnd_3239871] using wordTrace_append hprefix tailTrace_3239871
  have hstable : (prefixWord ++ tailWord_3239871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239871).length < 2 ^ (prefixWord ++ tailWord_3239871).sum := by decide
  have hdescent : baseEnd_3239871 < baseStart_3239871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239887 : List Nat := [1, 1, 2, 1, 1, 5, 3, 3, 2, 1, 3]
def baseStart_3239887 : Nat := 118140960795 + 3239887 * 2 ^ 59
def prefixEnd_3239887 : Nat := 4983230072969 + 3 ^ 40 * 3239887 * 2
def baseEnd_3239887 : Nat := 1663619297253470660912537

theorem tailTrace_3239887 : CollatzResearch.WordTrace tailWord_3239887 prefixEnd_3239887 1663619297253470660912537 := by
  unfold tailWord_3239887
  simp only [CollatzResearch.WordTrace]
  refine ⟨118168386813450202491965915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78778924542300134994643943 118168386813450202491965915)
  ·
    refine ⟨177252580220175303737948873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118168386813450202491965915 177252580220175303737948873)
    ·
      refine ⟨132939435165131477803461655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177252580220175303737948873 132939435165131477803461655)
      ·
        refine ⟨199409152747697216705192483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132939435165131477803461655 199409152747697216705192483)
        ·
          refine ⟨299113729121545825057788725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199409152747697216705192483 299113729121545825057788725)
          ·
            refine ⟨28041912105144921099167693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 299113729121545825057788725 28041912105144921099167693)
            ·
              refine ⟨10515717039429345412187885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28041912105144921099167693 10515717039429345412187885)
              ·
                refine ⟨3943393889786004529570457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10515717039429345412187885 3943393889786004529570457)
                ·
                  refine ⟨2957545417339503397177843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3943393889786004529570457 2957545417339503397177843)
                  ·
                    refine ⟨4436318126009255095766765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2957545417339503397177843 4436318126009255095766765)
                    ·
                      refine ⟨1663619297253470660912537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4436318126009255095766765 1663619297253470660912537)
                      ·
                        rfl

theorem cell23_3239887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 2, 1, 3].length) (baseStart_3239887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239887 prefixEnd_3239887 := by exact prefixLift 3239887
  have htrace : WordTrace (prefixWord ++ tailWord_3239887) baseStart_3239887 baseEnd_3239887 := by
    simpa [prefixWord, tailWord_3239887, baseEnd_3239887] using wordTrace_append hprefix tailTrace_3239887
  have hstable : (prefixWord ++ tailWord_3239887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239887).length < 2 ^ (prefixWord ++ tailWord_3239887).sum := by decide
  have hdescent : baseEnd_3239887 < baseStart_3239887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239923 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 4]
def baseStart_3239923 : Nat := 118140960795 + 3239923 * 2 ^ 59
def prefixEnd_3239923 : Nat := 4983230072969 + 3 ^ 40 * 3239923 * 2
def baseEnd_3239923 : Nat := 1663637782557032520062371

theorem tailTrace_3239923 : CollatzResearch.WordTrace tailWord_3239923 prefixEnd_3239923 1663637782557032520062371 := by
  unfold tailWord_3239923
  simp only [CollatzResearch.WordTrace]
  refine ⟨118169699841319780640276423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78779799894213187093517615 118169699841319780640276423)
  ·
    refine ⟨177254549761979670960414635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118169699841319780640276423 177254549761979670960414635)
    ·
      refine ⟨265881824642969506440621953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177254549761979670960414635 265881824642969506440621953)
      ·
        refine ⟨199411368482227129830466465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265881824642969506440621953 199411368482227129830466465)
        ·
          refine ⟨149558526361670347372849849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199411368482227129830466465 149558526361670347372849849)
          ·
            refine ⟨112168894771252760529637387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149558526361670347372849849 112168894771252760529637387)
            ·
              refine ⟨168253342156879140794456081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112168894771252760529637387 168253342156879140794456081)
              ·
                refine ⟨126190006617659355595842061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168253342156879140794456081 126190006617659355595842061)
                ·
                  refine ⟨47321252481622258348440773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126190006617659355595842061 47321252481622258348440773)
                  ·
                    refine ⟨8872734840304173440332645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47321252481622258348440773 8872734840304173440332645)
                    ·
                      refine ⟨1663637782557032520062371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8872734840304173440332645 1663637782557032520062371)
                      ·
                        rfl

theorem cell23_3239923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 4].length) (baseStart_3239923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239923 prefixEnd_3239923 := by exact prefixLift 3239923
  have htrace : WordTrace (prefixWord ++ tailWord_3239923) baseStart_3239923 baseEnd_3239923 := by
    simpa [prefixWord, tailWord_3239923, baseEnd_3239923] using wordTrace_append hprefix tailTrace_3239923
  have hstable : (prefixWord ++ tailWord_3239923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239923).length < 2 ^ (prefixWord ++ tailWord_3239923).sum := by decide
  have hdescent : baseEnd_3239923 < baseStart_3239923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239944 : List Nat := [2, 1, 3, 2, 1, 2, 1, 5, 2, 2, 2]
def baseStart_3239944 : Nat := 118140960795 + 3239944 * 2 ^ 59
def prefixEnd_3239944 : Nat := 4983230072969 + 3 ^ 40 * 3239944 * 2
def baseEnd_3239944 : Nat := 1663648565650776937899775

theorem tailTrace_3239944 : CollatzResearch.WordTrace tailWord_3239944 prefixEnd_3239944 1663648565650776937899775 := by
  unfold tailWord_3239944
  simp only [CollatzResearch.WordTrace]
  refine ⟨59085232887121850613395443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78780310516162467484527257 59085232887121850613395443)
  ·
    refine ⟨88627849330682775920093165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59085232887121850613395443 88627849330682775920093165)
    ·
      refine ⟨33235443499006040970034937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88627849330682775920093165 33235443499006040970034937)
      ·
        refine ⟨24926582624254530727526203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33235443499006040970034937 24926582624254530727526203)
        ·
          refine ⟨37389873936381796091289305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24926582624254530727526203 37389873936381796091289305)
          ·
            refine ⟨28042405452286347068466979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37389873936381796091289305 28042405452286347068466979)
            ·
              refine ⟨42063608178429520602700469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28042405452286347068466979 42063608178429520602700469)
              ·
                refine ⟨3943463266727767556503169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42063608178429520602700469 3943463266727767556503169)
                ·
                  refine ⟨2957597450045825667377377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3943463266727767556503169 2957597450045825667377377)
                  ·
                    refine ⟨2218198087534369250533033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2957597450045825667377377 2218198087534369250533033)
                    ·
                      refine ⟨1663648565650776937899775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2218198087534369250533033 1663648565650776937899775)
                      ·
                        rfl

theorem cell23_3239944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_3239944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239944 prefixEnd_3239944 := by exact prefixLift 3239944
  have htrace : WordTrace (prefixWord ++ tailWord_3239944) baseStart_3239944 baseEnd_3239944 := by
    simpa [prefixWord, tailWord_3239944, baseEnd_3239944] using wordTrace_append hprefix tailTrace_3239944
  have hstable : (prefixWord ++ tailWord_3239944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239944).length < 2 ^ (prefixWord ++ tailWord_3239944).sum := by decide
  have hdescent : baseEnd_3239944 < baseStart_3239944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239950 : List Nat := [4, 1, 1, 2, 2, 1, 3, 2, 7]
def baseStart_3239950 : Nat := 118140960795 + 3239950 * 2 ^ 59
def prefixEnd_3239950 : Nat := 4983230072969 + 3 ^ 40 * 3239950 * 2
def baseEnd_3239950 : Nat := 184850182948300434936083

theorem tailTrace_3239950 : CollatzResearch.WordTrace tailWord_3239950 prefixEnd_3239950 184850182948300434936083 := by
  unfold tailWord_3239950
  simp only [CollatzResearch.WordTrace]
  refine ⟨14771335576527745531438663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78780456408147976167672869 14771335576527745531438663)
  ·
    refine ⟨22157003364791618297157995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14771335576527745531438663 22157003364791618297157995)
    ·
      refine ⟨33235505047187427445736993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22157003364791618297157995 33235505047187427445736993)
      ·
        refine ⟨24926628785390570584302745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33235505047187427445736993 24926628785390570584302745)
        ·
          refine ⟨18694971589042927938227059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24926628785390570584302745 18694971589042927938227059)
          ·
            refine ⟨28042457383564391907340589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18694971589042927938227059 28042457383564391907340589)
            ·
              refine ⟨10515921518836646965252721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28042457383564391907340589 10515921518836646965252721)
              ·
                refine ⟨7886941139127485223939541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10515921518836646965252721 7886941139127485223939541)
                ·
                  refine ⟨184850182948300434936083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7886941139127485223939541 184850182948300434936083)
                  ·
                    rfl

theorem cell23_3239950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 7].length) (baseStart_3239950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239950 prefixEnd_3239950 := by exact prefixLift 3239950
  have htrace : WordTrace (prefixWord ++ tailWord_3239950) baseStart_3239950 baseEnd_3239950 := by
    simpa [prefixWord, tailWord_3239950, baseEnd_3239950] using wordTrace_append hprefix tailTrace_3239950
  have hstable : (prefixWord ++ tailWord_3239950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239950).length < 2 ^ (prefixWord ++ tailWord_3239950).sum := by decide
  have hdescent : baseEnd_3239950 < baseStart_3239950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239960 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 1, 5, 3]
def baseStart_3239960 : Nat := 118140960795 + 3239960 * 2 ^ 59
def prefixEnd_3239960 : Nat := 4983230072969 + 3 ^ 40 * 3239960 * 2
def baseEnd_3239960 : Nat := 1663656781341248875299701

theorem tailTrace_3239960 : CollatzResearch.WordTrace tailWord_3239960 prefixEnd_3239960 1663656781341248875299701 := by
  unfold tailWord_3239960
  simp only [CollatzResearch.WordTrace]
  refine ⟨59085524671092867979686667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78780699561457157306248889 59085524671092867979686667)
  ·
    refine ⟨88628287006639301969530001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59085524671092867979686667 88628287006639301969530001)
    ·
      refine ⟨66471215254979476477147501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88628287006639301969530001 66471215254979476477147501)
      ·
        refine ⟨24926705720617303678930313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66471215254979476477147501 24926705720617303678930313)
        ·
          refine ⟨18695029290462977759197735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24926705720617303678930313 18695029290462977759197735)
          ·
            refine ⟨28042543935694466638796603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18695029290462977759197735 28042543935694466638796603)
            ·
              refine ⟨42063815903541699958194905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28042543935694466638796603 42063815903541699958194905)
              ·
                refine ⟨31547861927656274968646179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42063815903541699958194905 31547861927656274968646179)
                ·
                  refine ⟨47321792891484412452969269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31547861927656274968646179 47321792891484412452969269)
                  ·
                    refine ⟨4436418083576663667465869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47321792891484412452969269 4436418083576663667465869)
                    ·
                      refine ⟨1663656781341248875299701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4436418083576663667465869 1663656781341248875299701)
                      ·
                        rfl

theorem cell23_3239960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_3239960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239960 prefixEnd_3239960 := by exact prefixLift 3239960
  have htrace : WordTrace (prefixWord ++ tailWord_3239960) baseStart_3239960 baseEnd_3239960 := by
    simpa [prefixWord, tailWord_3239960, baseEnd_3239960] using wordTrace_append hprefix tailTrace_3239960
  have hstable : (prefixWord ++ tailWord_3239960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239960).length < 2 ^ (prefixWord ++ tailWord_3239960).sum := by decide
  have hdescent : baseEnd_3239960 < baseStart_3239960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239967 : List Nat := [1, 1, 2, 4, 1, 2, 4, 3, 5]
def baseStart_3239967 : Nat := 118140960795 + 3239967 * 2 ^ 59
def prefixEnd_3239967 : Nat := 4983230072969 + 3 ^ 40 * 3239967 * 2
def baseEnd_3239967 : Nat := 184851152856203371990241

theorem tailTrace_3239967 : CollatzResearch.WordTrace tailWord_3239967 prefixEnd_3239967 184851152856203371990241 := by
  unfold tailWord_3239967
  simp only [CollatzResearch.WordTrace]
  refine ⟨118171304653160376154878155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78780869768773584103252103 118171304653160376154878155)
  ·
    refine ⟨177256956979740564232317233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118171304653160376154878155 177256956979740564232317233)
    ·
      refine ⟨132942717734805423174237925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177256956979740564232317233 132942717734805423174237925)
      ·
        refine ⟨24926759575276016845169611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132942717734805423174237925 24926759575276016845169611)
        ·
          refine ⟨37390139362914025267754417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24926759575276016845169611 37390139362914025267754417)
          ·
            refine ⟨28042604522185518950815813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37390139362914025267754417 28042604522185518950815813)
            ·
              refine ⟨5257988347909784803277965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28042604522185518950815813 5257988347909784803277965)
              ·
                refine ⟨1971745630466169301229237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5257988347909784803277965 1971745630466169301229237)
                ·
                  refine ⟨184851152856203371990241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1971745630466169301229237 184851152856203371990241)
                  ·
                    rfl

theorem cell23_3239967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3, 5].length) (baseStart_3239967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239967 prefixEnd_3239967 := by exact prefixLift 3239967
  have htrace : WordTrace (prefixWord ++ tailWord_3239967) baseStart_3239967 baseEnd_3239967 := by
    simpa [prefixWord, tailWord_3239967, baseEnd_3239967] using wordTrace_append hprefix tailTrace_3239967
  have hstable : (prefixWord ++ tailWord_3239967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239967).length < 2 ^ (prefixWord ++ tailWord_3239967).sum := by decide
  have hdescent : baseEnd_3239967 < baseStart_3239967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239978 : List Nat := [3, 1, 4, 1, 2, 3, 1, 2, 2, 2, 2]
def baseStart_3239978 : Nat := 118140960795 + 3239978 * 2 ^ 59
def prefixEnd_3239978 : Nat := 4983230072969 + 3 ^ 40 * 3239978 * 2
def baseEnd_3239978 : Nat := 1663666023993029804874619

theorem tailTrace_3239978 : CollatzResearch.WordTrace tailWord_3239978 prefixEnd_3239978 1663666023993029804874619 := by
  unfold tailWord_3239978
  simp only [CollatzResearch.WordTrace]
  refine ⟨29542926464030131258382147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78781137237413683355685725 29542926464030131258382147)
  ·
    refine ⟨44314389696045196887573221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29542926464030131258382147 44314389696045196887573221)
    ·
      refine ⟨8308948068008474416419979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44314389696045196887573221 8308948068008474416419979)
      ·
        refine ⟨12463422102012711624629969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8308948068008474416419979 12463422102012711624629969)
        ·
          refine ⟨9347566576509533718472477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12463422102012711624629969 9347566576509533718472477)
          ·
            refine ⟨3505337466191075144427179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9347566576509533718472477 3505337466191075144427179)
            ·
              refine ⟨5258006199286612716640769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3505337466191075144427179 5258006199286612716640769)
              ·
                refine ⟨3943504649464959537480577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5258006199286612716640769 3943504649464959537480577)
                ·
                  refine ⟨2957628487098719653110433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3943504649464959537480577 2957628487098719653110433)
                  ·
                    refine ⟨2218221365324039739832825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2957628487098719653110433 2218221365324039739832825)
                    ·
                      refine ⟨1663666023993029804874619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2218221365324039739832825 1663666023993029804874619)
                      ·
                        rfl

theorem cell23_3239978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_3239978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3239978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3239978 prefixEnd_3239978 := by exact prefixLift 3239978
  have htrace : WordTrace (prefixWord ++ tailWord_3239978) baseStart_3239978 baseEnd_3239978 := by
    simpa [prefixWord, tailWord_3239978, baseEnd_3239978] using wordTrace_append hprefix tailTrace_3239978
  have hstable : (prefixWord ++ tailWord_3239978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239978).length < 2 ^ (prefixWord ++ tailWord_3239978).sum := by decide
  have hdescent : baseEnd_3239978 < baseStart_3239978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240000 : List Nat := [2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 4]
def baseStart_3240000 : Nat := 118140960795 + 3240000 * 2 ^ 59
def prefixEnd_3240000 : Nat := 4983230072969 + 3 ^ 40 * 3240000 * 2
def baseEnd_3240000 : Nat := 1663677320567428718799517

theorem tailTrace_3240000 : CollatzResearch.WordTrace tailWord_3240000 prefixEnd_3240000 1663677320567428718799517 := by
  unfold tailWord_3240000
  simp only [CollatzResearch.WordTrace]
  refine ⟨59086254131020411395414727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78781672174693881860552969 59086254131020411395414727)
  ·
    refine ⟨88629381196530617093122091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59086254131020411395414727 88629381196530617093122091)
    ·
      refine ⟨132944071794795925639683137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88629381196530617093122091 132944071794795925639683137)
      ·
        refine ⟨99708053846096944229762353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132944071794795925639683137 99708053846096944229762353)
        ·
          refine ⟨74781040384572708172321765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99708053846096944229762353 74781040384572708172321765)
          ·
            refine ⟨14021445072107382782310331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74781040384572708172321765 14021445072107382782310331)
            ·
              refine ⟨21032167608161074173465497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14021445072107382782310331 21032167608161074173465497)
              ·
                refine ⟨15774125706120805630099123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21032167608161074173465497 15774125706120805630099123)
                ·
                  refine ⟨23661188559181208445148685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15774125706120805630099123 23661188559181208445148685)
                  ·
                    refine ⟨8872945709692953166930757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23661188559181208445148685 8872945709692953166930757)
                    ·
                      refine ⟨1663677320567428718799517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8872945709692953166930757 1663677320567428718799517)
                      ·
                        rfl

theorem cell23_3240000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_3240000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240000 prefixEnd_3240000 := by exact prefixLift 3240000
  have htrace : WordTrace (prefixWord ++ tailWord_3240000) baseStart_3240000 baseEnd_3240000 := by
    simpa [prefixWord, tailWord_3240000, baseEnd_3240000] using wordTrace_append hprefix tailTrace_3240000
  have hstable : (prefixWord ++ tailWord_3240000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240000).length < 2 ^ (prefixWord ++ tailWord_3240000).sum := by decide
  have hdescent : baseEnd_3240000 < baseStart_3240000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240020 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 2, 3, 5]
def baseStart_3240020 : Nat := 118140960795 + 3240020 * 2 ^ 59
def prefixEnd_3240020 : Nat := 4983230072969 + 3 ^ 40 * 3240020 * 2
def baseEnd_3240020 : Nat := 1663687590180518640549425

theorem tailTrace_3240020 : CollatzResearch.WordTrace tailWord_3240020 prefixEnd_3240020 1663687590180518640549425 := by
  unfold tailWord_3240020
  simp only [CollatzResearch.WordTrace]
  refine ⟨59086618860984183103278757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78782158481312244137705009 59086618860984183103278757)
  ·
    refine ⟨11078741036434534331864767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59086618860984183103278757 11078741036434534331864767)
    ·
      refine ⟨16618111554651801497797151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11078741036434534331864767 16618111554651801497797151)
      ·
        refine ⟨24927167331977702246695727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16618111554651801497797151 24927167331977702246695727)
        ·
          refine ⟨37390750997966553370043591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24927167331977702246695727 37390750997966553370043591)
          ·
            refine ⟨56086126496949830055065387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37390750997966553370043591 56086126496949830055065387)
            ·
              refine ⟨84129189745424745082598081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56086126496949830055065387 84129189745424745082598081)
              ·
                refine ⟨63096892309068558811948561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84129189745424745082598081 63096892309068558811948561)
                ·
                  refine ⟨47322669231801419108961421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63096892309068558811948561 47322669231801419108961421)
                  ·
                    refine ⟨17746000961925532165860533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47322669231801419108961421 17746000961925532165860533)
                    ·
                      refine ⟨1663687590180518640549425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17746000961925532165860533 1663687590180518640549425)
                      ·
                        rfl

theorem cell23_3240020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_3240020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240020 prefixEnd_3240020 := by exact prefixLift 3240020
  have htrace : WordTrace (prefixWord ++ tailWord_3240020) baseStart_3240020 baseEnd_3240020 := by
    simpa [prefixWord, tailWord_3240020, baseEnd_3240020] using wordTrace_append hprefix tailTrace_3240020
  have hstable : (prefixWord ++ tailWord_3240020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240020).length < 2 ^ (prefixWord ++ tailWord_3240020).sum := by decide
  have hdescent : baseEnd_3240020 < baseStart_3240020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240037 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 4, 2, 3]
def baseStart_3240037 : Nat := 118140960795 + 3240037 * 2 ^ 59
def prefixEnd_3240037 : Nat := 4983230072969 + 3 ^ 40 * 3240037 * 2
def baseEnd_3240037 : Nat := 1663696319351645074036847

theorem tailTrace_3240037 : CollatzResearch.WordTrace tailWord_3240037 prefixEnd_3240037 1663696319351645074036847 := by
  unfold tailWord_3240037
  simp only [CollatzResearch.WordTrace]
  refine ⟨118173857762906778109926365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78782571841937852073284243 118173857762906778109926365)
  ·
    refine ⟨44315196661090041791222387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118173857762906778109926365 44315196661090041791222387)
    ·
      refine ⟨66472794991635062686833581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44315196661090041791222387 66472794991635062686833581)
      ·
        refine ⟨24927298121863148507562593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66472794991635062686833581 24927298121863148507562593)
        ·
          refine ⟨18695473591397361380671945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24927298121863148507562593 18695473591397361380671945)
          ·
            refine ⟨14021605193548021035503959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18695473591397361380671945 14021605193548021035503959)
            ·
              refine ⟨21032407790322031553255939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14021605193548021035503959 21032407790322031553255939)
              ·
                refine ⟨31548611685483047329883909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21032407790322031553255939 31548611685483047329883909)
                ·
                  refine ⟨5915364691028071374353233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31548611685483047329883909 5915364691028071374353233)
                  ·
                    refine ⟨4436523518271053530764925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5915364691028071374353233 4436523518271053530764925)
                    ·
                      refine ⟨1663696319351645074036847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4436523518271053530764925 1663696319351645074036847)
                      ·
                        rfl

theorem cell23_3240037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_3240037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240037 prefixEnd_3240037 := by exact prefixLift 3240037
  have htrace : WordTrace (prefixWord ++ tailWord_3240037) baseStart_3240037 baseEnd_3240037 := by
    simpa [prefixWord, tailWord_3240037, baseEnd_3240037] using wordTrace_append hprefix tailTrace_3240037
  have hstable : (prefixWord ++ tailWord_3240037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240037).length < 2 ^ (prefixWord ++ tailWord_3240037).sum := by decide
  have hdescent : baseEnd_3240037 < baseStart_3240037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240044 : List Nat := [2, 2, 1, 1, 3, 5, 1, 1, 3, 4]
def baseStart_3240044 : Nat := 118140960795 + 3240044 * 2 ^ 59
def prefixEnd_3240044 : Nat := 4983230072969 + 3 ^ 40 * 3240044 * 2
def baseEnd_3240044 : Nat := 554566637905408848883105

theorem tailTrace_3240044 : CollatzResearch.WordTrace tailWord_3240044 prefixEnd_3240044 554566637905408848883105 := by
  unfold tailWord_3240044
  simp only [CollatzResearch.WordTrace]
  refine ⟨59087056536940709152715593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78782742049254278870287457 59087056536940709152715593)
  ·
    refine ⟨44315292402705531864536695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59087056536940709152715593 44315292402705531864536695)
    ·
      refine ⟨66472938604058297796805043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44315292402705531864536695 66472938604058297796805043)
      ·
        refine ⟨99709407906087446695207565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66472938604058297796805043 99709407906087446695207565)
        ·
          refine ⟨37391027964782792510702837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99709407906087446695207565 37391027964782792510702837)
          ·
            refine ⟨3505408871698386797878391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37391027964782792510702837 3505408871698386797878391)
            ·
              refine ⟨5258113307547580196817587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3505408871698386797878391 5258113307547580196817587)
              ·
                refine ⟨7887169961321370295226381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5258113307547580196817587 7887169961321370295226381)
                ·
                  refine ⟨2957688735495513860709893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7887169961321370295226381 2957688735495513860709893)
                  ·
                    refine ⟨554566637905408848883105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2957688735495513860709893 554566637905408848883105)
                    ·
                      rfl

theorem cell23_3240044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 4].length) (baseStart_3240044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240044 prefixEnd_3240044 := by exact prefixLift 3240044
  have htrace : WordTrace (prefixWord ++ tailWord_3240044) baseStart_3240044 baseEnd_3240044 := by
    simpa [prefixWord, tailWord_3240044, baseEnd_3240044] using wordTrace_append hprefix tailTrace_3240044
  have hstable : (prefixWord ++ tailWord_3240044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240044).length < 2 ^ (prefixWord ++ tailWord_3240044).sum := by decide
  have hdescent : baseEnd_3240044 < baseStart_3240044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240057 : List Nat := [1, 2, 1, 3, 4, 2, 1, 3, 6]
def baseStart_3240057 : Nat := 118140960795 + 3240057 * 2 ^ 59
def prefixEnd_3240057 : Nat := 4983230072969 + 3 ^ 40 * 3240057 * 2
def baseEnd_3240057 : Nat := 184856287662748332865195

theorem tailTrace_3240057 : CollatzResearch.WordTrace tailWord_3240057 prefixEnd_3240057 184856287662748332865195 := by
  unfold tailWord_3240057
  simp only [CollatzResearch.WordTrace]
  refine ⟨118174587222834321525654425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78783058148556214350436283 118174587222834321525654425)
  ·
    refine ⟨88630940417125741144240819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118174587222834321525654425 88630940417125741144240819)
    ·
      refine ⟨132946410625688611716361229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88630940417125741144240819 132946410625688611716361229)
      ·
        refine ⟨49854903984633229393635461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132946410625688611716361229 49854903984633229393635461)
        ·
          refine ⟨9347794497118730511306649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49854903984633229393635461 9347794497118730511306649)
          ·
            refine ⟨7010845872839047883479987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9347794497118730511306649 7010845872839047883479987)
            ·
              refine ⟨10516268809258571825219981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7010845872839047883479987 10516268809258571825219981)
              ·
                refine ⟨3943600803471964434457493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10516268809258571825219981 3943600803471964434457493)
                ·
                  refine ⟨184856287662748332865195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3943600803471964434457493 184856287662748332865195)
                  ·
                    rfl

theorem cell23_3240057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 6].length) (baseStart_3240057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240057 prefixEnd_3240057 := by exact prefixLift 3240057
  have htrace : WordTrace (prefixWord ++ tailWord_3240057) baseStart_3240057 baseEnd_3240057 := by
    simpa [prefixWord, tailWord_3240057, baseEnd_3240057] using wordTrace_append hprefix tailTrace_3240057
  have hstable : (prefixWord ++ tailWord_3240057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240057).length < 2 ^ (prefixWord ++ tailWord_3240057).sum := by decide
  have hdescent : baseEnd_3240057 < baseStart_3240057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240101 : List Nat := [1, 3, 1, 2, 1, 3, 3, 4, 1, 1, 3]
def baseStart_3240101 : Nat := 118140960795 + 3240101 * 2 ^ 59
def prefixEnd_3240101 : Nat := 4983230072969 + 3 ^ 40 * 3240101 * 2
def baseEnd_3240101 : Nat := 1663729182113532823636553

theorem tailTrace_3240101 : CollatzResearch.WordTrace tailWord_3240101 prefixEnd_3240101 1663729182113532823636553 := by
  unfold tailWord_3240101
  simp only [CollatzResearch.WordTrace]
  refine ⟨118176192034674917040256157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78784128023116611360170771 118176192034674917040256157)
  ·
    refine ⟨44316072013003093890096059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118176192034674917040256157 44316072013003093890096059)
    ·
      refine ⟨66474108019504640835144089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44316072013003093890096059 66474108019504640835144089)
      ·
        refine ⟨49855581014628480626358067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66474108019504640835144089 49855581014628480626358067)
        ·
          refine ⟨74783371521942720939537101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49855581014628480626358067 74783371521942720939537101)
          ·
            refine ⟨28043764320728520352326413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74783371521942720939537101 28043764320728520352326413)
            ·
              refine ⟨10516411620273195132122405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28043764320728520352326413 10516411620273195132122405)
              ·
                refine ⟨1971827178801224087272951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10516411620273195132122405 1971827178801224087272951)
                ·
                  refine ⟨2957740768201836130909427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1971827178801224087272951 2957740768201836130909427)
                  ·
                    refine ⟨4436611152302754196364141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2957740768201836130909427 4436611152302754196364141)
                    ·
                      refine ⟨1663729182113532823636553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4436611152302754196364141 1663729182113532823636553)
                      ·
                        rfl

theorem cell23_3240101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 4, 1, 1, 3].length) (baseStart_3240101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240101 prefixEnd_3240101 := by exact prefixLift 3240101
  have htrace : WordTrace (prefixWord ++ tailWord_3240101) baseStart_3240101 baseEnd_3240101 := by
    simpa [prefixWord, tailWord_3240101, baseEnd_3240101] using wordTrace_append hprefix tailTrace_3240101
  have hstable : (prefixWord ++ tailWord_3240101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240101).length < 2 ^ (prefixWord ++ tailWord_3240101).sum := by decide
  have hdescent : baseEnd_3240101 < baseStart_3240101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240184 : List Nat := [2, 1, 2, 1, 1, 2, 1, 5, 3, 3, 2]
def baseStart_3240184 : Nat := 118140960795 + 3240184 * 2 ^ 59
def prefixEnd_3240184 : Nat := 4983230072969 + 3 ^ 40 * 3240184 * 2
def baseEnd_3240184 : Nat := 1663771801007855998898671

theorem tailTrace_3240184 : CollatzResearch.WordTrace tailWord_3240184 prefixEnd_3240184 1663771801007855998898671 := by
  unfold tailWord_3240184
  simp only [CollatzResearch.WordTrace]
  refine ⟨59089609646687111107763803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78786146195582814810351737 59089609646687111107763803)
  ·
    refine ⟨88634414470030666661645705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59089609646687111107763803 88634414470030666661645705)
    ·
      refine ⟨66475810852522999996234279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88634414470030666661645705 66475810852522999996234279)
      ·
        refine ⟨99713716278784499994351419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66475810852522999996234279 99713716278784499994351419)
        ·
          refine ⟨149570574418176749991527129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99713716278784499994351419 149570574418176749991527129)
          ·
            refine ⟨112177930813632562493645347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149570574418176749991527129 112177930813632562493645347)
            ·
              refine ⟨168266896220448843740468021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112177930813632562493645347 168266896220448843740468021)
              ·
                refine ⟨15775021520667079100668877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 168266896220448843740468021 15775021520667079100668877)
                ·
                  refine ⟨5915633070250154662750829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15775021520667079100668877 5915633070250154662750829)
                  ·
                    refine ⟨2218362401343807998531561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5915633070250154662750829 2218362401343807998531561)
                    ·
                      refine ⟨1663771801007855998898671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2218362401343807998531561 1663771801007855998898671)
                      ·
                        rfl

theorem cell23_3240184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 3, 3, 2].length) (baseStart_3240184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240184 prefixEnd_3240184 := by exact prefixLift 3240184
  have htrace : WordTrace (prefixWord ++ tailWord_3240184) baseStart_3240184 baseEnd_3240184 := by
    simpa [prefixWord, tailWord_3240184, baseEnd_3240184] using wordTrace_append hprefix tailTrace_3240184
  have hstable : (prefixWord ++ tailWord_3240184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240184).length < 2 ^ (prefixWord ++ tailWord_3240184).sum := by decide
  have hdescent : baseEnd_3240184 < baseStart_3240184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240201 : List Nat := [1, 2, 1, 1, 3, 4, 2, 3, 1, 3, 2]
def baseStart_3240201 : Nat := 118140960795 + 3240201 * 2 ^ 59
def prefixEnd_3240201 : Nat := 4983230072969 + 3 ^ 40 * 3240201 * 2
def baseEnd_3240201 : Nat := 1663780530178982432386093

theorem tailTrace_3240201 : CollatzResearch.WordTrace tailWord_3240201 prefixEnd_3240201 1663780530178982432386093 := by
  unfold tailWord_3240201
  simp only [CollatzResearch.WordTrace]
  refine ⟨118179839334312634118896457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78786559556208422745930971 118179839334312634118896457)
  ·
    refine ⟨88634879500734475589172343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118179839334312634118896457 88634879500734475589172343)
    ·
      refine ⟨132952319251101713383758515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88634879500734475589172343 132952319251101713383758515)
      ·
        refine ⟨199428478876652570075637773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132952319251101713383758515 199428478876652570075637773)
        ·
          refine ⟨74785679578744713778364165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199428478876652570075637773 74785679578744713778364165)
          ·
            refine ⟨14022314921014633833443281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74785679578744713778364165 14022314921014633833443281)
            ·
              refine ⟨10516736190760975375082461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14022314921014633833443281 10516736190760975375082461)
              ·
                refine ⟨3943776071535365765655923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10516736190760975375082461 3943776071535365765655923)
                ·
                  refine ⟨5915664107303048648483885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3943776071535365765655923 5915664107303048648483885)
                  ·
                    refine ⟨2218374040238643243181457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5915664107303048648483885 2218374040238643243181457)
                    ·
                      refine ⟨1663780530178982432386093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2218374040238643243181457 1663780530178982432386093)
                      ·
                        rfl

theorem cell23_3240201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 3, 2].length) (baseStart_3240201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240201 prefixEnd_3240201 := by exact prefixLift 3240201
  have htrace : WordTrace (prefixWord ++ tailWord_3240201) baseStart_3240201 baseEnd_3240201 := by
    simpa [prefixWord, tailWord_3240201, baseEnd_3240201] using wordTrace_append hprefix tailTrace_3240201
  have hstable : (prefixWord ++ tailWord_3240201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240201).length < 2 ^ (prefixWord ++ tailWord_3240201).sum := by decide
  have hdescent : baseEnd_3240201 < baseStart_3240201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240227 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 4]
def baseStart_3240227 : Nat := 118140960795 + 3240227 * 2 ^ 59
def prefixEnd_3240227 : Nat := 4983230072969 + 3 ^ 40 * 3240227 * 2
def baseEnd_3240227 : Nat := 1663793880675999330660973

theorem tailTrace_3240227 : CollatzResearch.WordTrace tailWord_3240227 prefixEnd_3240227 1663793880675999330660973 := by
  unfold tailWord_3240227
  simp only [CollatzResearch.WordTrace]
  refine ⟨118180787632218440559342935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78787191754812293706228623 118180787632218440559342935)
  ·
    refine ⟨177271181448327660839014403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118180787632218440559342935 177271181448327660839014403)
    ·
      refine ⟨265906772172491491258521605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177271181448327660839014403 265906772172491491258521605)
      ·
        refine ⟨49857519782342154610972801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265906772172491491258521605 49857519782342154610972801)
        ·
          refine ⟨37393139836756615958229601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49857519782342154610972801 37393139836756615958229601)
          ·
            refine ⟨28044854877567461968672201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37393139836756615958229601 28044854877567461968672201)
            ·
              refine ⟨21033641158175596476504151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28044854877567461968672201 21033641158175596476504151)
              ·
                refine ⟨31550461737263394714756227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21033641158175596476504151 31550461737263394714756227)
                ·
                  refine ⟨47325692605895092072134341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31550461737263394714756227 47325692605895092072134341)
                  ·
                    refine ⟨8873567363605329763525189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47325692605895092072134341 8873567363605329763525189)
                    ·
                      refine ⟨1663793880675999330660973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8873567363605329763525189 1663793880675999330660973)
                      ·
                        rfl

theorem cell23_3240227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_3240227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240227 prefixEnd_3240227 := by exact prefixLift 3240227
  have htrace : WordTrace (prefixWord ++ tailWord_3240227) baseStart_3240227 baseEnd_3240227 := by
    simpa [prefixWord, tailWord_3240227, baseEnd_3240227] using wordTrace_append hprefix tailTrace_3240227
  have hstable : (prefixWord ++ tailWord_3240227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240227).length < 2 ^ (prefixWord ++ tailWord_3240227).sum := by decide
  have hdescent : baseEnd_3240227 < baseStart_3240227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240267 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 4, 5]
def baseStart_3240267 : Nat := 118140960795 + 3240267 * 2 ^ 59
def prefixEnd_3240267 : Nat := 4983230072969 + 3 ^ 40 * 3240267 * 2
def baseEnd_3240267 : Nat := 554604806634059724720263

theorem tailTrace_3240267 : CollatzResearch.WordTrace tailWord_3240267 prefixEnd_3240267 554604806634059724720263 := by
  unfold tailWord_3240267
  simp only [CollatzResearch.WordTrace]
  refine ⟨118182246552073527390799055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78788164368049018260532703 118182246552073527390799055)
  ·
    refine ⟨177273369828110291086198583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118182246552073527390799055 177273369828110291086198583)
    ·
      refine ⟨265910054742165436629297875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177273369828110291086198583 265910054742165436629297875)
      ·
        refine ⟨398865082113248154943946813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265910054742165436629297875 398865082113248154943946813)
        ·
          refine ⟨149574405792468058103980055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 398865082113248154943946813 149574405792468058103980055)
          ·
            refine ⟨224361608688702087155970083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149574405792468058103980055 224361608688702087155970083)
            ·
              refine ⟨336542413033053130733955125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224361608688702087155970083 336542413033053130733955125)
              ·
                refine ⟨31550851221848731006308293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 336542413033053130733955125 31550851221848731006308293)
                ·
                  refine ⟨5915784604096637063682805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31550851221848731006308293 5915784604096637063682805)
                  ·
                    refine ⟨554604806634059724720263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5915784604096637063682805 554604806634059724720263)
                    ·
                      rfl

theorem cell23_3240267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 5].length) (baseStart_3240267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240267 prefixEnd_3240267 := by exact prefixLift 3240267
  have htrace : WordTrace (prefixWord ++ tailWord_3240267) baseStart_3240267 baseEnd_3240267 := by
    simpa [prefixWord, tailWord_3240267, baseEnd_3240267] using wordTrace_append hprefix tailTrace_3240267
  have hstable : (prefixWord ++ tailWord_3240267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240267).length < 2 ^ (prefixWord ++ tailWord_3240267).sum := by decide
  have hdescent : baseEnd_3240267 < baseStart_3240267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240304 : List Nat := [2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 4]
def baseStart_3240304 : Nat := 118140960795 + 3240304 * 2 ^ 59
def prefixEnd_3240304 : Nat := 4983230072969 + 3 ^ 40 * 3240304 * 2
def baseEnd_3240304 : Nat := 1663833418686395529398119

theorem tailTrace_3240304 : CollatzResearch.WordTrace tailWord_3240304 prefixEnd_3240304 1663833418686395529398119 := by
  unfold tailWord_3240304
  simp only [CollatzResearch.WordTrace]
  refine ⟨59091798026469741354947983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78789064035292988473263977 59091798026469741354947983)
  ·
    refine ⟨88637697039704612032421975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59091798026469741354947983 88637697039704612032421975)
    ·
      refine ⟨132956545559556918048632963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88637697039704612032421975 132956545559556918048632963)
      ·
        refine ⟨199434818339335377072949445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132956545559556918048632963 199434818339335377072949445)
        ·
          refine ⟨37394028438625383201178021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 199434818339335377072949445 37394028438625383201178021)
          ·
            refine ⟨7011380332242259350220879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37394028438625383201178021 7011380332242259350220879)
            ·
              refine ⟨10517070498363389025331319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7011380332242259350220879 10517070498363389025331319)
              ·
                refine ⟨15775605747545083537996979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10517070498363389025331319 15775605747545083537996979)
                ·
                  refine ⟨23663408621317625306995469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15775605747545083537996979 23663408621317625306995469)
                  ·
                    refine ⟨8873778232994109490123301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23663408621317625306995469 8873778232994109490123301)
                    ·
                      refine ⟨1663833418686395529398119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8873778232994109490123301 1663833418686395529398119)
                      ·
                        rfl

theorem cell23_3240304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 4].length) (baseStart_3240304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240304 prefixEnd_3240304 := by exact prefixLift 3240304
  have htrace : WordTrace (prefixWord ++ tailWord_3240304) baseStart_3240304 baseEnd_3240304 := by
    simpa [prefixWord, tailWord_3240304, baseEnd_3240304] using wordTrace_append hprefix tailTrace_3240304
  have hstable : (prefixWord ++ tailWord_3240304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240304).length < 2 ^ (prefixWord ++ tailWord_3240304).sum := by decide
  have hdescent : baseEnd_3240304 < baseStart_3240304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240331 : List Nat := [1, 1, 1, 1, 4, 5, 2, 1, 3, 4]
def baseStart_3240331 : Nat := 118140960795 + 3240331 * 2 ^ 59
def prefixEnd_3240331 : Nat := 4983230072969 + 3 ^ 40 * 3240331 * 2
def baseEnd_3240331 : Nat := 554615760888022307920165

theorem tailTrace_3240331 : CollatzResearch.WordTrace tailWord_3240331 prefixEnd_3240331 554615760888022307920165 := by
  unfold tailWord_3240331
  simp only [CollatzResearch.WordTrace]
  refine ⟨118184580823841666321128847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78789720549227777547419231 118184580823841666321128847)
  ·
    refine ⟨177276871235762499481693271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118184580823841666321128847 177276871235762499481693271)
    ·
      refine ⟨265915306853643749222539907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177276871235762499481693271 265915306853643749222539907)
      ·
        refine ⟨398872960280465623833809861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265915306853643749222539907 398872960280465623833809861)
        ·
          refine ⟨74788680052587304468839349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 398872960280465623833809861 74788680052587304468839349)
          ·
            refine ⟨7011438754930059793953689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74788680052587304468839349 7011438754930059793953689)
            ·
              refine ⟨5258579066197544845465267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7011438754930059793953689 5258579066197544845465267)
              ·
                refine ⟨7887868599296317268197901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5258579066197544845465267 7887868599296317268197901)
                ·
                  refine ⟨2957950724736118975574213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7887868599296317268197901 2957950724736118975574213)
                  ·
                    refine ⟨554615760888022307920165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2957950724736118975574213 554615760888022307920165)
                    ·
                      rfl

theorem cell23_3240331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 3, 4].length) (baseStart_3240331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240331 prefixEnd_3240331 := by exact prefixLift 3240331
  have htrace : WordTrace (prefixWord ++ tailWord_3240331) baseStart_3240331 baseEnd_3240331 := by
    simpa [prefixWord, tailWord_3240331, baseEnd_3240331] using wordTrace_append hprefix tailTrace_3240331
  have hstable : (prefixWord ++ tailWord_3240331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240331).length < 2 ^ (prefixWord ++ tailWord_3240331).sum := by decide
  have hdescent : baseEnd_3240331 < baseStart_3240331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240428 : List Nat := [2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 4]
def baseStart_3240428 : Nat := 118140960795 + 3240428 * 2 ^ 59
def prefixEnd_3240428 : Nat := 4983230072969 + 3 ^ 40 * 3240428 * 2
def baseEnd_3240428 : Nat := 1663897090287553044247549

theorem tailTrace_3240428 : CollatzResearch.WordTrace tailWord_3240428 prefixEnd_3240428 1663897090287553044247549 := by
  unfold tailWord_3240428
  simp only [CollatzResearch.WordTrace]
  refine ⟨59094059352245125943704969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78792079136326834591606625 59094059352245125943704969)
  ·
    refine ⟨44320544514183844457778727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59094059352245125943704969 44320544514183844457778727)
    ·
      refine ⟨66480816771275766686668091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44320544514183844457778727 66480816771275766686668091)
      ·
        refine ⟨99721225156913650030002137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66480816771275766686668091 99721225156913650030002137)
        ·
          refine ⟨74790918867685237522501603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99721225156913650030002137 74790918867685237522501603)
          ·
            refine ⟨112186378301527856283752405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74790918867685237522501603 112186378301527856283752405)
            ·
              refine ⟨2629368241442059131650447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 112186378301527856283752405 2629368241442059131650447)
              ·
                refine ⟨3944052362163088697475671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2629368241442059131650447 3944052362163088697475671)
                ·
                  refine ⟨5916078543244633046213507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3944052362163088697475671 5916078543244633046213507)
                  ·
                    refine ⟨8874117814866949569320261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5916078543244633046213507 8874117814866949569320261)
                    ·
                      refine ⟨1663897090287553044247549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8874117814866949569320261 1663897090287553044247549)
                      ·
                        rfl

theorem cell23_3240428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 4].length) (baseStart_3240428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240428 prefixEnd_3240428 := by exact prefixLift 3240428
  have htrace : WordTrace (prefixWord ++ tailWord_3240428) baseStart_3240428 baseEnd_3240428 := by
    simpa [prefixWord, tailWord_3240428, baseEnd_3240428] using wordTrace_append hprefix tailTrace_3240428
  have hstable : (prefixWord ++ tailWord_3240428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240428).length < 2 ^ (prefixWord ++ tailWord_3240428).sum := by decide
  have hdescent : baseEnd_3240428 < baseStart_3240428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240434 : List Nat := [3, 2, 1, 4, 13]
def baseStart_3240434 : Nat := 118140960795 + 3240434 * 2 ^ 59
def prefixEnd_3240434 : Nat := 4983230072969 + 3 ^ 40 * 3240434 * 2
def baseEnd_3240434 : Nat := 2282441935763347079249

theorem tailTrace_3240434 : CollatzResearch.WordTrace tailWord_3240434 prefixEnd_3240434 2282441935763347079249 := by
  unfold tailWord_3240434
  simp only [CollatzResearch.WordTrace]
  refine ⟨29547084385617128728032089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78792225028312343274752237 29547084385617128728032089)
  ·
    refine ⟨22160313289212846546024067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29547084385617128728032089 22160313289212846546024067)
    ·
      refine ⟨33240469933819269819036101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22160313289212846546024067 33240469933819269819036101)
      ·
        refine ⟨6232588112591113091069269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33240469933819269819036101 6232588112591113091069269)
        ·
          refine ⟨2282441935763347079249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 6232588112591113091069269 2282441935763347079249)
          ·
            rfl

theorem cell23_3240434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 13].length) (baseStart_3240434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240434 prefixEnd_3240434 := by exact prefixLift 3240434
  have htrace : WordTrace (prefixWord ++ tailWord_3240434) baseStart_3240434 baseEnd_3240434 := by
    simpa [prefixWord, tailWord_3240434, baseEnd_3240434] using wordTrace_append hprefix tailTrace_3240434
  have hstable : (prefixWord ++ tailWord_3240434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240434).length < 2 ^ (prefixWord ++ tailWord_3240434).sum := by decide
  have hdescent : baseEnd_3240434 < baseStart_3240434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240558 : List Nat := [4, 1, 2, 2, 2, 1, 3, 1, 7]
def baseStart_3240558 : Nat := 118140960795 + 3240558 * 2 ^ 59
def prefixEnd_3240558 : Nat := 4983230072969 + 3 ^ 40 * 3240558 * 2
def baseEnd_3240558 : Nat := 184884871419181948402439

theorem tailTrace_3240558 : CollatzResearch.WordTrace tailWord_3240558 prefixEnd_3240558 184884871419181948402439 := by
  unfold tailWord_3240558
  simp only [CollatzResearch.WordTrace]
  refine ⟨14774107524252410511205291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78795240129346189393094885 14774107524252410511205291)
  ·
    refine ⟨22161161286378615766807937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14774107524252410511205291 22161161286378615766807937)
    ·
      refine ⟨16620870964783961825105953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22161161286378615766807937 16620870964783961825105953)
      ·
        refine ⟨12465653223587971368829465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16620870964783961825105953 12465653223587971368829465)
        ·
          refine ⟨9349239917690978526622099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12465653223587971368829465 9349239917690978526622099)
          ·
            refine ⟨14023859876536467789933149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9349239917690978526622099 14023859876536467789933149)
            ·
              refine ⟨5258947453701175421224931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14023859876536467789933149 5258947453701175421224931)
              ·
                refine ⟨7888421180551763131837397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5258947453701175421224931 7888421180551763131837397)
                ·
                  refine ⟨184884871419181948402439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7888421180551763131837397 184884871419181948402439)
                  ·
                    rfl

theorem cell23_3240558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 7].length) (baseStart_3240558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240558 prefixEnd_3240558 := by exact prefixLift 3240558
  have htrace : WordTrace (prefixWord ++ tailWord_3240558) baseStart_3240558 baseEnd_3240558 := by
    simpa [prefixWord, tailWord_3240558, baseEnd_3240558] using wordTrace_append hprefix tailTrace_3240558
  have hstable : (prefixWord ++ tailWord_3240558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240558).length < 2 ^ (prefixWord ++ tailWord_3240558).sum := by decide
  have hdescent : baseEnd_3240558 < baseStart_3240558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240569 : List Nat := [1, 2, 1, 3, 3, 4, 2, 1, 2, 2, 2]
def baseStart_3240569 : Nat := 118140960795 + 3240569 * 2 ^ 59
def prefixEnd_3240569 : Nat := 4983230072969 + 3 ^ 40 * 3240569 * 2
def baseEnd_3240569 : Nat := 1663969491059836992584401

theorem tailTrace_3240569 : CollatzResearch.WordTrace tailWord_3240569 prefixEnd_3240569 1663969491059836992584401 := by
  unfold tailWord_3240569
  simp only [CollatzResearch.WordTrace]
  refine ⟨118193261396979432968292761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78795507597986288645528507 118193261396979432968292761)
  ·
    refine ⟨88644946047734574726219571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118193261396979432968292761 88644946047734574726219571)
    ·
      refine ⟨132967419071601862089329357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88644946047734574726219571 132967419071601862089329357)
      ·
        refine ⟨49862782151850698283498509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132967419071601862089329357 49862782151850698283498509)
        ·
          refine ⟨18698543306944011856311941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49862782151850698283498509 18698543306944011856311941)
          ·
            refine ⟨3505976870052002223058489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18698543306944011856311941 3505976870052002223058489)
            ·
              refine ⟨2629482652539001667293867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3505976870052002223058489 2629482652539001667293867)
              ·
                refine ⟨3944223978808502500940801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2629482652539001667293867 3944223978808502500940801)
                ·
                  refine ⟨2958167984106376875705601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3944223978808502500940801 2958167984106376875705601)
                  ·
                    refine ⟨2218625988079782656779201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2958167984106376875705601 2218625988079782656779201)
                    ·
                      refine ⟨1663969491059836992584401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2218625988079782656779201 1663969491059836992584401)
                      ·
                        rfl

theorem cell23_3240569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 2, 2, 2].length) (baseStart_3240569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240569 prefixEnd_3240569 := by exact prefixLift 3240569
  have htrace : WordTrace (prefixWord ++ tailWord_3240569) baseStart_3240569 baseEnd_3240569 := by
    simpa [prefixWord, tailWord_3240569, baseEnd_3240569] using wordTrace_append hprefix tailTrace_3240569
  have hstable : (prefixWord ++ tailWord_3240569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240569).length < 2 ^ (prefixWord ++ tailWord_3240569).sum := by decide
  have hdescent : baseEnd_3240569 < baseStart_3240569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240591 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 4]
def baseStart_3240591 : Nat := 118140960795 + 3240591 * 2 ^ 59
def prefixEnd_3240591 : Nat := 4983230072969 + 3 ^ 40 * 3240591 * 2
def baseEnd_3240591 : Nat := 1663980787634235906509299

theorem tailTrace_3240591 : CollatzResearch.WordTrace tailWord_3240591 prefixEnd_3240591 1663980787634235906509299 := by
  unfold tailWord_3240591
  simp only [CollatzResearch.WordTrace]
  refine ⟨118194063802899730725593627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78796042535266487150395751 118194063802899730725593627)
  ·
    refine ⟨177291095704349596088390441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118194063802899730725593627 177291095704349596088390441)
    ·
      refine ⟨132968321778262197066292831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177291095704349596088390441 132968321778262197066292831)
      ·
        refine ⟨199452482667393295599439247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132968321778262197066292831 199452482667393295599439247)
        ·
          refine ⟨299178724001089943399158871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199452482667393295599439247 299178724001089943399158871)
          ·
            refine ⟨448768086001634915098738307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299178724001089943399158871 448768086001634915098738307)
            ·
              refine ⟨673152129002452372648107461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448768086001634915098738307 673152129002452372648107461)
              ·
                refine ⟨126216024187959819871520149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 673152129002452372648107461 126216024187959819871520149)
                ·
                  refine ⟨5916376133810616556477507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 126216024187959819871520149 5916376133810616556477507)
                  ·
                    refine ⟨8874564200715924834716261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5916376133810616556477507 8874564200715924834716261)
                    ·
                      refine ⟨1663980787634235906509299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8874564200715924834716261 1663980787634235906509299)
                      ·
                        rfl

theorem cell23_3240591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 4].length) (baseStart_3240591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240591 prefixEnd_3240591 := by exact prefixLift 3240591
  have htrace : WordTrace (prefixWord ++ tailWord_3240591) baseStart_3240591 baseEnd_3240591 := by
    simpa [prefixWord, tailWord_3240591, baseEnd_3240591] using wordTrace_append hprefix tailTrace_3240591
  have hstable : (prefixWord ++ tailWord_3240591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240591).length < 2 ^ (prefixWord ++ tailWord_3240591).sum := by decide
  have hdescent : baseEnd_3240591 < baseStart_3240591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240609 : List Nat := [1, 2, 3, 3, 4, 1, 2, 2, 5]
def baseStart_3240609 : Nat := 118140960795 + 3240609 * 2 ^ 59
def prefixEnd_3240609 : Nat := 4983230072969 + 3 ^ 40 * 3240609 * 2
def baseEnd_3240609 : Nat := 184887781142890759564913

theorem tailTrace_3240609 : CollatzResearch.WordTrace tailWord_3240609 prefixEnd_3240609 184887781142890759564913 := by
  unfold tailWord_3240609
  simp only [CollatzResearch.WordTrace]
  refine ⟨118194720316834519799748881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78796480211223013199832587 118194720316834519799748881)
  ·
    refine ⟨88646040237625889849811661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118194720316834519799748881 88646040237625889849811661)
    ·
      refine ⟨33242265089109708693679373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88646040237625889849811661 33242265089109708693679373)
      ·
        refine ⟨12465849408416140760129765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33242265089109708693679373 12465849408416140760129765)
        ·
          refine ⟨2337346764078026392524331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12465849408416140760129765 2337346764078026392524331)
          ·
            refine ⟨3506020146117039588786497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2337346764078026392524331 3506020146117039588786497)
            ·
              refine ⟨2629515109587779691589873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3506020146117039588786497 2629515109587779691589873)
              ·
                refine ⟨1972136332190834768692405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2629515109587779691589873 1972136332190834768692405)
                ·
                  refine ⟨184887781142890759564913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1972136332190834768692405 184887781142890759564913)
                  ·
                    rfl

theorem cell23_3240609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 2, 5].length) (baseStart_3240609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240609 prefixEnd_3240609 := by exact prefixLift 3240609
  have htrace : WordTrace (prefixWord ++ tailWord_3240609) baseStart_3240609 baseEnd_3240609 := by
    simpa [prefixWord, tailWord_3240609, baseEnd_3240609] using wordTrace_append hprefix tailTrace_3240609
  have hstable : (prefixWord ++ tailWord_3240609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240609).length < 2 ^ (prefixWord ++ tailWord_3240609).sum := by decide
  have hdescent : baseEnd_3240609 < baseStart_3240609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240652 : List Nat := [2, 2, 1, 5, 1, 1, 1, 5, 1, 4]
def baseStart_3240652 : Nat := 118140960795 + 3240652 * 2 ^ 59
def prefixEnd_3240652 : Nat := 4983230072969 + 3 ^ 40 * 3240652 * 2
def baseEnd_3240652 : Nat := 554670703318053389282173

theorem tailTrace_3240652 : CollatzResearch.WordTrace tailWord_3240652 prefixEnd_3240652 554670703318053389282173 := by
  unfold tailWord_3240652
  simp only [CollatzResearch.WordTrace]
  refine ⟨59098144327839369071782105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78797525770452492095709473 59098144327839369071782105)
  ·
    refine ⟨44323608245879526803836579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59098144327839369071782105 44323608245879526803836579)
    ·
      refine ⟨66485412368819290205754869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44323608245879526803836579 66485412368819290205754869)
      ·
        refine ⟨6233007409576808456789519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66485412368819290205754869 6233007409576808456789519)
        ·
          refine ⟨9349511114365212685184279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6233007409576808456789519 9349511114365212685184279)
          ·
            refine ⟨14024266671547819027776419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9349511114365212685184279 14024266671547819027776419)
            ·
              refine ⟨21036400007321728541664629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14024266671547819027776419 21036400007321728541664629)
              ·
                refine ⟨1972162500686412050781059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21036400007321728541664629 1972162500686412050781059)
                ·
                  refine ⟨2958243751029618076171589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1972162500686412050781059 2958243751029618076171589)
                  ·
                    refine ⟨554670703318053389282173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2958243751029618076171589 554670703318053389282173)
                    ·
                      rfl

theorem cell23_3240652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 5, 1, 4].length) (baseStart_3240652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240652 prefixEnd_3240652 := by exact prefixLift 3240652
  have htrace : WordTrace (prefixWord ++ tailWord_3240652) baseStart_3240652 baseEnd_3240652 := by
    simpa [prefixWord, tailWord_3240652, baseEnd_3240652] using wordTrace_append hprefix tailTrace_3240652
  have hstable : (prefixWord ++ tailWord_3240652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240652).length < 2 ^ (prefixWord ++ tailWord_3240652).sum := by decide
  have hdescent : baseEnd_3240652 < baseStart_3240652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240685 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 3, 5, 2]
def baseStart_3240685 : Nat := 118140960795 + 3240685 * 2 ^ 59
def prefixEnd_3240685 : Nat := 4983230072969 + 3 ^ 40 * 3240685 * 2
def baseEnd_3240685 : Nat := 1664029054815758538733867

theorem tailTrace_3240685 : CollatzResearch.WordTrace tailWord_3240685 prefixEnd_3240685 1664029054815758538733867 := by
  unfold tailWord_3240685
  simp only [CollatzResearch.WordTrace]
  refine ⟨118197492264559184779515509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78798328176372789853010339 118197492264559184779515509)
  ·
    refine ⟨11081014899802423573079579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118197492264559184779515509 11081014899802423573079579)
    ·
      refine ⟨16621522349703635359619369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11081014899802423573079579 16621522349703635359619369)
      ·
        refine ⟨12466141762277726519714527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16621522349703635359619369 12466141762277726519714527)
        ·
          refine ⟨18699212643416589779571791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12466141762277726519714527 18699212643416589779571791)
          ·
            refine ⟨28048818965124884669357687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18699212643416589779571791 28048818965124884669357687)
            ·
              refine ⟨42073228447687327004036531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28048818965124884669357687 42073228447687327004036531)
              ·
                refine ⟨63109842671530990506054797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42073228447687327004036531 63109842671530990506054797)
                ·
                  refine ⟨23666191001824121439770549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63109842671530990506054797 23666191001824121439770549)
                  ·
                    refine ⟨2218705406421011384978489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23666191001824121439770549 2218705406421011384978489)
                    ·
                      refine ⟨1664029054815758538733867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2218705406421011384978489 1664029054815758538733867)
                      ·
                        rfl

theorem cell23_3240685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_3240685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240685 prefixEnd_3240685 := by exact prefixLift 3240685
  have htrace : WordTrace (prefixWord ++ tailWord_3240685) baseStart_3240685 baseEnd_3240685 := by
    simpa [prefixWord, tailWord_3240685, baseEnd_3240685] using wordTrace_append hprefix tailTrace_3240685
  have hstable : (prefixWord ++ tailWord_3240685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240685).length < 2 ^ (prefixWord ++ tailWord_3240685).sum := by decide
  have hdescent : baseEnd_3240685 < baseStart_3240685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240698 : List Nat := [3, 1, 1, 1, 1, 3, 2, 3, 3, 1, 4]
def baseStart_3240698 : Nat := 118140960795 + 3240698 * 2 ^ 59
def prefixEnd_3240698 : Nat := 4983230072969 + 3 ^ 40 * 3240698 * 2
def baseEnd_3240698 : Nat := 1664035730064266987871307

theorem tailTrace_3240698 : CollatzResearch.WordTrace tailWord_3240698 prefixEnd_3240698 1664035730064266987871307 := by
  unfold tailWord_3240698
  simp only [CollatzResearch.WordTrace]
  refine ⟨29549491603378021999934687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78798644275674725333159165 29549491603378021999934687)
  ·
    refine ⟨44324237405067032999902031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29549491603378021999934687 44324237405067032999902031)
    ·
      refine ⟨66486356107600549499853047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44324237405067032999902031 66486356107600549499853047)
      ·
        refine ⟨99729534161400824249779571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66486356107600549499853047 99729534161400824249779571)
        ·
          refine ⟨149594301242101236374669357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99729534161400824249779571 149594301242101236374669357)
          ·
            refine ⟨56097862965787963640501009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149594301242101236374669357 56097862965787963640501009)
            ·
              refine ⟨42073397224340972730375757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56097862965787963640501009 42073397224340972730375757)
              ·
                refine ⟨15777523959127864773890909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42073397224340972730375757 15777523959127864773890909)
                ·
                  refine ⟨5916571484672949290209091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15777523959127864773890909 5916571484672949290209091)
                  ·
                    refine ⟨8874857227009423935313637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5916571484672949290209091 8874857227009423935313637)
                    ·
                      refine ⟨1664035730064266987871307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8874857227009423935313637 1664035730064266987871307)
                      ·
                        rfl

theorem cell23_3240698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_3240698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240698 prefixEnd_3240698 := by exact prefixLift 3240698
  have htrace : WordTrace (prefixWord ++ tailWord_3240698) baseStart_3240698 baseEnd_3240698 := by
    simpa [prefixWord, tailWord_3240698, baseEnd_3240698] using wordTrace_append hprefix tailTrace_3240698
  have hstable : (prefixWord ++ tailWord_3240698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240698).length < 2 ^ (prefixWord ++ tailWord_3240698).sum := by decide
  have hdescent : baseEnd_3240698 < baseStart_3240698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240702 : List Nat := [4, 2, 2, 1, 2, 1, 2, 1, 1, 5, 2]
def baseStart_3240702 : Nat := 118140960795 + 3240702 * 2 ^ 59
def prefixEnd_3240702 : Nat := 4983230072969 + 3 ^ 40 * 3240702 * 2
def baseEnd_3240702 : Nat := 1664037783986884972221289

theorem tailTrace_3240702 : CollatzResearch.WordTrace tailWord_3240702 prefixEnd_3240702 1664037783986884972221289 := by
  unfold tailWord_3240702
  simp only [CollatzResearch.WordTrace]
  refine ⟨14774764038187199585360545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78798741536998397788589573 14774764038187199585360545)
  ·
    refine ⟨11081073028640399689020409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14774764038187199585360545 11081073028640399689020409)
    ·
      refine ⟨8310804771480299766765307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11081073028640399689020409 8310804771480299766765307)
      ·
        refine ⟨12466207157220449650147961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8310804771480299766765307 12466207157220449650147961)
        ·
          refine ⟨9349655367915337237610971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12466207157220449650147961 9349655367915337237610971)
          ·
            refine ⟨14024483051873005856416457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9349655367915337237610971 14024483051873005856416457)
            ·
              refine ⟨10518362288904754392312343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14024483051873005856416457 10518362288904754392312343)
              ·
                refine ⟨15777543433357131588468515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10518362288904754392312343 15777543433357131588468515)
                ·
                  refine ⟨23666315150035697382702773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15777543433357131588468515 23666315150035697382702773)
                  ·
                    refine ⟨2218717045315846629628385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23666315150035697382702773 2218717045315846629628385)
                    ·
                      refine ⟨1664037783986884972221289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2218717045315846629628385 1664037783986884972221289)
                      ·
                        rfl

theorem cell23_3240702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_3240702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240702 prefixEnd_3240702 := by exact prefixLift 3240702
  have htrace : WordTrace (prefixWord ++ tailWord_3240702) baseStart_3240702 baseEnd_3240702 := by
    simpa [prefixWord, tailWord_3240702, baseEnd_3240702] using wordTrace_append hprefix tailTrace_3240702
  have hstable : (prefixWord ++ tailWord_3240702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240702).length < 2 ^ (prefixWord ++ tailWord_3240702).sum := by decide
  have hdescent : baseEnd_3240702 < baseStart_3240702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240708 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 3, 6]
def baseStart_3240708 : Nat := 118140960795 + 3240708 * 2 ^ 59
def prefixEnd_3240708 : Nat := 4983230072969 + 3 ^ 40 * 3240708 * 2
def baseEnd_3240708 : Nat := 554680288290270649582087

theorem tailTrace_3240708 : CollatzResearch.WordTrace tailWord_3240708 prefixEnd_3240708 554680288290270649582087 := by
  unfold tailWord_3240708
  simp only [CollatzResearch.WordTrace]
  refine ⟨59099165571737929853801389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78798887428983906471735185 59099165571737929853801389)
  ·
    refine ⟨22162187089401723695175521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59099165571737929853801389 22162187089401723695175521)
    ·
      refine ⟨16621640317051292771381641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22162187089401723695175521 16621640317051292771381641)
      ·
        refine ⟨12466230237788469578536231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16621640317051292771381641 12466230237788469578536231)
        ·
          refine ⟨18699345356682704367804347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12466230237788469578536231 18699345356682704367804347)
          ·
            refine ⟨28049018035024056551706521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18699345356682704367804347 28049018035024056551706521)
            ·
              refine ⟨21036763526268042413779891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28049018035024056551706521 21036763526268042413779891)
              ·
                refine ⟨31555145289402063620669837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21036763526268042413779891 31555145289402063620669837)
                ·
                  refine ⟨11833179483525773857751189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31555145289402063620669837 11833179483525773857751189)
                  ·
                    refine ⟨554680288290270649582087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11833179483525773857751189 554680288290270649582087)
                    ·
                      rfl

theorem cell23_3240708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_3240708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240708 prefixEnd_3240708 := by exact prefixLift 3240708
  have htrace : WordTrace (prefixWord ++ tailWord_3240708) baseStart_3240708 baseEnd_3240708 := by
    simpa [prefixWord, tailWord_3240708, baseEnd_3240708] using wordTrace_append hprefix tailTrace_3240708
  have hstable : (prefixWord ++ tailWord_3240708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240708).length < 2 ^ (prefixWord ++ tailWord_3240708).sum := by decide
  have hdescent : baseEnd_3240708 < baseStart_3240708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240721 : List Nat := [1, 2, 2, 1, 1, 3, 13]
def baseStart_3240721 : Nat := 118140960795 + 3240721 * 2 ^ 59
def prefixEnd_3240721 : Nat := 4983230072969 + 3 ^ 40 * 3240721 * 2
def baseEnd_3240721 : Nat := 20543796791596548122021

theorem tailTrace_3240721 : CollatzResearch.WordTrace tailWord_3240721 prefixEnd_3240721 20543796791596548122021 := by
  unfold tailWord_3240721
  simp only [CollatzResearch.WordTrace]
  refine ⟨118198805292428762927826017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78799203528285841951884011 118198805292428762927826017)
  ·
    refine ⟨88649103969321572195869513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118198805292428762927826017 88649103969321572195869513)
    ·
      refine ⟨66486827976991179146902135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88649103969321572195869513 66486827976991179146902135)
      ·
        refine ⟨99730241965486768720353203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66486827976991179146902135 99730241965486768720353203)
        ·
          refine ⟨149595362948230153080529805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99730241965486768720353203 149595362948230153080529805)
          ·
            refine ⟨56098261105586307405198677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149595362948230153080529805 56098261105586307405198677)
            ·
              refine ⟨20543796791596548122021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 56098261105586307405198677 20543796791596548122021)
              ·
                rfl

theorem cell23_3240721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 13].length) (baseStart_3240721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240721 prefixEnd_3240721 := by exact prefixLift 3240721
  have htrace : WordTrace (prefixWord ++ tailWord_3240721) baseStart_3240721 baseEnd_3240721 := by
    simpa [prefixWord, tailWord_3240721, baseEnd_3240721] using wordTrace_append hprefix tailTrace_3240721
  have hstable : (prefixWord ++ tailWord_3240721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240721).length < 2 ^ (prefixWord ++ tailWord_3240721).sum := by decide
  have hdescent : baseEnd_3240721 < baseStart_3240721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240725 : List Nat := [1, 3, 2, 1, 2, 2, 2, 4, 2, 4]
def baseStart_3240725 : Nat := 118140960795 + 3240725 * 2 ^ 59
def prefixEnd_3240725 : Nat := 4983230072969 + 3 ^ 40 * 3240725 * 2
def baseEnd_3240725 : Nat := 554683198013979460744561

theorem tailTrace_3240725 : CollatzResearch.WordTrace tailWord_3240725 prefixEnd_3240725 554683198013979460744561 := by
  unfold tailWord_3240725
  simp only [CollatzResearch.WordTrace]
  refine ⟨118198951184414271610971629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78799300789609514407314419 118198951184414271610971629)
  ·
    refine ⟨44324606694155351854114361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118198951184414271610971629 44324606694155351854114361)
    ·
      refine ⟨33243455020616513890585771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44324606694155351854114361 33243455020616513890585771)
      ·
        refine ⟨49865182530924770835878657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33243455020616513890585771 49865182530924770835878657)
        ·
          refine ⟨37398886898193578126908993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49865182530924770835878657 37398886898193578126908993)
          ·
            refine ⟨28049165173645183595181745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37398886898193578126908993 28049165173645183595181745)
            ·
              refine ⟨21036873880233887696386309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28049165173645183595181745 21036873880233887696386309)
              ·
                refine ⟨3944413852543853943072433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21036873880233887696386309 3944413852543853943072433)
                ·
                  refine ⟨2958310389407890457304325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3944413852543853943072433 2958310389407890457304325)
                  ·
                    refine ⟨554683198013979460744561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2958310389407890457304325 554683198013979460744561)
                    ·
                      rfl

theorem cell23_3240725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_3240725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240725 prefixEnd_3240725 := by exact prefixLift 3240725
  have htrace : WordTrace (prefixWord ++ tailWord_3240725) baseStart_3240725 baseEnd_3240725 := by
    simpa [prefixWord, tailWord_3240725, baseEnd_3240725] using wordTrace_append hprefix tailTrace_3240725
  have hstable : (prefixWord ++ tailWord_3240725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240725).length < 2 ^ (prefixWord ++ tailWord_3240725).sum := by decide
  have hdescent : baseEnd_3240725 < baseStart_3240725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240731 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 7]
def baseStart_3240731 : Nat := 118140960795 + 3240731 * 2 ^ 59
def prefixEnd_3240731 : Nat := 4983230072969 + 3 ^ 40 * 3240731 * 2
def baseEnd_3240731 : Nat := 1664052674925865358758655

theorem tailTrace_3240731 : CollatzResearch.WordTrace tailWord_3240731 prefixEnd_3240731 1664052674925865358758655 := by
  unfold tailWord_3240731
  simp only [CollatzResearch.WordTrace]
  refine ⟨118199170022392534635690047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78799446681595023090460031 118199170022392534635690047)
  ·
    refine ⟨177298755033588801953535071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118199170022392534635690047 177298755033588801953535071)
    ·
      refine ⟨265948132550383202930302607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177298755033588801953535071 265948132550383202930302607)
      ·
        refine ⟨398922198825574804395453911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265948132550383202930302607 398922198825574804395453911)
        ·
          refine ⟨598383298238362206593180867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398922198825574804395453911 598383298238362206593180867)
          ·
            refine ⟨897574947357543309889771301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598383298238362206593180867 897574947357543309889771301)
            ·
              refine ⟨168295302629539370604332119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 897574947357543309889771301 168295302629539370604332119)
              ·
                refine ⟨252442953944309055906498179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168295302629539370604332119 252442953944309055906498179)
                ·
                  refine ⟨378664430916463583859747269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 252442953944309055906498179 378664430916463583859747269)
                  ·
                    refine ⟨70999580796836921973702613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 378664430916463583859747269 70999580796836921973702613)
                    ·
                      refine ⟨1664052674925865358758655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 70999580796836921973702613 1664052674925865358758655)
                      ·
                        rfl

theorem cell23_3240731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 7].length) (baseStart_3240731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240731 prefixEnd_3240731 := by exact prefixLift 3240731
  have htrace : WordTrace (prefixWord ++ tailWord_3240731) baseStart_3240731 baseEnd_3240731 := by
    simpa [prefixWord, tailWord_3240731, baseEnd_3240731] using wordTrace_append hprefix tailTrace_3240731
  have hstable : (prefixWord ++ tailWord_3240731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240731).length < 2 ^ (prefixWord ++ tailWord_3240731).sum := by decide
  have hdescent : baseEnd_3240731 < baseStart_3240731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240738 : List Nat := [3, 3, 1, 1, 2, 2, 1, 10]
def baseStart_3240738 : Nat := 118140960795 + 3240738 * 2 ^ 59
def prefixEnd_3240738 : Nat := 4983230072969 + 3 ^ 40 * 3240738 * 2
def baseEnd_3240738 : Nat := 61631713677423956717449

theorem tailTrace_3240738 : CollatzResearch.WordTrace tailWord_3240738 prefixEnd_3240738 61631713677423956717449 := by
  unfold tailWord_3240738
  simp only [CollatzResearch.WordTrace]
  refine ⟨29549856333341793707798717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78799616888911449887463245 29549856333341793707798717)
  ·
    refine ⟨11081196125003172640424519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29549856333341793707798717 11081196125003172640424519)
    ·
      refine ⟨16621794187504758960636779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11081196125003172640424519 16621794187504758960636779)
      ·
        refine ⟨24932691281257138440955169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16621794187504758960636779 24932691281257138440955169)
        ·
          refine ⟨18699518460942853830716377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24932691281257138440955169 18699518460942853830716377)
          ·
            refine ⟨14024638845707140373037283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18699518460942853830716377 14024638845707140373037283)
            ·
              refine ⟨21036958268560710559555925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14024638845707140373037283 21036958268560710559555925)
              ·
                refine ⟨61631713677423956717449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21036958268560710559555925 61631713677423956717449)
                ·
                  rfl

theorem cell23_3240738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 10].length) (baseStart_3240738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240738 prefixEnd_3240738 := by exact prefixLift 3240738
  have htrace : WordTrace (prefixWord ++ tailWord_3240738) baseStart_3240738 baseEnd_3240738 := by
    simpa [prefixWord, tailWord_3240738, baseEnd_3240738] using wordTrace_append hprefix tailTrace_3240738
  have hstable : (prefixWord ++ tailWord_3240738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240738).length < 2 ^ (prefixWord ++ tailWord_3240738).sum := by decide
  have hdescent : baseEnd_3240738 < baseStart_3240738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240746 : List Nat := [3, 1, 4, 3, 2, 1, 1, 2, 1, 5]
def baseStart_3240746 : Nat := 118140960795 + 3240746 * 2 ^ 59
def prefixEnd_3240746 : Nat := 4983230072969 + 3 ^ 40 * 3240746 * 2
def baseEnd_3240746 : Nat := 554686792378560933357029

theorem tailTrace_3240746 : CollatzResearch.WordTrace tailWord_3240746 prefixEnd_3240746 554686792378560933357029 := by
  unfold tailWord_3240746
  simp only [CollatzResearch.WordTrace]
  refine ⟨29549929279334548049371523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78799811411558794798324061 29549929279334548049371523)
  ·
    refine ⟨44324893919001822074057285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29549929279334548049371523 44324893919001822074057285)
    ·
      refine ⟨8310917609812841638885741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44324893919001822074057285 8310917609812841638885741)
      ·
        refine ⟨3116594103679815614582153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8310917609812841638885741 3116594103679815614582153)
        ·
          refine ⟨2337445577759861710936615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3116594103679815614582153 2337445577759861710936615)
          ·
            refine ⟨3506168366639792566404923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2337445577759861710936615 3506168366639792566404923)
            ·
              refine ⟨5259252549959688849607385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3506168366639792566404923 5259252549959688849607385)
              ·
                refine ⟨3944439412469766637205539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5259252549959688849607385 3944439412469766637205539)
                ·
                  refine ⟨5916659118704649955808309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3944439412469766637205539 5916659118704649955808309)
                  ·
                    refine ⟨554686792378560933357029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5916659118704649955808309 554686792378560933357029)
                    ·
                      rfl

theorem cell23_3240746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_3240746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240746 prefixEnd_3240746 := by exact prefixLift 3240746
  have htrace : WordTrace (prefixWord ++ tailWord_3240746) baseStart_3240746 baseEnd_3240746 := by
    simpa [prefixWord, tailWord_3240746, baseEnd_3240746] using wordTrace_append hprefix tailTrace_3240746
  have hstable : (prefixWord ++ tailWord_3240746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240746).length < 2 ^ (prefixWord ++ tailWord_3240746).sum := by decide
  have hdescent : baseEnd_3240746 < baseStart_3240746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240749 : List Nat := [1, 5, 3, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_3240749 : Nat := 118140960795 + 3240749 * 2 ^ 59
def prefixEnd_3240749 : Nat := 4983230072969 + 3 ^ 40 * 3240749 * 2
def baseEnd_3240749 : Nat := 1664061917577646288333573

theorem tailTrace_3240749 : CollatzResearch.WordTrace tailWord_3240749 prefixEnd_3240749 1664061917577646288333573 := by
  unfold tailWord_3240749
  simp only [CollatzResearch.WordTrace]
  refine ⟨118199826536327323709845301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78799884357551549139896867 118199826536327323709845301)
  ·
    refine ⟨11081233737780686597797997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118199826536327323709845301 11081233737780686597797997)
    ·
      refine ⟨4155462651667757474174249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11081233737780686597797997 4155462651667757474174249)
      ·
        refine ⟨3116596988750818105630687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4155462651667757474174249 3116596988750818105630687)
        ·
          refine ⟨4674895483126227158446031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3116596988750818105630687 4674895483126227158446031)
          ·
            refine ⟨7012343224689340737669047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4674895483126227158446031 7012343224689340737669047)
            ·
              refine ⟨10518514837034011106503571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7012343224689340737669047 10518514837034011106503571)
              ·
                refine ⟨15777772255551016659755357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10518514837034011106503571 15777772255551016659755357)
                ·
                  refine ⟨5916664595831631247408259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15777772255551016659755357 5916664595831631247408259)
                  ·
                    refine ⟨8874996893747446871112389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5916664595831631247408259 8874996893747446871112389)
                    ·
                      refine ⟨1664061917577646288333573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8874996893747446871112389 1664061917577646288333573)
                      ·
                        rfl

theorem cell23_3240749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_3240749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240749 prefixEnd_3240749 := by exact prefixLift 3240749
  have htrace : WordTrace (prefixWord ++ tailWord_3240749) baseStart_3240749 baseEnd_3240749 := by
    simpa [prefixWord, tailWord_3240749, baseEnd_3240749] using wordTrace_append hprefix tailTrace_3240749
  have hstable : (prefixWord ++ tailWord_3240749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240749).length < 2 ^ (prefixWord ++ tailWord_3240749).sum := by decide
  have hdescent : baseEnd_3240749 < baseStart_3240749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240769 : List Nat := [1, 2, 5, 3, 1, 2, 1, 1, 1, 1, 5]
def baseStart_3240769 : Nat := 118140960795 + 3240769 * 2 ^ 59
def prefixEnd_3240769 : Nat := 4983230072969 + 3 ^ 40 * 3240769 * 2
def baseEnd_3240769 : Nat := 1664072187190736210083481

theorem tailTrace_3240769 : CollatzResearch.WordTrace tailWord_3240769 prefixEnd_3240769 1664072187190736210083481 := by
  unfold tailWord_3240769
  simp only [CollatzResearch.WordTrace]
  refine ⟨118200555996254867125573361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78800370664169911417048907 118200555996254867125573361)
  ·
    refine ⟨88650416997191150344180021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118200555996254867125573361 88650416997191150344180021)
    ·
      refine ⟨8310976593486670344766877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88650416997191150344180021 8310976593486670344766877)
      ·
        refine ⟨3116616222557501379287579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8310976593486670344766877 3116616222557501379287579)
        ·
          refine ⟨4674924333836252068931369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3116616222557501379287579 4674924333836252068931369)
          ·
            refine ⟨3506193250377189051698527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4674924333836252068931369 3506193250377189051698527)
            ·
              refine ⟨5259289875565783577547791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3506193250377189051698527 5259289875565783577547791)
              ·
                refine ⟨7888934813348675366321687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5259289875565783577547791 7888934813348675366321687)
                ·
                  refine ⟨11833402220023013049482531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7888934813348675366321687 11833402220023013049482531)
                  ·
                    refine ⟨17750103330034519574223797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11833402220023013049482531 17750103330034519574223797)
                    ·
                      refine ⟨1664072187190736210083481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17750103330034519574223797 1664072187190736210083481)
                      ·
                        rfl

theorem cell23_3240769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_3240769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240769 prefixEnd_3240769 := by exact prefixLift 3240769
  have htrace : WordTrace (prefixWord ++ tailWord_3240769) baseStart_3240769 baseEnd_3240769 := by
    simpa [prefixWord, tailWord_3240769, baseEnd_3240769] using wordTrace_append hprefix tailTrace_3240769
  have hstable : (prefixWord ++ tailWord_3240769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240769).length < 2 ^ (prefixWord ++ tailWord_3240769).sum := by decide
  have hdescent : baseEnd_3240769 < baseStart_3240769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240772 : List Nat := [2, 3, 4, 2, 2, 10]
def baseStart_3240772 : Nat := 118140960795 + 3240772 * 2 ^ 59
def prefixEnd_3240772 : Nat := 4983230072969 + 3 ^ 40 * 3240772 * 2
def baseEnd_3240772 : Nat := 6848040031410286824469

theorem tailTrace_3240772 : CollatzResearch.WordTrace tailWord_3240772 prefixEnd_3240772 6848040031410286824469 := by
  unfold tailWord_3240772
  simp only [CollatzResearch.WordTrace]
  refine ⟨59100332707621999318966285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78800443610162665758621713 59100332707621999318966285)
  ·
    refine ⟨22162624765358249744612357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59100332707621999318966285 22162624765358249744612357)
    ·
      refine ⟨4155492143504671827114817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22162624765358249744612357 4155492143504671827114817)
      ·
        refine ⟨3116619107628503870336113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4155492143504671827114817 3116619107628503870336113)
        ·
          refine ⟨2337464330721377902752085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3116619107628503870336113 2337464330721377902752085)
          ·
            refine ⟨6848040031410286824469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2337464330721377902752085 6848040031410286824469)
            ·
              rfl

theorem cell23_3240772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 10].length) (baseStart_3240772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240772 prefixEnd_3240772 := by exact prefixLift 3240772
  have htrace : WordTrace (prefixWord ++ tailWord_3240772) baseStart_3240772 baseEnd_3240772 := by
    simpa [prefixWord, tailWord_3240772, baseEnd_3240772] using wordTrace_append hprefix tailTrace_3240772
  have hstable : (prefixWord ++ tailWord_3240772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240772).length < 2 ^ (prefixWord ++ tailWord_3240772).sum := by decide
  have hdescent : baseEnd_3240772 < baseStart_3240772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240839 : List Nat := [1, 1, 4, 2, 3, 2, 1, 1, 4, 2, 2]
def baseStart_3240839 : Nat := 118140960795 + 3240839 * 2 ^ 59
def prefixEnd_3240839 : Nat := 4983230072969 + 3 ^ 40 * 3240839 * 2
def baseEnd_3240839 : Nat := 1664108130836550936208159

theorem tailTrace_3240839 : CollatzResearch.WordTrace tailWord_3240839 prefixEnd_3240839 1664108130836550936208159 := by
  unfold tailWord_3240839
  simp only [CollatzResearch.WordTrace]
  refine ⟨118203109106001269080621571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78802072737334179387081047 118203109106001269080621571)
  ·
    refine ⟨177304663659001903620932357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118203109106001269080621571 177304663659001903620932357)
    ·
      refine ⟨33244624436062856928924817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177304663659001903620932357 33244624436062856928924817)
      ·
        refine ⟨24933468327047142696693613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33244624436062856928924817 24933468327047142696693613)
        ·
          refine ⟨9350050622642678511260105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24933468327047142696693613 9350050622642678511260105)
          ·
            refine ⟨7012537966982008883445079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9350050622642678511260105 7012537966982008883445079)
            ·
              refine ⟨10518806950473013325167619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7012537966982008883445079 10518806950473013325167619)
              ·
                refine ⟨15778210425709519987751429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10518806950473013325167619 15778210425709519987751429)
                ·
                  refine ⟨2958414454820534997703393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15778210425709519987751429 2958414454820534997703393)
                  ·
                    refine ⟨2218810841115401248277545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2958414454820534997703393 2218810841115401248277545)
                    ·
                      refine ⟨1664108130836550936208159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2218810841115401248277545 1664108130836550936208159)
                      ·
                        rfl

theorem cell23_3240839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_3240839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240839 prefixEnd_3240839 := by exact prefixLift 3240839
  have htrace : WordTrace (prefixWord ++ tailWord_3240839) baseStart_3240839 baseEnd_3240839 := by
    simpa [prefixWord, tailWord_3240839, baseEnd_3240839] using wordTrace_append hprefix tailTrace_3240839
  have hstable : (prefixWord ++ tailWord_3240839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240839).length < 2 ^ (prefixWord ++ tailWord_3240839).sum := by decide
  have hdescent : baseEnd_3240839 < baseStart_3240839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240855 : List Nat := [1, 1, 3, 3, 1, 2, 1, 3, 2, 3, 3]
def baseStart_3240855 : Nat := 118140960795 + 3240855 * 2 ^ 59
def prefixEnd_3240855 : Nat := 4983230072969 + 3 ^ 40 * 3240855 * 2
def baseEnd_3240855 : Nat := 1664116346527022873608085

theorem tailTrace_3240855 : CollatzResearch.WordTrace tailWord_3240855 prefixEnd_3240855 1664116346527022873608085 := by
  unfold tailWord_3240855
  simp only [CollatzResearch.WordTrace]
  refine ⟨118203692673943303813204019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78802461782628869208802679 118203692673943303813204019)
  ·
    refine ⟨177305539010914955719806029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118203692673943303813204019 177305539010914955719806029)
    ·
      refine ⟨66489577129093108394927261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177305539010914955719806029 66489577129093108394927261)
      ·
        refine ⟨24933591423409915648097723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66489577129093108394927261 24933591423409915648097723)
        ·
          refine ⟨37400387135114873472146585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24933591423409915648097723 37400387135114873472146585)
          ·
            refine ⟨28050290351336155104109939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37400387135114873472146585 28050290351336155104109939)
            ·
              refine ⟨42075435527004232656164909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28050290351336155104109939 42075435527004232656164909)
              ·
                refine ⟨15778288322626587246061841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42075435527004232656164909 15778288322626587246061841)
                ·
                  refine ⟨11833716241969940434546381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15778288322626587246061841 11833716241969940434546381)
                  ·
                    refine ⟨4437643590738727662954893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11833716241969940434546381 4437643590738727662954893)
                    ·
                      refine ⟨1664116346527022873608085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4437643590738727662954893 1664116346527022873608085)
                      ·
                        rfl

theorem cell23_3240855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_3240855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240855 prefixEnd_3240855 := by exact prefixLift 3240855
  have htrace : WordTrace (prefixWord ++ tailWord_3240855) baseStart_3240855 baseEnd_3240855 := by
    simpa [prefixWord, tailWord_3240855, baseEnd_3240855] using wordTrace_append hprefix tailTrace_3240855
  have hstable : (prefixWord ++ tailWord_3240855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240855).length < 2 ^ (prefixWord ++ tailWord_3240855).sum := by decide
  have hdescent : baseEnd_3240855 < baseStart_3240855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240885 : List Nat := [1, 3, 3, 2, 1, 1, 2, 2, 1, 2, 5]
def baseStart_3240885 : Nat := 118140960795 + 3240885 * 2 ^ 59
def prefixEnd_3240885 : Nat := 4983230072969 + 3 ^ 40 * 3240885 * 2
def baseEnd_3240885 : Nat := 1664131750946657756232947

theorem tailTrace_3240885 : CollatzResearch.WordTrace tailWord_3240885 prefixEnd_3240885 1664131750946657756232947 := by
  unfold tailWord_3240885
  simp only [CollatzResearch.WordTrace]
  refine ⟨118204786863834618936796109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78803191242556412624530739 118204786863834618936796109)
  ·
    refine ⟨44326795073937982101298541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118204786863834618936796109 44326795073937982101298541)
    ·
      refine ⟨16622548152726743287986953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44326795073937982101298541 16622548152726743287986953)
      ·
        refine ⟨12466911114545057465990215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16622548152726743287986953 12466911114545057465990215)
        ·
          refine ⟨18700366671817586198985323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12466911114545057465990215 18700366671817586198985323)
          ·
            refine ⟨28050550007726379298477985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18700366671817586198985323 28050550007726379298477985)
            ·
              refine ⟨21037912505794784473858489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28050550007726379298477985 21037912505794784473858489)
              ·
                refine ⟨15778434379346088355393867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21037912505794784473858489 15778434379346088355393867)
                ·
                  refine ⟨23667651569019132533090801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15778434379346088355393867 23667651569019132533090801)
                  ·
                    refine ⟨17750738676764349399818101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23667651569019132533090801 17750738676764349399818101)
                    ·
                      refine ⟨1664131750946657756232947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17750738676764349399818101 1664131750946657756232947)
                      ·
                        rfl

theorem cell23_3240885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_3240885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240885 prefixEnd_3240885 := by exact prefixLift 3240885
  have htrace : WordTrace (prefixWord ++ tailWord_3240885) baseStart_3240885 baseEnd_3240885 := by
    simpa [prefixWord, tailWord_3240885, baseEnd_3240885] using wordTrace_append hprefix tailTrace_3240885
  have hstable : (prefixWord ++ tailWord_3240885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240885).length < 2 ^ (prefixWord ++ tailWord_3240885).sum := by decide
  have hdescent : baseEnd_3240885 < baseStart_3240885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240956 : List Nat := [2, 2, 2, 1, 2, 3, 4, 2, 1, 4]
def baseStart_3240956 : Nat := 118140960795 + 3240956 * 2 ^ 59
def prefixEnd_3240956 : Nat := 4983230072969 + 3 ^ 40 * 3240956 * 2
def baseEnd_3240956 : Nat := 554722736024375659481707

theorem tailTrace_3240956 : CollatzResearch.WordTrace tailWord_3240956 prefixEnd_3240956 554722736024375659481707 := by
  unfold tailWord_3240956
  simp only [CollatzResearch.WordTrace]
  refine ⟨59103688223288699031315361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78804917631051598708420481 59103688223288699031315361)
  ·
    refine ⟨44327766167466524273486521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59103688223288699031315361 44327766167466524273486521)
    ·
      refine ⟨33245824625599893205114891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44327766167466524273486521 33245824625599893205114891)
      ·
        refine ⟨49868736938399839807672337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33245824625599893205114891 49868736938399839807672337)
        ·
          refine ⟨37401552703799879855754253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49868736938399839807672337 37401552703799879855754253)
          ·
            refine ⟨14025582263924954945907845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37401552703799879855754253 14025582263924954945907845)
            ·
              refine ⟨2629796674485929052357721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14025582263924954945907845 2629796674485929052357721)
              ·
                refine ⟨1972347505864446789268291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2629796674485929052357721 1972347505864446789268291)
                ·
                  refine ⟨2958521258796670183902437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1972347505864446789268291 2958521258796670183902437)
                  ·
                    refine ⟨554722736024375659481707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2958521258796670183902437 554722736024375659481707)
                    ·
                      rfl

theorem cell23_3240956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_3240956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240956 prefixEnd_3240956 := by exact prefixLift 3240956
  have htrace : WordTrace (prefixWord ++ tailWord_3240956) baseStart_3240956 baseEnd_3240956 := by
    simpa [prefixWord, tailWord_3240956, baseEnd_3240956] using wordTrace_append hprefix tailTrace_3240956
  have hstable : (prefixWord ++ tailWord_3240956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240956).length < 2 ^ (prefixWord ++ tailWord_3240956).sum := by decide
  have hdescent : baseEnd_3240956 < baseStart_3240956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240965 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 5, 5]
def baseStart_3240965 : Nat := 118140960795 + 3240965 * 2 ^ 59
def prefixEnd_3240965 : Nat := 4983230072969 + 3 ^ 40 * 3240965 * 2
def baseEnd_3240965 : Nat := 554724276466339147744193

theorem tailTrace_3240965 : CollatzResearch.WordTrace tailWord_3240965 prefixEnd_3240965 554724276466339147744193 := by
  unfold tailWord_3240965
  simp only [CollatzResearch.WordTrace]
  refine ⟨118207704703544792599708349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78805136469029861733138899 118207704703544792599708349)
  ·
    refine ⟨44327889263829297224890631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118207704703544792599708349 44327889263829297224890631)
    ·
      refine ⟨66491833895743945837335947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44327889263829297224890631 66491833895743945837335947)
      ·
        refine ⟨99737750843615918756003921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66491833895743945837335947 99737750843615918756003921)
        ·
          refine ⟨74803313132711939067002941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99737750843615918756003921 74803313132711939067002941)
          ·
            refine ⟨28051242424766977150126103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74803313132711939067002941 28051242424766977150126103)
            ·
              refine ⟨42076863637150465725189155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28051242424766977150126103 42076863637150465725189155)
              ·
                refine ⟨63115295455725698587783733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42076863637150465725189155 63115295455725698587783733)
                ·
                  refine ⟨5917058948974284242604725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63115295455725698587783733 5917058948974284242604725)
                  ·
                    refine ⟨554724276466339147744193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5917058948974284242604725 554724276466339147744193)
                    ·
                      rfl

theorem cell23_3240965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 5].length) (baseStart_3240965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3240965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3240965 prefixEnd_3240965 := by exact prefixLift 3240965
  have htrace : WordTrace (prefixWord ++ tailWord_3240965) baseStart_3240965 baseEnd_3240965 := by
    simpa [prefixWord, tailWord_3240965, baseEnd_3240965] using wordTrace_append hprefix tailTrace_3240965
  have hstable : (prefixWord ++ tailWord_3240965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240965).length < 2 ^ (prefixWord ++ tailWord_3240965).sum := by decide
  have hdescent : baseEnd_3240965 < baseStart_3240965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241015 : List Nat := [1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 6]
def baseStart_3241015 : Nat := 118140960795 + 3241015 * 2 ^ 59
def prefixEnd_3241015 : Nat := 4983230072969 + 3 ^ 40 * 3241015 * 2
def baseEnd_3241015 : Nat := 1664198503431742247607349

theorem tailTrace_3241015 : CollatzResearch.WordTrace tailWord_3241015 prefixEnd_3241015 1664198503431742247607349 := by
  unfold tailWord_3241015
  simp only [CollatzResearch.WordTrace]
  refine ⟨118209528353363651139028499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78806352235575767426018999 118209528353363651139028499)
  ·
    refine ⟨177314292530045476708542749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118209528353363651139028499 177314292530045476708542749)
    ·
      refine ⟨66492859698767053765703531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177314292530045476708542749 66492859698767053765703531)
      ·
        refine ⟨99739289548150580648555297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66492859698767053765703531 99739289548150580648555297)
        ·
          refine ⟨74804467161112935486416473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99739289548150580648555297 74804467161112935486416473)
          ·
            refine ⟨56103350370834701614812355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74804467161112935486416473 56103350370834701614812355)
            ·
              refine ⟨84155025556252052422218533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56103350370834701614812355 84155025556252052422218533)
              ·
                refine ⟨15779067291797259829165975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84155025556252052422218533 15779067291797259829165975)
                ·
                  refine ⟨23668600937695889743748963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15779067291797259829165975 23668600937695889743748963)
                  ·
                    refine ⟨35502901406543834615623445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23668600937695889743748963 35502901406543834615623445)
                    ·
                      refine ⟨1664198503431742247607349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35502901406543834615623445 1664198503431742247607349)
                      ·
                        rfl

theorem cell23_3241015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_3241015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241015 prefixEnd_3241015 := by exact prefixLift 3241015
  have htrace : WordTrace (prefixWord ++ tailWord_3241015) baseStart_3241015 baseEnd_3241015 := by
    simpa [prefixWord, tailWord_3241015, baseEnd_3241015] using wordTrace_append hprefix tailTrace_3241015
  have hstable : (prefixWord ++ tailWord_3241015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241015).length < 2 ^ (prefixWord ++ tailWord_3241015).sum := by decide
  have hdescent : baseEnd_3241015 < baseStart_3241015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241042 : List Nat := [3, 2, 2, 1, 3, 2, 1, 9]
def baseStart_3241042 : Nat := 118140960795 + 3241042 * 2 ^ 59
def prefixEnd_3241042 : Nat := 4983230072969 + 3 ^ 40 * 3241042 * 2
def baseEnd_3241042 : Nat := 61637495089237542295175

theorem tailTrace_3241042 : CollatzResearch.WordTrace tailWord_3241042 prefixEnd_3241042 61637495089237542295175 := by
  unfold tailWord_3241042
  simp only [CollatzResearch.WordTrace]
  refine ⟨29552628281066458687565345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78807008749510556500174253 29552628281066458687565345)
  ·
    refine ⟨22164471210799844015674009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29552628281066458687565345 22164471210799844015674009)
    ·
      refine ⟨16623353408099883011755507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22164471210799844015674009 16623353408099883011755507)
      ·
        refine ⟨24935030112149824517633261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16623353408099883011755507 24935030112149824517633261)
        ·
          refine ⟨9350636292056184194112473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24935030112149824517633261 9350636292056184194112473)
          ·
            refine ⟨7012977219042138145584355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9350636292056184194112473 7012977219042138145584355)
            ·
              refine ⟨10519465828563207218376533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7012977219042138145584355 10519465828563207218376533)
              ·
                refine ⟨61637495089237542295175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10519465828563207218376533 61637495089237542295175)
                ·
                  rfl

theorem cell23_3241042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 9].length) (baseStart_3241042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241042 prefixEnd_3241042 := by exact prefixLift 3241042
  have htrace : WordTrace (prefixWord ++ tailWord_3241042) baseStart_3241042 baseEnd_3241042 := by
    simpa [prefixWord, tailWord_3241042, baseEnd_3241042] using wordTrace_append hprefix tailTrace_3241042
  have hstable : (prefixWord ++ tailWord_3241042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241042).length < 2 ^ (prefixWord ++ tailWord_3241042).sum := by decide
  have hdescent : baseEnd_3241042 < baseStart_3241042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241079 : List Nat := [1, 1, 3, 1, 1, 4, 2, 2, 3, 3, 2]
def baseStart_3241079 : Nat := 118140960795 + 3241079 * 2 ^ 59
def prefixEnd_3241079 : Nat := 4983230072969 + 3 ^ 40 * 3241079 * 2
def baseEnd_3241079 : Nat := 1664231366193629997207055

theorem tailTrace_3241079 : CollatzResearch.WordTrace tailWord_3241079 prefixEnd_3241079 1664231366193629997207055 := by
  unfold tailWord_3241079
  simp only [CollatzResearch.WordTrace]
  refine ⟨118211862625131790069358291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78807908416754526712905527 118211862625131790069358291)
  ·
    refine ⟨177317793937697685104037437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118211862625131790069358291 177317793937697685104037437)
    ·
      refine ⟨66494172726636631914014039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177317793937697685104037437 66494172726636631914014039)
      ·
        refine ⟨99741259089954947871021059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66494172726636631914014039 99741259089954947871021059)
        ·
          refine ⟨149611888634932421806531589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99741259089954947871021059 149611888634932421806531589)
          ·
            refine ⟨28052229119049829088724673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149611888634932421806531589 28052229119049829088724673)
            ·
              refine ⟨21039171839287371816543505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28052229119049829088724673 21039171839287371816543505)
              ·
                refine ⟨15779378879465528862407629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21039171839287371816543505 15779378879465528862407629)
                ·
                  refine ⟨5917267079799573323402861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15779378879465528862407629 5917267079799573323402861)
                  ·
                    refine ⟨2218975154924839996276073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5917267079799573323402861 2218975154924839996276073)
                    ·
                      refine ⟨1664231366193629997207055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2218975154924839996276073 1664231366193629997207055)
                      ·
                        rfl

theorem cell23_3241079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 3, 2].length) (baseStart_3241079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241079 prefixEnd_3241079 := by exact prefixLift 3241079
  have htrace : WordTrace (prefixWord ++ tailWord_3241079) baseStart_3241079 baseEnd_3241079 := by
    simpa [prefixWord, tailWord_3241079, baseEnd_3241079] using wordTrace_append hprefix tailTrace_3241079
  have hstable : (prefixWord ++ tailWord_3241079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241079).length < 2 ^ (prefixWord ++ tailWord_3241079).sum := by decide
  have hdescent : baseEnd_3241079 < baseStart_3241079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241209 : List Nat := [1, 2, 1, 3, 1, 1, 3, 4, 3, 4]
def baseStart_3241209 : Nat := 118140960795 + 3241209 * 2 ^ 59
def prefixEnd_3241209 : Nat := 4983230072969 + 3 ^ 40 * 3241209 * 2
def baseEnd_3241209 : Nat := 554766039559571496193819

theorem tailTrace_3241209 : CollatzResearch.WordTrace tailWord_3241209 prefixEnd_3241209 554766039559571496193819 := by
  unfold tailWord_3241209
  simp only [CollatzResearch.WordTrace]
  refine ⟨118216604114660822271590681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78811069409773881514393787 118216604114660822271590681)
  ·
    refine ⟨88662453085995616703693011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118216604114660822271590681 88662453085995616703693011)
    ·
      refine ⟨132993679628993425055539517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88662453085995616703693011 132993679628993425055539517)
      ·
        refine ⟨49872629860872534395827319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132993679628993425055539517 49872629860872534395827319)
        ·
          refine ⟨74808944791308801593740979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49872629860872534395827319 74808944791308801593740979)
          ·
            refine ⟨112213417186963202390611469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74808944791308801593740979 112213417186963202390611469)
            ·
              refine ⟨42080031445111200896479301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112213417186963202390611469 42080031445111200896479301)
              ·
                refine ⟨7890005895958350168089869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42080031445111200896479301 7890005895958350168089869)
                ·
                  refine ⟨2958752210984381313033701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7890005895958350168089869 2958752210984381313033701)
                  ·
                    refine ⟨554766039559571496193819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2958752210984381313033701 554766039559571496193819)
                    ·
                      rfl

theorem cell23_3241209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 3, 4].length) (baseStart_3241209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241209 prefixEnd_3241209 := by exact prefixLift 3241209
  have htrace : WordTrace (prefixWord ++ tailWord_3241209) baseStart_3241209 baseEnd_3241209 := by
    simpa [prefixWord, tailWord_3241209, baseEnd_3241209] using wordTrace_append hprefix tailTrace_3241209
  have hstable : (prefixWord ++ tailWord_3241209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241209).length < 2 ^ (prefixWord ++ tailWord_3241209).sum := by decide
  have hdescent : baseEnd_3241209 < baseStart_3241209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241219 : List Nat := [1, 1, 1, 3, 2, 4, 2, 1, 1, 4, 3]
def baseStart_3241219 : Nat := 118140960795 + 3241219 * 2 ^ 59
def prefixEnd_3241219 : Nat := 4983230072969 + 3 ^ 40 * 3241219 * 2
def baseEnd_3241219 : Nat := 1664303253485259449456411

theorem tailTrace_3241219 : CollatzResearch.WordTrace tailWord_3241219 prefixEnd_3241219 1664303253485259449456411 := by
  unfold tailWord_3241219
  simp only [CollatzResearch.WordTrace]
  refine ⟨118216968844624593979454711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78811312563083062652969807 118216968844624593979454711)
  ·
    refine ⟨177325453266936890969182067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118216968844624593979454711 177325453266936890969182067)
    ·
      refine ⟨265988179900405336453773101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177325453266936890969182067 265988179900405336453773101)
      ·
        refine ⟨99745567462652001170164913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265988179900405336453773101 99745567462652001170164913)
        ·
          refine ⟨74809175596989000877623685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99745567462652001170164913 74809175596989000877623685)
          ·
            refine ⟨14026720424435437664554441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74809175596989000877623685 14026720424435437664554441)
            ·
              refine ⟨10520040318326578248415831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14026720424435437664554441 10520040318326578248415831)
              ·
                refine ⟨15780060477489867372623747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10520040318326578248415831 15780060477489867372623747)
                ·
                  refine ⟨23670090716234801058935621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15780060477489867372623747 23670090716234801058935621)
                  ·
                    refine ⟨4438142009294025198550429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23670090716234801058935621 4438142009294025198550429)
                    ·
                      refine ⟨1664303253485259449456411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4438142009294025198550429 1664303253485259449456411)
                      ·
                        rfl

theorem cell23_3241219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 4, 3].length) (baseStart_3241219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241219 prefixEnd_3241219 := by exact prefixLift 3241219
  have htrace : WordTrace (prefixWord ++ tailWord_3241219) baseStart_3241219 baseEnd_3241219 := by
    simpa [prefixWord, tailWord_3241219, baseEnd_3241219] using wordTrace_append hprefix tailTrace_3241219
  have hstable : (prefixWord ++ tailWord_3241219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241219).length < 2 ^ (prefixWord ++ tailWord_3241219).sum := by decide
  have hdescent : baseEnd_3241219 < baseStart_3241219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241239 : List Nat := [1, 1, 3, 4, 1, 1, 2, 4, 6]
def baseStart_3241239 : Nat := 118140960795 + 3241239 * 2 ^ 59
def prefixEnd_3241239 : Nat := 4983230072969 + 3 ^ 40 * 3241239 * 2
def baseEnd_3241239 : Nat := 184923724788705485689591

theorem tailTrace_3241239 : CollatzResearch.WordTrace tailWord_3241239 prefixEnd_3241239 184923724788705485689591 := by
  unfold tailWord_3241239
  simp only [CollatzResearch.WordTrace]
  refine ⟨118217698304552137395182771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78811798869701424930121847 118217698304552137395182771)
  ·
    refine ⟨177326547456828206092774157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118217698304552137395182771 177326547456828206092774157)
    ·
      refine ⟨66497455296310577284790309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177326547456828206092774157 66497455296310577284790309)
      ·
        refine ⟨12468272868058233240898183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66497455296310577284790309 12468272868058233240898183)
        ·
          refine ⟨18702409302087349861347275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12468272868058233240898183 18702409302087349861347275)
          ·
            refine ⟨28053613953131024792020913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18702409302087349861347275 28053613953131024792020913)
            ·
              refine ⟨21040210464848268594015685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28053613953131024792020913 21040210464848268594015685)
              ·
                refine ⟨3945039462159050361377941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21040210464848268594015685 3945039462159050361377941)
                ·
                  refine ⟨184923724788705485689591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3945039462159050361377941 184923724788705485689591)
                  ·
                    rfl

theorem cell23_3241239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 6].length) (baseStart_3241239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241239 prefixEnd_3241239 := by exact prefixLift 3241239
  have htrace : WordTrace (prefixWord ++ tailWord_3241239) baseStart_3241239 baseEnd_3241239 := by
    simpa [prefixWord, tailWord_3241239, baseEnd_3241239] using wordTrace_append hprefix tailTrace_3241239
  have hstable : (prefixWord ++ tailWord_3241239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241239).length < 2 ^ (prefixWord ++ tailWord_3241239).sum := by decide
  have hdescent : baseEnd_3241239 < baseStart_3241239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241256 : List Nat := [2, 1, 5, 1, 2, 2, 1, 3, 6]
def baseStart_3241256 : Nat := 118140960795 + 3241256 * 2 ^ 59
def prefixEnd_3241256 : Nat := 4983230072969 + 3 ^ 40 * 3241256 * 2
def baseEnd_3241256 : Nat := 184924694696608422743749

theorem tailTrace_3241256 : CollatzResearch.WordTrace tailWord_3241256 prefixEnd_3241256 184924694696608422743749 := by
  unfold tailWord_3241256
  simp only [CollatzResearch.WordTrace]
  refine ⟨59109159172745274649275811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78812212230327032865701081 59109159172745274649275811)
  ·
    refine ⟨88663738759117911973913717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59109159172745274649275811 88663738759117911973913717)
    ·
      refine ⟨8312225508667304247554411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88663738759117911973913717 8312225508667304247554411)
      ·
        refine ⟨12468338263000956371331617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8312225508667304247554411 12468338263000956371331617)
        ·
          refine ⟨9351253697250717278498713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12468338263000956371331617 9351253697250717278498713)
          ·
            refine ⟨7013440272938037958874035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9351253697250717278498713 7013440272938037958874035)
            ·
              refine ⟨10520160409407056938311053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7013440272938037958874035 10520160409407056938311053)
              ·
                refine ⟨3945060153527646351866645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10520160409407056938311053 3945060153527646351866645)
                ·
                  refine ⟨184924694696608422743749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3945060153527646351866645 184924694696608422743749)
                  ·
                    rfl

theorem cell23_3241256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 6].length) (baseStart_3241256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241256 prefixEnd_3241256 := by exact prefixLift 3241256
  have htrace : WordTrace (prefixWord ++ tailWord_3241256) baseStart_3241256 baseEnd_3241256 := by
    simpa [prefixWord, tailWord_3241256, baseEnd_3241256] using wordTrace_append hprefix tailTrace_3241256
  have hstable : (prefixWord ++ tailWord_3241256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241256).length < 2 ^ (prefixWord ++ tailWord_3241256).sum := by decide
  have hdescent : baseEnd_3241256 < baseStart_3241256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241283 : List Nat := [1, 1, 1, 3, 1, 3, 1, 7, 1, 1, 3]
def baseStart_3241283 : Nat := 118140960795 + 3241283 * 2 ^ 59
def prefixEnd_3241283 : Nat := 4983230072969 + 3 ^ 40 * 3241283 * 2
def baseEnd_3241283 : Nat := 1664336116247147199056117

theorem tailTrace_3241283 : CollatzResearch.WordTrace tailWord_3241283 prefixEnd_3241283 1664336116247147199056117 := by
  unfold tailWord_3241283
  simp only [CollatzResearch.WordTrace]
  refine ⟨118219303116392732909784503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78812868744261821939856335 118219303116392732909784503)
  ·
    refine ⟨177328954674589099364676755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118219303116392732909784503 177328954674589099364676755)
    ·
      refine ⟨265993432011883649047015133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177328954674589099364676755 265993432011883649047015133)
      ·
        refine ⟨99747537004456368392630675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265993432011883649047015133 99747537004456368392630675)
        ·
          refine ⟨149621305506684552588946013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99747537004456368392630675 149621305506684552588946013)
          ·
            refine ⟨56107989565006707220854755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149621305506684552588946013 56107989565006707220854755)
            ·
              refine ⟨84161984347510060831282133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56107989565006707220854755 84161984347510060831282133)
              ·
                refine ⟨1972546508144767050733175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 84161984347510060831282133 1972546508144767050733175)
                ·
                  refine ⟨2958819762217150576099763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1972546508144767050733175 2958819762217150576099763)
                  ·
                    refine ⟨4438229643325725864149645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2958819762217150576099763 4438229643325725864149645)
                    ·
                      refine ⟨1664336116247147199056117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4438229643325725864149645 1664336116247147199056117)
                      ·
                        rfl

theorem cell23_3241283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 7, 1, 1, 3].length) (baseStart_3241283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241283 prefixEnd_3241283 := by exact prefixLift 3241283
  have htrace : WordTrace (prefixWord ++ tailWord_3241283) baseStart_3241283 baseEnd_3241283 := by
    simpa [prefixWord, tailWord_3241283, baseEnd_3241283] using wordTrace_append hprefix tailTrace_3241283
  have hstable : (prefixWord ++ tailWord_3241283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241283).length < 2 ^ (prefixWord ++ tailWord_3241283).sum := by decide
  have hdescent : baseEnd_3241283 < baseStart_3241283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241300 : List Nat := [2, 4, 1, 1, 2, 1, 3, 4, 1, 1, 3]
def baseStart_3241300 : Nat := 118140960795 + 3241300 * 2 ^ 59
def prefixEnd_3241300 : Nat := 4983230072969 + 3 ^ 40 * 3241300 * 2
def baseEnd_3241300 : Nat := 1664344845418273632543539

theorem tailTrace_3241300 : CollatzResearch.WordTrace tailWord_3241300 prefixEnd_3241300 1664344845418273632543539 := by
  unfold tailWord_3241300
  simp only [CollatzResearch.WordTrace]
  refine ⟨59109961578665572406576677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78813282104887429875435569 59109961578665572406576677)
  ·
    refine ⟨11083117795999794826233127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59109961578665572406576677 11083117795999794826233127)
    ·
      refine ⟨16624676693999692239349691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11083117795999794826233127 16624676693999692239349691)
      ·
        refine ⟨24937015040999538359024537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16624676693999692239349691 24937015040999538359024537)
        ·
          refine ⟨18702761280749653769268403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24937015040999538359024537 18702761280749653769268403)
          ·
            refine ⟨28054141921124480653902605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18702761280749653769268403 28054141921124480653902605)
            ·
              refine ⟨10520303220421680245213477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28054141921124480653902605 10520303220421680245213477)
              ·
                refine ⟨1972556853829065045977527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10520303220421680245213477 1972556853829065045977527)
                ·
                  refine ⟨2958835280743597568966291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1972556853829065045977527 2958835280743597568966291)
                  ·
                    refine ⟨4438252921115396353449437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2958835280743597568966291 4438252921115396353449437)
                    ·
                      refine ⟨1664344845418273632543539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4438252921115396353449437 1664344845418273632543539)
                      ·
                        rfl

theorem cell23_3241300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_3241300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241300 prefixEnd_3241300 := by exact prefixLift 3241300
  have htrace : WordTrace (prefixWord ++ tailWord_3241300) baseStart_3241300 baseEnd_3241300 := by
    simpa [prefixWord, tailWord_3241300, baseEnd_3241300] using wordTrace_append hprefix tailTrace_3241300
  have hstable : (prefixWord ++ tailWord_3241300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241300).length < 2 ^ (prefixWord ++ tailWord_3241300).sum := by decide
  have hdescent : baseEnd_3241300 < baseStart_3241300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241316 : List Nat := [2, 3, 1, 1, 3, 3, 2, 1, 1, 6]
def baseStart_3241316 : Nat := 118140960795 + 3241316 * 2 ^ 59
def prefixEnd_3241316 : Nat := 4983230072969 + 3 ^ 40 * 3241316 * 2
def baseEnd_3241316 : Nat := 554784353702915189981155

theorem tailTrace_3241316 : CollatzResearch.WordTrace tailWord_3241316 prefixEnd_3241316 554784353702915189981155 := by
  unfold tailWord_3241316
  simp only [CollatzResearch.WordTrace]
  refine ⟨59110253362636589772867901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78813671150182119697157201 59110253362636589772867901)
  ·
    refine ⟨22166345010988721164825463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59110253362636589772867901 22166345010988721164825463)
    ·
      refine ⟨33249517516483081747238195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22166345010988721164825463 33249517516483081747238195)
      ·
        refine ⟨49874276274724622620857293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33249517516483081747238195 49874276274724622620857293)
        ·
          refine ⟨18702853603021733482821485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49874276274724622620857293 18702853603021733482821485)
          ·
            refine ⟨7013570101133150056058057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18702853603021733482821485 7013570101133150056058057)
            ·
              refine ⟨5260177575849862542043543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7013570101133150056058057 5260177575849862542043543)
              ·
                refine ⟨7890266363774793813065315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5260177575849862542043543 7890266363774793813065315)
                ·
                  refine ⟨11835399545662190719597973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7890266363774793813065315 11835399545662190719597973)
                  ·
                    refine ⟨554784353702915189981155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11835399545662190719597973 554784353702915189981155)
                    ·
                      rfl

theorem cell23_3241316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_3241316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241316 prefixEnd_3241316 := by exact prefixLift 3241316
  have htrace : WordTrace (prefixWord ++ tailWord_3241316) baseStart_3241316 baseEnd_3241316 := by
    simpa [prefixWord, tailWord_3241316, baseEnd_3241316] using wordTrace_append hprefix tailTrace_3241316
  have hstable : (prefixWord ++ tailWord_3241316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241316).length < 2 ^ (prefixWord ++ tailWord_3241316).sum := by decide
  have hdescent : baseEnd_3241316 < baseStart_3241316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241373 : List Nat := [1, 4, 2, 1, 3, 1, 3, 1, 1, 3, 3]
def baseStart_3241373 : Nat := 118140960795 + 3241373 * 2 ^ 59
def prefixEnd_3241373 : Nat := 4983230072969 + 3 ^ 40 * 3241373 * 2
def baseEnd_3241373 : Nat := 1664382329506051846930703

theorem tailTrace_3241373 : CollatzResearch.WordTrace tailWord_3241373 prefixEnd_3241373 1664382329506051846930703 := by
  unfold tailWord_3241373
  simp only [CollatzResearch.WordTrace]
  refine ⟨118222585686066678280560773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78815057124044452187040515 118222585686066678280560773)
  ·
    refine ⟨22166734816137502177605145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118222585686066678280560773 22166734816137502177605145)
    ·
      refine ⟨16625051112103126633203859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22166734816137502177605145 16625051112103126633203859)
      ·
        refine ⟨24937576668154689949805789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16625051112103126633203859 24937576668154689949805789)
        ·
          refine ⟨9351591250558008731177171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24937576668154689949805789 9351591250558008731177171)
          ·
            refine ⟨14027386875837013096765757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9351591250558008731177171 14027386875837013096765757)
            ·
              refine ⟨5260270078438879911287159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14027386875837013096765757 5260270078438879911287159)
              ·
                refine ⟨7890405117658319866930739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5260270078438879911287159 7890405117658319866930739)
                ·
                  refine ⟨11835607676487479800396109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7890405117658319866930739 11835607676487479800396109)
                  ·
                    refine ⟨4438352878682804925148541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11835607676487479800396109 4438352878682804925148541)
                    ·
                      refine ⟨1664382329506051846930703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4438352878682804925148541 1664382329506051846930703)
                      ·
                        rfl

theorem cell23_3241373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_3241373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241373 prefixEnd_3241373 := by exact prefixLift 3241373
  have htrace : WordTrace (prefixWord ++ tailWord_3241373) baseStart_3241373 baseEnd_3241373 := by
    simpa [prefixWord, tailWord_3241373, baseEnd_3241373] using wordTrace_append hprefix tailTrace_3241373
  have hstable : (prefixWord ++ tailWord_3241373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241373).length < 2 ^ (prefixWord ++ tailWord_3241373).sum := by decide
  have hdescent : baseEnd_3241373 < baseStart_3241373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241416 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 2, 4, 3]
def baseStart_3241416 : Nat := 118140960795 + 3241416 * 2 ^ 59
def prefixEnd_3241416 : Nat := 4983230072969 + 3 ^ 40 * 3241416 * 2
def baseEnd_3241416 : Nat := 1664404409174195178693005

theorem tailTrace_3241416 : CollatzResearch.WordTrace tailWord_3241416 prefixEnd_3241416 1664404409174195178693005 := by
  unfold tailWord_3241416
  simp only [CollatzResearch.WordTrace]
  refine ⟨59112077012455448312188051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78816102683273931082917401 59112077012455448312188051)
  ·
    refine ⟨88668115518683172468282077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59112077012455448312188051 88668115518683172468282077)
    ·
      refine ⟨33250543319506189675605779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88668115518683172468282077 33250543319506189675605779)
      ·
        refine ⟨49875814979259284513408669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33250543319506189675605779 49875814979259284513408669)
        ·
          refine ⟨18703430617222231692528251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49875814979259284513408669 18703430617222231692528251)
          ·
            refine ⟨28055145925833347538792377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18703430617222231692528251 28055145925833347538792377)
            ·
              refine ⟨21041359444375010654094283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28055145925833347538792377 21041359444375010654094283)
              ·
                refine ⟨31562039166562515981141425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21041359444375010654094283 31562039166562515981141425)
                ·
                  refine ⟨23671529374921886985856069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31562039166562515981141425 23671529374921886985856069)
                  ·
                    refine ⟨4438411757797853809848013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23671529374921886985856069 4438411757797853809848013)
                    ·
                      refine ⟨1664404409174195178693005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4438411757797853809848013 1664404409174195178693005)
                      ·
                        rfl

theorem cell23_3241416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_3241416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241416 prefixEnd_3241416 := by exact prefixLift 3241416
  have htrace : WordTrace (prefixWord ++ tailWord_3241416) baseStart_3241416 baseEnd_3241416 := by
    simpa [prefixWord, tailWord_3241416, baseEnd_3241416] using wordTrace_append hprefix tailTrace_3241416
  have hstable : (prefixWord ++ tailWord_3241416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241416).length < 2 ^ (prefixWord ++ tailWord_3241416).sum := by decide
  have hdescent : baseEnd_3241416 < baseStart_3241416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241449 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 5, 7]
def baseStart_3241449 : Nat := 118140960795 + 3241449 * 2 ^ 59
def prefixEnd_3241449 : Nat := 4983230072969 + 3 ^ 40 * 3241449 * 2
def baseEnd_3241449 : Nat := 554807118011931183193451

theorem tailTrace_3241449 : CollatzResearch.WordTrace tailWord_3241449 prefixEnd_3241449 554807118011931183193451 := by
  unfold tailWord_3241449
  simp only [CollatzResearch.WordTrace]
  refine ⟨118225357633791343260327401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78816905089194228840218267 118225357633791343260327401)
  ·
    refine ⟨88669018225343507445245551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118225357633791343260327401 88669018225343507445245551)
    ·
      refine ⟨133003527338015261167868327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88669018225343507445245551 133003527338015261167868327)
      ·
        refine ⟨199505291007022891751802491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133003527338015261167868327 199505291007022891751802491)
        ·
          refine ⟨299257936510534337627703737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199505291007022891751802491 299257936510534337627703737)
          ·
            refine ⟨224443452382900753220777803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299257936510534337627703737 224443452382900753220777803)
            ·
              refine ⟨336665178574351129831166705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224443452382900753220777803 336665178574351129831166705)
              ·
                refine ⟨252498883930763347373375029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 336665178574351129831166705 252498883930763347373375029)
                ·
                  refine ⟨23671770368509063816253909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 252498883930763347373375029 23671770368509063816253909)
                  ·
                    refine ⟨554807118011931183193451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23671770368509063816253909 554807118011931183193451)
                    ·
                      rfl

theorem cell23_3241449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 7].length) (baseStart_3241449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241449 prefixEnd_3241449 := by exact prefixLift 3241449
  have htrace : WordTrace (prefixWord ++ tailWord_3241449) baseStart_3241449 baseEnd_3241449 := by
    simpa [prefixWord, tailWord_3241449, baseEnd_3241449] using wordTrace_append hprefix tailTrace_3241449
  have hstable : (prefixWord ++ tailWord_3241449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241449).length < 2 ^ (prefixWord ++ tailWord_3241449).sum := by decide
  have hdescent : baseEnd_3241449 < baseStart_3241449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241466 : List Nat := [3, 1, 1, 1, 1, 2, 3, 4, 2, 5]
def baseStart_3241466 : Nat := 118140960795 + 3241466 * 2 ^ 59
def prefixEnd_3241466 : Nat := 4983230072969 + 3 ^ 40 * 3241466 * 2
def baseEnd_3241466 : Nat := 554810027735639994355925

theorem tailTrace_3241466 : CollatzResearch.WordTrace tailWord_3241466 prefixEnd_3241466 554810027735639994355925 := by
  unfold tailWord_3241466
  simp only [CollatzResearch.WordTrace]
  refine ⟨29556494418682438790924063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78817318449819836775797501 29556494418682438790924063)
  ·
    refine ⟨44334741628023658186386095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29556494418682438790924063 44334741628023658186386095)
    ·
      refine ⟨66502112442035487279579143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44334741628023658186386095 66502112442035487279579143)
      ·
        refine ⟨99753168663053230919368715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66502112442035487279579143 99753168663053230919368715)
        ·
          refine ⟨149629752994579846379053073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99753168663053230919368715 149629752994579846379053073)
          ·
            refine ⟨112222314745934884784289805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149629752994579846379053073 112222314745934884784289805)
            ·
              refine ⟨42083368029725581794108677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112222314745934884784289805 42083368029725581794108677)
              ·
                refine ⟨7890631505573546586395377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42083368029725581794108677 7890631505573546586395377)
                ·
                  refine ⟨5917973629180159939796533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7890631505573546586395377 5917973629180159939796533)
                  ·
                    refine ⟨554810027735639994355925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5917973629180159939796533 554810027735639994355925)
                    ·
                      rfl

theorem cell23_3241466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 2, 5].length) (baseStart_3241466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241466 prefixEnd_3241466 := by exact prefixLift 3241466
  have htrace : WordTrace (prefixWord ++ tailWord_3241466) baseStart_3241466 baseEnd_3241466 := by
    simpa [prefixWord, tailWord_3241466, baseEnd_3241466] using wordTrace_append hprefix tailTrace_3241466
  have hstable : (prefixWord ++ tailWord_3241466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241466).length < 2 ^ (prefixWord ++ tailWord_3241466).sum := by decide
  have hdescent : baseEnd_3241466 < baseStart_3241466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241503 : List Nat := [1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 4]
def baseStart_3241503 : Nat := 118140960795 + 3241503 * 2 ^ 59
def prefixEnd_3241503 : Nat := 4983230072969 + 3 ^ 40 * 3241503 * 2
def baseEnd_3241503 : Nat := 1664449081991136338305105

theorem tailTrace_3241503 : CollatzResearch.WordTrace tailWord_3241503 prefixEnd_3241503 1664449081991136338305105 := by
  unfold tailWord_3241503
  simp only [CollatzResearch.WordTrace]
  refine ⟨118227327175595710482793163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78818218117063806988528775 118227327175595710482793163)
  ·
    refine ⟨177340990763393565724189745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118227327175595710482793163 177340990763393565724189745)
    ·
      refine ⟨133005743072545174293142309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177340990763393565724189745 133005743072545174293142309)
      ·
        refine ⟨24938576826102220179964183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133005743072545174293142309 24938576826102220179964183)
        ·
          refine ⟨37407865239153330269946275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24938576826102220179964183 37407865239153330269946275)
          ·
            refine ⟨56111797858729995404919413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37407865239153330269946275 56111797858729995404919413)
            ·
              refine ⟨5260481049255937069211195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56111797858729995404919413 5260481049255937069211195)
              ·
                refine ⟨7890721573883905603816793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5260481049255937069211195 7890721573883905603816793)
                ·
                  refine ⟨5918041180412929202862595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7890721573883905603816793 5918041180412929202862595)
                  ·
                    refine ⟨8877061770619393804293893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5918041180412929202862595 8877061770619393804293893)
                    ·
                      refine ⟨1664449081991136338305105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8877061770619393804293893 1664449081991136338305105)
                      ·
                        rfl

theorem cell23_3241503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_3241503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241503 prefixEnd_3241503 := by exact prefixLift 3241503
  have htrace : WordTrace (prefixWord ++ tailWord_3241503) baseStart_3241503 baseEnd_3241503 := by
    simpa [prefixWord, tailWord_3241503, baseEnd_3241503] using wordTrace_append hprefix tailTrace_3241503
  have hstable : (prefixWord ++ tailWord_3241503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241503).length < 2 ^ (prefixWord ++ tailWord_3241503).sum := by decide
  have hdescent : baseEnd_3241503 < baseStart_3241503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241530 : List Nat := [3, 1, 1, 1, 3, 2, 1, 6, 1, 4]
def baseStart_3241530 : Nat := 118140960795 + 3241530 * 2 ^ 59
def prefixEnd_3241530 : Nat := 4983230072969 + 3 ^ 40 * 3241530 * 2
def baseEnd_3241530 : Nat := 554820981989602577555827

theorem tailTrace_3241530 : CollatzResearch.WordTrace tailWord_3241530 prefixEnd_3241530 554820981989602577555827 := by
  unfold tailWord_3241530
  simp only [CollatzResearch.WordTrace]
  refine ⟨29557077986624473523506511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78818874630998596062684029 29557077986624473523506511)
  ·
    refine ⟨44335616979936710285259767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29557077986624473523506511 44335616979936710285259767)
    ·
      refine ⟨66503425469905065427889651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44335616979936710285259767 66503425469905065427889651)
      ·
        refine ⟨99755138204857598141834477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66503425469905065427889651 99755138204857598141834477)
        ·
          refine ⟨37408176826821599303187929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99755138204857598141834477 37408176826821599303187929)
          ·
            refine ⟨28056132620116199477390947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37408176826821599303187929 28056132620116199477390947)
            ·
              refine ⟨42084198930174299216086421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28056132620116199477390947 42084198930174299216086421)
              ·
                refine ⟨1972696824851920275754051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42084198930174299216086421 1972696824851920275754051)
                ·
                  refine ⟨2959045237277880413631077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1972696824851920275754051 2959045237277880413631077)
                  ·
                    refine ⟨554820981989602577555827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2959045237277880413631077 554820981989602577555827)
                    ·
                      rfl

theorem cell23_3241530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 6, 1, 4].length) (baseStart_3241530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241530 prefixEnd_3241530 := by exact prefixLift 3241530
  have htrace : WordTrace (prefixWord ++ tailWord_3241530) baseStart_3241530 baseEnd_3241530 := by
    simpa [prefixWord, tailWord_3241530, baseEnd_3241530] using wordTrace_append hprefix tailTrace_3241530
  have hstable : (prefixWord ++ tailWord_3241530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241530).length < 2 ^ (prefixWord ++ tailWord_3241530).sum := by decide
  have hdescent : baseEnd_3241530 < baseStart_3241530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241546 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 1, 2, 6]
def baseStart_3241546 : Nat := 118140960795 + 3241546 * 2 ^ 59
def prefixEnd_3241546 : Nat := 4983230072969 + 3 ^ 40 * 3241546 * 2
def baseEnd_3241546 : Nat := 1664471161659279670067407

theorem tailTrace_3241546 : CollatzResearch.WordTrace tailWord_3241546 prefixEnd_3241546 1664471161659279670067407 := by
  unfold tailWord_3241546
  simp only [CollatzResearch.WordTrace]
  refine ⟨29557223878609982206652123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78819263676293285884405661 29557223878609982206652123)
  ·
    refine ⟨44335835817914973309978185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29557223878609982206652123 44335835817914973309978185)
    ·
      refine ⟨33251876863436229982483639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44335835817914973309978185 33251876863436229982483639)
      ·
        refine ⟨49877815295154344973725459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33251876863436229982483639 49877815295154344973725459)
        ·
          refine ⟨74816722942731517460588189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49877815295154344973725459 74816722942731517460588189)
          ·
            refine ⟨28056271103524319047720571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74816722942731517460588189 28056271103524319047720571)
            ·
              refine ⟨42084406655286478571580857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28056271103524319047720571 42084406655286478571580857)
              ·
                refine ⟨31563304991464858928685643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42084406655286478571580857 31563304991464858928685643)
                ·
                  refine ⟨47344957487197288393028465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31563304991464858928685643 47344957487197288393028465)
                  ·
                    refine ⟨35508718115397966294771349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47344957487197288393028465 35508718115397966294771349)
                    ·
                      refine ⟨1664471161659279670067407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35508718115397966294771349 1664471161659279670067407)
                      ·
                        rfl

theorem cell23_3241546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_3241546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241546 prefixEnd_3241546 := by exact prefixLift 3241546
  have htrace : WordTrace (prefixWord ++ tailWord_3241546) baseStart_3241546 baseEnd_3241546 := by
    simpa [prefixWord, tailWord_3241546, baseEnd_3241546] using wordTrace_append hprefix tailTrace_3241546
  have hstable : (prefixWord ++ tailWord_3241546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241546).length < 2 ^ (prefixWord ++ tailWord_3241546).sum := by decide
  have hdescent : baseEnd_3241546 < baseStart_3241546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241564 : List Nat := [2, 2, 4, 1, 2, 3, 1, 3, 1, 4]
def baseStart_3241564 : Nat := 118140960795 + 3241564 * 2 ^ 59
def prefixEnd_3241564 : Nat := 4983230072969 + 3 ^ 40 * 3241564 * 2
def baseEnd_3241564 : Nat := 554826801437020199880775

theorem tailTrace_3241564 : CollatzResearch.WordTrace tailWord_3241564 prefixEnd_3241564 554826801437020199880775 := by
  unfold tailWord_3241564
  simp only [CollatzResearch.WordTrace]
  refine ⟨59114776014187358950381873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78819701352249811933842497 59114776014187358950381873)
  ·
    refine ⟨44336082010640519212786405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59114776014187358950381873 44336082010640519212786405)
    ·
      refine ⟨8313015376995097352397451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44336082010640519212786405 8313015376995097352397451)
      ·
        refine ⟨12469523065492646028596177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8313015376995097352397451 12469523065492646028596177)
        ·
          refine ⟨9352142299119484521447133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12469523065492646028596177 9352142299119484521447133)
          ·
            refine ⟨3507053362169806695542675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9352142299119484521447133 3507053362169806695542675)
            ·
              refine ⟨5260580043254710043314013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3507053362169806695542675 5260580043254710043314013)
              ·
                refine ⟨1972717516220516266242755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5260580043254710043314013 1972717516220516266242755)
                ·
                  refine ⟨2959076274330774399364133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1972717516220516266242755 2959076274330774399364133)
                  ·
                    refine ⟨554826801437020199880775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2959076274330774399364133 554826801437020199880775)
                    ·
                      rfl

theorem cell23_3241564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_3241564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241564 prefixEnd_3241564 := by exact prefixLift 3241564
  have htrace : WordTrace (prefixWord ++ tailWord_3241564) baseStart_3241564 baseEnd_3241564 := by
    simpa [prefixWord, tailWord_3241564, baseEnd_3241564] using wordTrace_append hprefix tailTrace_3241564
  have hstable : (prefixWord ++ tailWord_3241564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241564).length < 2 ^ (prefixWord ++ tailWord_3241564).sum := by decide
  have hdescent : baseEnd_3241564 < baseStart_3241564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241593 : List Nat := [1, 2, 1, 3, 3, 1, 2, 2, 3, 1, 4]
def baseStart_3241593 : Nat := 118140960795 + 3241593 * 2 ^ 59
def prefixEnd_3241593 : Nat := 4983230072969 + 3 ^ 40 * 3241593 * 2
def baseEnd_3241593 : Nat := 1664495295250040986179691

theorem tailTrace_3241593 : CollatzResearch.WordTrace tailWord_3241593 prefixEnd_3241593 1664495295250040986179691 := by
  unfold tailWord_3241593
  simp only [CollatzResearch.WordTrace]
  refine ⟨118230609745269655853569433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78820406496846437235712955 118230609745269655853569433)
  ·
    refine ⟨88672957308952241890177075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118230609745269655853569433 88672957308952241890177075)
    ·
      refine ⟨133009435963428362835265613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88672957308952241890177075 133009435963428362835265613)
      ·
        refine ⟨49878538486285636063224605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133009435963428362835265613 49878538486285636063224605)
        ·
          refine ⟨18704451932357113523709227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49878538486285636063224605 18704451932357113523709227)
          ·
            refine ⟨28056677898535670285563841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18704451932357113523709227 28056677898535670285563841)
            ·
              refine ⟨21042508423901752714172881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28056677898535670285563841 21042508423901752714172881)
              ·
                refine ⟨15781881317926314535629661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21042508423901752714172881 15781881317926314535629661)
                ·
                  refine ⟨5918205494222367950861123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15781881317926314535629661 5918205494222367950861123)
                  ·
                    refine ⟨8877308241333551926291685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5918205494222367950861123 8877308241333551926291685)
                    ·
                      refine ⟨1664495295250040986179691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8877308241333551926291685 1664495295250040986179691)
                      ·
                        rfl

theorem cell23_3241593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_3241593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241593 prefixEnd_3241593 := by exact prefixLift 3241593
  have htrace : WordTrace (prefixWord ++ tailWord_3241593) baseStart_3241593 baseEnd_3241593 := by
    simpa [prefixWord, tailWord_3241593, baseEnd_3241593] using wordTrace_append hprefix tailTrace_3241593
  have hstable : (prefixWord ++ tailWord_3241593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241593).length < 2 ^ (prefixWord ++ tailWord_3241593).sum := by decide
  have hdescent : baseEnd_3241593 < baseStart_3241593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241610 : List Nat := [3, 1, 2, 3, 2, 2, 1, 1, 3, 1, 4]
def baseStart_3241610 : Nat := 118140960795 + 3241610 * 2 ^ 59
def prefixEnd_3241610 : Nat := 4983230072969 + 3 ^ 40 * 3241610 * 2
def baseEnd_3241610 : Nat := 1664504024421167419667113

theorem tailTrace_3241610 : CollatzResearch.WordTrace tailWord_3241610 prefixEnd_3241610 1664504024421167419667113 := by
  unfold tailWord_3241610
  simp only [CollatzResearch.WordTrace]
  refine ⟨29557807446552016939234571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78820819857472045171292189 29557807446552016939234571)
  ·
    refine ⟨44336711169828025408851857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29557807446552016939234571 44336711169828025408851857)
    ·
      refine ⟨33252533377371019056638893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44336711169828025408851857 33252533377371019056638893)
      ·
        refine ⟨12469700016514132146239585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33252533377371019056638893 12469700016514132146239585)
        ·
          refine ⟨9352275012385599109679689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12469700016514132146239585 9352275012385599109679689)
          ·
            refine ⟨7014206259289199332259767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9352275012385599109679689 7014206259289199332259767)
            ·
              refine ⟨10521309388933798998389651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7014206259289199332259767 10521309388933798998389651)
              ·
                refine ⟨15781964083400698497584477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10521309388933798998389651 15781964083400698497584477)
                ·
                  refine ⟨5918236531275261936594179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15781964083400698497584477 5918236531275261936594179)
                  ·
                    refine ⟨8877354796912892904891269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5918236531275261936594179 8877354796912892904891269)
                    ·
                      refine ⟨1664504024421167419667113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8877354796912892904891269 1664504024421167419667113)
                      ·
                        rfl

theorem cell23_3241610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_3241610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241610 prefixEnd_3241610 := by exact prefixLift 3241610
  have htrace : WordTrace (prefixWord ++ tailWord_3241610) baseStart_3241610 baseEnd_3241610 := by
    simpa [prefixWord, tailWord_3241610, baseEnd_3241610] using wordTrace_append hprefix tailTrace_3241610
  have hstable : (prefixWord ++ tailWord_3241610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241610).length < 2 ^ (prefixWord ++ tailWord_3241610).sum := by decide
  have hdescent : baseEnd_3241610 < baseStart_3241610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241623 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 4]
def baseStart_3241623 : Nat := 118140960795 + 3241623 * 2 ^ 59
def prefixEnd_3241623 : Nat := 4983230072969 + 3 ^ 40 * 3241623 * 2
def baseEnd_3241623 : Nat := 1664510699669675868804553

theorem tailTrace_3241623 : CollatzResearch.WordTrace tailWord_3241623 prefixEnd_3241623 1664510699669675868804553 := by
  unfold tailWord_3241623
  simp only [CollatzResearch.WordTrace]
  refine ⟨118231703935160970977161523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78821135956773980651441015 118231703935160970977161523)
  ·
    refine ⟨177347555902741456465742285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118231703935160970977161523 177347555902741456465742285)
    ·
      refine ⟨66505333463528046174653357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177347555902741456465742285 66505333463528046174653357)
      ·
        refine ⟨24939500048823017315495009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66505333463528046174653357 24939500048823017315495009)
        ·
          refine ⟨18704625036617262986621257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24939500048823017315495009 18704625036617262986621257)
          ·
            refine ⟨14028468777462947239965943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18704625036617262986621257 14028468777462947239965943)
            ·
              refine ⟨21042703166194420859948915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14028468777462947239965943 21042703166194420859948915)
              ·
                refine ⟨31564054749291631289923373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21042703166194420859948915 31564054749291631289923373)
                ·
                  refine ⟨11836520530984361733721265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31564054749291631289923373 11836520530984361733721265)
                  ·
                    refine ⟨8877390398238271300290949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11836520530984361733721265 8877390398238271300290949)
                    ·
                      refine ⟨1664510699669675868804553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8877390398238271300290949 1664510699669675868804553)
                      ·
                        rfl

theorem cell23_3241623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_3241623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241623 prefixEnd_3241623 := by exact prefixLift 3241623
  have htrace : WordTrace (prefixWord ++ tailWord_3241623) baseStart_3241623 baseEnd_3241623 := by
    simpa [prefixWord, tailWord_3241623, baseEnd_3241623] using wordTrace_append hprefix tailTrace_3241623
  have hstable : (prefixWord ++ tailWord_3241623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241623).length < 2 ^ (prefixWord ++ tailWord_3241623).sum := by decide
  have hdescent : baseEnd_3241623 < baseStart_3241623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241654 : List Nat := [5, 1, 3, 1, 1, 1, 2, 3, 2, 4]
def baseStart_3241654 : Nat := 118140960795 + 3241654 * 2 ^ 59
def prefixEnd_3241654 : Nat := 4983230072969 + 3 ^ 40 * 3241654 * 2
def baseEnd_3241654 : Nat := 554842205856655082505637

theorem tailTrace_3241654 : CollatzResearch.WordTrace tailWord_3241654 prefixEnd_3241654 554842205856655082505637 := by
  unfold tailWord_3241654
  simp only [CollatzResearch.WordTrace]
  refine ⟨7389552162378041454471251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78821889732032442181026677 7389552162378041454471251)
  ·
    refine ⟨11084328243567062181706877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7389552162378041454471251 11084328243567062181706877)
    ·
      refine ⟨4156623091337648318140079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11084328243567062181706877 4156623091337648318140079)
      ·
        refine ⟨6234934637006472477210119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4156623091337648318140079 6234934637006472477210119)
        ·
          refine ⟨9352401955509708715815179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6234934637006472477210119 9352401955509708715815179)
          ·
            refine ⟨14028602933264563073722769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9352401955509708715815179 14028602933264563073722769)
            ·
              refine ⟨10521452199948422305292077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14028602933264563073722769 10521452199948422305292077)
              ·
                refine ⟨3945544574980658364484529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10521452199948422305292077 3945544574980658364484529)
                ·
                  refine ⟨2959158431235493773363397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3945544574980658364484529 2959158431235493773363397)
                  ·
                    refine ⟨554842205856655082505637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2959158431235493773363397 554842205856655082505637)
                    ·
                      rfl

theorem cell23_3241654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_3241654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241654 prefixEnd_3241654 := by exact prefixLift 3241654
  have htrace : WordTrace (prefixWord ++ tailWord_3241654) baseStart_3241654 baseEnd_3241654 := by
    simpa [prefixWord, tailWord_3241654, baseEnd_3241654] using wordTrace_append hprefix tailTrace_3241654
  have hstable : (prefixWord ++ tailWord_3241654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241654).length < 2 ^ (prefixWord ++ tailWord_3241654).sum := by decide
  have hdescent : baseEnd_3241654 < baseStart_3241654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241660 : List Nat := [2, 2, 2, 3, 1, 2, 1, 3, 1, 3, 3]
def baseStart_3241660 : Nat := 118140960795 + 3241660 * 2 ^ 59
def prefixEnd_3241660 : Nat := 4983230072969 + 3 ^ 40 * 3241660 * 2
def baseEnd_3241660 : Nat := 1664529698453892224041883

theorem tailTrace_3241660 : CollatzResearch.WordTrace tailWord_3241660 prefixEnd_3241660 1664529698453892224041883 := by
  unfold tailWord_3241660
  simp only [CollatzResearch.WordTrace]
  refine ⟨59116526718013463148129217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78822035624017950864172289 59116526718013463148129217)
  ·
    refine ⟨44337395038510097361096913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59116526718013463148129217 44337395038510097361096913)
    ·
      refine ⟨33253046278882573020822685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44337395038510097361096913 33253046278882573020822685)
      ·
        refine ⟨12469892354580964882808507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33253046278882573020822685 12469892354580964882808507)
        ·
          refine ⟨18704838531871447324212761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12469892354580964882808507 18704838531871447324212761)
          ·
            refine ⟨14028628898903585493159571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18704838531871447324212761 14028628898903585493159571)
            ·
              refine ⟨21042943348355378239739357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14028628898903585493159571 21042943348355378239739357)
              ·
                refine ⟨7891103755633266839902259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21042943348355378239739357 7891103755633266839902259)
                ·
                  refine ⟨11836655633449900259853389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7891103755633266839902259 11836655633449900259853389)
                  ·
                    refine ⟨4438745862543712597445021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11836655633449900259853389 4438745862543712597445021)
                    ·
                      refine ⟨1664529698453892224041883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4438745862543712597445021 1664529698453892224041883)
                      ·
                        rfl

theorem cell23_3241660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_3241660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241660 prefixEnd_3241660 := by exact prefixLift 3241660
  have htrace : WordTrace (prefixWord ++ tailWord_3241660) baseStart_3241660 baseEnd_3241660 := by
    simpa [prefixWord, tailWord_3241660, baseEnd_3241660] using wordTrace_append hprefix tailTrace_3241660
  have hstable : (prefixWord ++ tailWord_3241660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241660).length < 2 ^ (prefixWord ++ tailWord_3241660).sum := by decide
  have hdescent : baseEnd_3241660 < baseStart_3241660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241687 : List Nat := [1, 1, 3, 2, 1, 3, 3, 3, 1, 3, 2]
def baseStart_3241687 : Nat := 118140960795 + 3241687 * 2 ^ 59
def prefixEnd_3241687 : Nat := 4983230072969 + 3 ^ 40 * 3241687 * 2
def baseEnd_3241687 : Nat := 1664543562431563618404259

theorem tailTrace_3241687 : CollatzResearch.WordTrace tailWord_3241687 prefixEnd_3241687 1664543562431563618404259 := by
  unfold tailWord_3241687
  simp only [CollatzResearch.WordTrace]
  refine ⟨118234038206929109907491315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78822692137952739938327543 118234038206929109907491315)
  ·
    refine ⟨177351057310393664861236973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118234038206929109907491315 177351057310393664861236973)
    ·
      refine ⟨66506646491397624322963865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177351057310393664861236973 66506646491397624322963865)
      ·
        refine ⟨49879984868548218242222899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66506646491397624322963865 49879984868548218242222899)
        ·
          refine ⟨74819977302822327363334349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49879984868548218242222899 74819977302822327363334349)
          ·
            refine ⟨28057491488558372761250381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74819977302822327363334349 28057491488558372761250381)
            ·
              refine ⟨10521559308209389785468893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28057491488558372761250381 10521559308209389785468893)
              ·
                refine ⟨3945584740578521169550835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10521559308209389785468893 3945584740578521169550835)
                ·
                  refine ⟨5918377110867781754326253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3945584740578521169550835 5918377110867781754326253)
                  ·
                    refine ⟨2219391416575418157872345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5918377110867781754326253 2219391416575418157872345)
                    ·
                      refine ⟨1664543562431563618404259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2219391416575418157872345 1664543562431563618404259)
                      ·
                        rfl

theorem cell23_3241687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 3, 2].length) (baseStart_3241687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241687 prefixEnd_3241687 := by exact prefixLift 3241687
  have htrace : WordTrace (prefixWord ++ tailWord_3241687) baseStart_3241687 baseEnd_3241687 := by
    simpa [prefixWord, tailWord_3241687, baseEnd_3241687] using wordTrace_append hprefix tailTrace_3241687
  have hstable : (prefixWord ++ tailWord_3241687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241687).length < 2 ^ (prefixWord ++ tailWord_3241687).sum := by decide
  have hdescent : baseEnd_3241687 < baseStart_3241687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241763 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 7]
def baseStart_3241763 : Nat := 118140960795 + 3241763 * 2 ^ 59
def prefixEnd_3241763 : Nat := 4983230072969 + 3 ^ 40 * 3241763 * 2
def baseEnd_3241763 : Nat := 1664582586961305321053909

theorem tailTrace_3241763 : CollatzResearch.WordTrace tailWord_3241763 prefixEnd_3241763 1664582586961305321053909 := by
  unfold tailWord_3241763
  simp only [CollatzResearch.WordTrace]
  refine ⟨118236810154653774887257943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78824540103102516591505295 118236810154653774887257943)
  ·
    refine ⟨177355215231980662330886915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118236810154653774887257943 177355215231980662330886915)
    ·
      refine ⟨266032822847970993496330373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177355215231980662330886915 266032822847970993496330373)
      ·
        refine ⟨49881154283994561280561945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 266032822847970993496330373 49881154283994561280561945)
        ·
          refine ⟨37410865712995920960421459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49881154283994561280561945 37410865712995920960421459)
          ·
            refine ⟨56116298569493881440632189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37410865712995920960421459 56116298569493881440632189)
            ·
              refine ⟨21043611963560205540237071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56116298569493881440632189 21043611963560205540237071)
              ·
                refine ⟨31565417945340308310355607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21043611963560205540237071 31565417945340308310355607)
                ·
                  refine ⟨47348126918010462465533411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31565417945340308310355607 47348126918010462465533411)
                  ·
                    refine ⟨71022190377015693698300117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47348126918010462465533411 71022190377015693698300117)
                    ·
                      refine ⟨1664582586961305321053909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 71022190377015693698300117 1664582586961305321053909)
                      ·
                        rfl

theorem cell23_3241763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_3241763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241763 prefixEnd_3241763 := by exact prefixLift 3241763
  have htrace : WordTrace (prefixWord ++ tailWord_3241763) baseStart_3241763 baseEnd_3241763 := by
    simpa [prefixWord, tailWord_3241763, baseEnd_3241763] using wordTrace_append hprefix tailTrace_3241763
  have hstable : (prefixWord ++ tailWord_3241763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241763).length < 2 ^ (prefixWord ++ tailWord_3241763).sum := by decide
  have hdescent : baseEnd_3241763 < baseStart_3241763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241768 : List Nat := [2, 1, 5, 1, 1, 4, 2, 1, 2, 2, 2]
def baseStart_3241768 : Nat := 118140960795 + 3241768 * 2 ^ 59
def prefixEnd_3241768 : Nat := 4983230072969 + 3 ^ 40 * 3241768 * 2
def baseEnd_3241768 : Nat := 1664585154364577801491387

theorem tailTrace_3241768 : CollatzResearch.WordTrace tailWord_3241768 prefixEnd_3241768 1664585154364577801491387 := by
  unfold tailWord_3241768
  simp only [CollatzResearch.WordTrace]
  refine ⟨59118496259817830370594979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78824661679757107160793305 59118496259817830370594979)
  ·
    refine ⟨88677744389726745555892469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59118496259817830370594979 88677744389726745555892469)
    ·
      refine ⟨8313538536536882395864919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88677744389726745555892469 8313538536536882395864919)
      ·
        refine ⟨12470307804805323593797379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8313538536536882395864919 12470307804805323593797379)
        ·
          refine ⟨18705461707207985390696069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12470307804805323593797379 18705461707207985390696069)
          ·
            refine ⟨3507274070101497260755513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18705461707207985390696069 3507274070101497260755513)
            ·
              refine ⟨2630455552576122945566635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3507274070101497260755513 2630455552576122945566635)
              ·
                refine ⟨3945683328864184418349953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2630455552576122945566635 3945683328864184418349953)
                ·
                  refine ⟨2959262496648138313762465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3945683328864184418349953 2959262496648138313762465)
                  ·
                    refine ⟨2219446872486103735321849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2959262496648138313762465 2219446872486103735321849)
                    ·
                      refine ⟨1664585154364577801491387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2219446872486103735321849 1664585154364577801491387)
                      ·
                        rfl

theorem cell23_3241768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_3241768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241768 prefixEnd_3241768 := by exact prefixLift 3241768
  have htrace : WordTrace (prefixWord ++ tailWord_3241768) baseStart_3241768 baseEnd_3241768 := by
    simpa [prefixWord, tailWord_3241768, baseEnd_3241768] using wordTrace_append hprefix tailTrace_3241768
  have hstable : (prefixWord ++ tailWord_3241768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241768).length < 2 ^ (prefixWord ++ tailWord_3241768).sum := by decide
  have hdescent : baseEnd_3241768 < baseStart_3241768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241864 : List Nat := [2, 1, 3, 3, 3, 2, 1, 2, 6]
def baseStart_3241864 : Nat := 118140960795 + 3241864 * 2 ^ 59
def prefixEnd_3241864 : Nat := 4983230072969 + 3 ^ 40 * 3241864 * 2
def baseEnd_3241864 : Nat := 184959383167489936210105

theorem tailTrace_3241864 : CollatzResearch.WordTrace tailWord_3241864 prefixEnd_3241864 184959383167489936210105 := by
  unfold tailWord_3241864
  simp only [CollatzResearch.WordTrace]
  refine ⟨59120246963643934568342323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78826995951525246091123097 59120246963643934568342323)
  ·
    refine ⟨88680370445465901852513485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59120246963643934568342323 88680370445465901852513485)
    ·
      refine ⟨33255138917049713194692557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88680370445465901852513485 33255138917049713194692557)
      ·
        refine ⟨12470677093893642448009709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33255138917049713194692557 12470677093893642448009709)
        ·
          refine ⟨4676503910210115918003641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12470677093893642448009709 4676503910210115918003641)
          ·
            refine ⟨3507377932657586938502731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4676503910210115918003641 3507377932657586938502731)
            ·
              refine ⟨5261066898986380407754097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3507377932657586938502731 5261066898986380407754097)
              ·
                refine ⟨3945800174239785305815573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5261066898986380407754097 3945800174239785305815573)
                ·
                  refine ⟨184959383167489936210105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3945800174239785305815573 184959383167489936210105)
                  ·
                    rfl

theorem cell23_3241864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 6].length) (baseStart_3241864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241864 prefixEnd_3241864 := by exact prefixLift 3241864
  have htrace : WordTrace (prefixWord ++ tailWord_3241864) baseStart_3241864 baseEnd_3241864 := by
    simpa [prefixWord, tailWord_3241864, baseEnd_3241864] using wordTrace_append hprefix tailTrace_3241864
  have hstable : (prefixWord ++ tailWord_3241864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241864).length < 2 ^ (prefixWord ++ tailWord_3241864).sum := by decide
  have hdescent : baseEnd_3241864 < baseStart_3241864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241867 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 4, 3, 2]
def baseStart_3241867 : Nat := 118140960795 + 3241867 * 2 ^ 59
def prefixEnd_3241867 : Nat := 4983230072969 + 3 ^ 40 * 3241867 * 2
def baseEnd_3241867 : Nat := 1664635988949372914153431

theorem tailTrace_3241867 : CollatzResearch.WordTrace tailWord_3241867 prefixEnd_3241867 1664635988949372914153431 := by
  unfold tailWord_3241867
  simp only [CollatzResearch.WordTrace]
  refine ⟨118240603346277000649043855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78827068897518000432695903 118240603346277000649043855)
  ·
    refine ⟨177360905019415500973565783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118240603346277000649043855 177360905019415500973565783)
    ·
      refine ⟨266041357529123251460348675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177360905019415500973565783 266041357529123251460348675)
      ·
        refine ⟨399062036293684877190523013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266041357529123251460348675 399062036293684877190523013)
        ·
          refine ⟨74824131805065914473223065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 399062036293684877190523013 74824131805065914473223065)
          ·
            refine ⟨56118098853799435854917299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74824131805065914473223065 56118098853799435854917299)
            ·
              refine ⟨84177148280699153782375949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56118098853799435854917299 84177148280699153782375949)
              ·
                refine ⟨31566430605262182668390981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84177148280699153782375949 31566430605262182668390981)
                ·
                  refine ⟨5918705738486659250323309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31566430605262182668390981 5918705738486659250323309)
                  ·
                    refine ⟨2219514651932497218871241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5918705738486659250323309 2219514651932497218871241)
                    ·
                      refine ⟨1664635988949372914153431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2219514651932497218871241 1664635988949372914153431)
                      ·
                        rfl

theorem cell23_3241867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 3, 2].length) (baseStart_3241867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241867 prefixEnd_3241867 := by exact prefixLift 3241867
  have htrace : WordTrace (prefixWord ++ tailWord_3241867) baseStart_3241867 baseEnd_3241867 := by
    simpa [prefixWord, tailWord_3241867, baseEnd_3241867] using wordTrace_append hprefix tailTrace_3241867
  have hstable : (prefixWord ++ tailWord_3241867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241867).length < 2 ^ (prefixWord ++ tailWord_3241867).sum := by decide
  have hdescent : baseEnd_3241867 < baseStart_3241867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241884 : List Nat := [2, 2, 3, 3, 1, 1, 1, 2, 1, 5, 2]
def baseStart_3241884 : Nat := 118140960795 + 3241884 * 2 ^ 59
def prefixEnd_3241884 : Nat := 4983230072969 + 3 ^ 40 * 3241884 * 2
def baseEnd_3241884 : Nat := 1664644718120499347640853

theorem tailTrace_3241884 : CollatzResearch.WordTrace tailWord_3241884 prefixEnd_3241884 1664644718120499347640853 := by
  unfold tailWord_3241884
  simp only [CollatzResearch.WordTrace]
  refine ⟨59120611693607706276206353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78827482258143608368275137 59120611693607706276206353)
  ·
    refine ⟨44340458770205779707154765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59120611693607706276206353 44340458770205779707154765)
    ·
      refine ⟨16627672038827167390183037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44340458770205779707154765 16627672038827167390183037)
      ·
        refine ⟨6235377014560187771318639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16627672038827167390183037 6235377014560187771318639)
        ·
          refine ⟨9353065521840281656977959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6235377014560187771318639 9353065521840281656977959)
          ·
            refine ⟨14029598282760422485466939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9353065521840281656977959 14029598282760422485466939)
            ·
              refine ⟨21044397424140633728200409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14029598282760422485466939 21044397424140633728200409)
              ·
                refine ⟨15783298068105475296150307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21044397424140633728200409 15783298068105475296150307)
                ·
                  refine ⟨23674947102158212944225461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15783298068105475296150307 23674947102158212944225461)
                  ·
                    refine ⟨2219526290827332463521137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23674947102158212944225461 2219526290827332463521137)
                    ·
                      refine ⟨1664644718120499347640853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2219526290827332463521137 1664644718120499347640853)
                      ·
                        rfl

theorem cell23_3241884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_3241884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241884 prefixEnd_3241884 := by exact prefixLift 3241884
  have htrace : WordTrace (prefixWord ++ tailWord_3241884) baseStart_3241884 baseEnd_3241884 := by
    simpa [prefixWord, tailWord_3241884, baseEnd_3241884] using wordTrace_append hprefix tailTrace_3241884
  have hstable : (prefixWord ++ tailWord_3241884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241884).length < 2 ^ (prefixWord ++ tailWord_3241884).sum := by decide
  have hdescent : baseEnd_3241884 < baseStart_3241884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241902 : List Nat := [4, 1, 5, 1, 1, 2, 1, 3, 1, 4]
def baseStart_3241902 : Nat := 118140960795 + 3241902 * 2 ^ 59
def prefixEnd_3241902 : Nat := 4983230072969 + 3 ^ 40 * 3241902 * 2
def baseEnd_3241902 : Nat := 554884653590760092405257

theorem tailTrace_3241902 : CollatzResearch.WordTrace tailWord_3241902 prefixEnd_3241902 554884653590760092405257 := by
  unfold tailWord_3241902
  simp only [CollatzResearch.WordTrace]
  refine ⟨14780234987643775203320995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78827919934100134417711973 14780234987643775203320995)
  ·
    refine ⟨22170352481465662804981493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14780234987643775203320995 22170352481465662804981493)
    ·
      refine ⟨2078470545137405887967015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22170352481465662804981493 2078470545137405887967015)
      ·
        refine ⟨3117705817706108831950523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2078470545137405887967015 3117705817706108831950523)
        ·
          refine ⟨4676558726559163247925785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3117705817706108831950523 4676558726559163247925785)
          ·
            refine ⟨3507419044919372435944339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4676558726559163247925785 3507419044919372435944339)
            ·
              refine ⟨5261128567379058653916509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3507419044919372435944339 5261128567379058653916509)
              ·
                refine ⟨1972923212767146995218691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5261128567379058653916509 1972923212767146995218691)
                ·
                  refine ⟨2959384819150720492828037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1972923212767146995218691 2959384819150720492828037)
                  ·
                    refine ⟨554884653590760092405257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2959384819150720492828037 554884653590760092405257)
                    ·
                      rfl

theorem cell23_3241902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_3241902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241902 prefixEnd_3241902 := by exact prefixLift 3241902
  have htrace : WordTrace (prefixWord ++ tailWord_3241902) baseStart_3241902 baseEnd_3241902 := by
    simpa [prefixWord, tailWord_3241902, baseEnd_3241902] using wordTrace_append hprefix tailTrace_3241902
  have hstable : (prefixWord ++ tailWord_3241902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241902).length < 2 ^ (prefixWord ++ tailWord_3241902).sum := by decide
  have hdescent : baseEnd_3241902 < baseStart_3241902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241917 : List Nat := [1, 4, 1, 2, 3, 1, 1, 3, 1, 1, 5]
def baseStart_3241917 : Nat := 118140960795 + 3241917 * 2 ^ 59
def prefixEnd_3241917 : Nat := 4983230072969 + 3 ^ 40 * 3241917 * 2
def baseEnd_3241917 : Nat := 1664661662982097718528201

theorem tailTrace_3241917 : CollatzResearch.WordTrace tailWord_3241917 prefixEnd_3241917 1664661662982097718528201 := by
  unfold tailWord_3241917
  simp only [CollatzResearch.WordTrace]
  refine ⟨118242426996095859188364005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78828284664063906125576003 118242426996095859188364005)
  ·
    refine ⟨22170455061767973597818251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118242426996095859188364005 22170455061767973597818251)
    ·
      refine ⟨33255682592651960396727377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22170455061767973597818251 33255682592651960396727377)
      ·
        refine ⟨24941761944488970297545533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33255682592651960396727377 24941761944488970297545533)
        ·
          refine ⟨9353160729183363861579575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24941761944488970297545533 9353160729183363861579575)
          ·
            refine ⟨14029741093775045792369363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9353160729183363861579575 14029741093775045792369363)
            ·
              refine ⟨21044611640662568688554045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14029741093775045792369363 21044611640662568688554045)
              ·
                refine ⟨7891729365248463258207767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21044611640662568688554045 7891729365248463258207767)
                ·
                  refine ⟨11837594047872694887311651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7891729365248463258207767 11837594047872694887311651)
                  ·
                    refine ⟨17756391071809042330967477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11837594047872694887311651 17756391071809042330967477)
                    ·
                      refine ⟨1664661662982097718528201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17756391071809042330967477 1664661662982097718528201)
                      ·
                        rfl

theorem cell23_3241917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_3241917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241917 prefixEnd_3241917 := by exact prefixLift 3241917
  have htrace : WordTrace (prefixWord ++ tailWord_3241917) baseStart_3241917 baseEnd_3241917 := by
    simpa [prefixWord, tailWord_3241917, baseEnd_3241917] using wordTrace_append hprefix tailTrace_3241917
  have hstable : (prefixWord ++ tailWord_3241917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241917).length < 2 ^ (prefixWord ++ tailWord_3241917).sum := by decide
  have hdescent : baseEnd_3241917 < baseStart_3241917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241941 : List Nat := [1, 3, 2, 3, 2, 1, 4, 1, 2, 4]
def baseStart_3241941 : Nat := 118140960795 + 3241941 * 2 ^ 59
def prefixEnd_3241941 : Nat := 4983230072969 + 3 ^ 40 * 3241941 * 2
def baseEnd_3241941 : Nat := 554891328839268541542697

theorem tailTrace_3241941 : CollatzResearch.WordTrace tailWord_3241941 prefixEnd_3241941 554891328839268541542697 := by
  unfold tailWord_3241941
  simp only [CollatzResearch.WordTrace]
  refine ⟨118243302348008911287237677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78828868232005940858158451 118243302348008911287237677)
  ·
    refine ⟨44341238380503341732714129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118243302348008911287237677 44341238380503341732714129)
    ·
      refine ⟨33255928785377506299535597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44341238380503341732714129 33255928785377506299535597)
      ·
        refine ⟨12470973294516564862325849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33255928785377506299535597 12470973294516564862325849)
        ·
          refine ⟨9353229970887423646744387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12470973294516564862325849 9353229970887423646744387)
          ·
            refine ⟨14029844956331135470116581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9353229970887423646744387 14029844956331135470116581)
            ·
              refine ⟨2630595929312087900646859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14029844956331135470116581 2630595929312087900646859)
              ·
                refine ⟨3945893893968131850970289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2630595929312087900646859 3945893893968131850970289)
                ·
                  refine ⟨2959420420476098888227717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3945893893968131850970289 2959420420476098888227717)
                  ·
                    refine ⟨554891328839268541542697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2959420420476098888227717 554891328839268541542697)
                    ·
                      rfl

theorem cell23_3241941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_3241941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241941 prefixEnd_3241941 := by exact prefixLift 3241941
  have htrace : WordTrace (prefixWord ++ tailWord_3241941) baseStart_3241941 baseEnd_3241941 := by
    simpa [prefixWord, tailWord_3241941, baseEnd_3241941] using wordTrace_append hprefix tailTrace_3241941
  have hstable : (prefixWord ++ tailWord_3241941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241941).length < 2 ^ (prefixWord ++ tailWord_3241941).sum := by decide
  have hdescent : baseEnd_3241941 < baseStart_3241941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241948 : List Nat := [2, 2, 6, 1, 1, 1, 1, 1, 3, 1, 4]
def baseStart_3241948 : Nat := 118140960795 + 3241948 * 2 ^ 59
def prefixEnd_3241948 : Nat := 4983230072969 + 3 ^ 40 * 3241948 * 2
def baseEnd_3241948 : Nat := 1664677580882387097240559

theorem tailTrace_3241948 : CollatzResearch.WordTrace tailWord_3241948 prefixEnd_3241948 1664677580882387097240559 := by
  unfold tailWord_3241948
  simp only [CollatzResearch.WordTrace]
  refine ⟨59121778829491775741371249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78829038439322367655161665 59121778829491775741371249)
  ·
    refine ⟨44341334122118831806028437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59121778829491775741371249 44341334122118831806028437)
    ·
      refine ⟨2078500036974320240907583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44341334122118831806028437 2078500036974320240907583)
      ·
        refine ⟨3117750055461480361361375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2078500036974320240907583 3117750055461480361361375)
        ·
          refine ⟨4676625083192220542042063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3117750055461480361361375 4676625083192220542042063)
          ·
            refine ⟨7014937624788330813063095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4676625083192220542042063 7014937624788330813063095)
            ·
              refine ⟨10522406437182496219594643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7014937624788330813063095 10522406437182496219594643)
              ·
                refine ⟨15783609655773744329391965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10522406437182496219594643 15783609655773744329391965)
                ·
                  refine ⟨5918853620915154123521987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15783609655773744329391965 5918853620915154123521987)
                  ·
                    refine ⟨8878280431372731185282981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5918853620915154123521987 8878280431372731185282981)
                    ·
                      refine ⟨1664677580882387097240559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8878280431372731185282981 1664677580882387097240559)
                      ·
                        rfl

theorem cell23_3241948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_3241948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241948 prefixEnd_3241948 := by exact prefixLift 3241948
  have htrace : WordTrace (prefixWord ++ tailWord_3241948) baseStart_3241948 baseEnd_3241948 := by
    simpa [prefixWord, tailWord_3241948, baseEnd_3241948] using wordTrace_append hprefix tailTrace_3241948
  have hstable : (prefixWord ++ tailWord_3241948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241948).length < 2 ^ (prefixWord ++ tailWord_3241948).sum := by decide
  have hdescent : baseEnd_3241948 < baseStart_3241948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241951 : List Nat := [1, 1, 2, 3, 4, 3, 1, 2, 1, 2, 3]
def baseStart_3241951 : Nat := 118140960795 + 3241951 * 2 ^ 59
def prefixEnd_3241951 : Nat := 4983230072969 + 3 ^ 40 * 3241951 * 2
def baseEnd_3241951 : Nat := 1664679121324350585503045

theorem tailTrace_3241951 : CollatzResearch.WordTrace tailWord_3241951 prefixEnd_3241951 1664679121324350585503045 := by
  unfold tailWord_3241951
  simp only [CollatzResearch.WordTrace]
  refine ⟨118243667077972682995101707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78829111385315121996734471 118243667077972682995101707)
  ·
    refine ⟨177365500616959024492652561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118243667077972682995101707 177365500616959024492652561)
    ·
      refine ⟨133024125462719268369489421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177365500616959024492652561 133024125462719268369489421)
      ·
        refine ⟨49884047048519725638558533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133024125462719268369489421 49884047048519725638558533)
        ·
          refine ⟨9353258821597448557229725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49884047048519725638558533 9353258821597448557229725)
          ·
            refine ⟨3507472058099043208961147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9353258821597448557229725 3507472058099043208961147)
            ·
              refine ⟨5261208087148564813441721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3507472058099043208961147 5261208087148564813441721)
              ·
                refine ⟨3945906065361423610081291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5261208087148564813441721 3945906065361423610081291)
                ·
                  refine ⟨5918859098042135415121937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3945906065361423610081291 5918859098042135415121937)
                  ·
                    refine ⟨4439144323531601561341453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5918859098042135415121937 4439144323531601561341453)
                    ·
                      refine ⟨1664679121324350585503045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4439144323531601561341453 1664679121324350585503045)
                      ·
                        rfl

theorem cell23_3241951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_3241951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241951 prefixEnd_3241951 := by exact prefixLift 3241951
  have htrace : WordTrace (prefixWord ++ tailWord_3241951) baseStart_3241951 baseEnd_3241951 := by
    simpa [prefixWord, tailWord_3241951, baseEnd_3241951] using wordTrace_append hprefix tailTrace_3241951
  have hstable : (prefixWord ++ tailWord_3241951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241951).length < 2 ^ (prefixWord ++ tailWord_3241951).sum := by decide
  have hdescent : baseEnd_3241951 < baseStart_3241951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241982 : List Nat := [4, 2, 2, 2, 1, 1, 4, 2, 1, 2, 2]
def baseStart_3241982 : Nat := 118140960795 + 3241982 * 2 ^ 59
def prefixEnd_3241982 : Nat := 4983230072969 + 3 ^ 40 * 3241982 * 2
def baseEnd_3241982 : Nat := 1664695039224639964215403

theorem tailTrace_3241982 : CollatzResearch.WordTrace tailWord_3241982 prefixEnd_3241982 1664695039224639964215403 := by
  unfold tailWord_3241982
  simp only [CollatzResearch.WordTrace]
  refine ⟨14780599717607546911185025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78829865160573583526320133 14780599717607546911185025)
  ·
    refine ⟨11085449788205660183388769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14780599717607546911185025 11085449788205660183388769)
    ·
      refine ⟨8314087341154245137541577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11085449788205660183388769 8314087341154245137541577)
      ·
        refine ⟨6235565505865683853156183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8314087341154245137541577 6235565505865683853156183)
        ·
          refine ⟨9353348258798525779734275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6235565505865683853156183 9353348258798525779734275)
          ·
            refine ⟨14030022388197788669601413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9353348258798525779734275 14030022388197788669601413)
            ·
              refine ⟨2630629197787085375550265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14030022388197788669601413 2630629197787085375550265)
              ·
                refine ⟨1972971898340314031662699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2630629197787085375550265 1972971898340314031662699)
                ·
                  refine ⟨2959457847510471047494049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1972971898340314031662699 2959457847510471047494049)
                  ·
                    refine ⟨2219593385632853285620537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2959457847510471047494049 2219593385632853285620537)
                    ·
                      refine ⟨1664695039224639964215403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2219593385632853285620537 1664695039224639964215403)
                      ·
                        rfl

theorem cell23_3241982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_3241982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3241982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3241982 prefixEnd_3241982 := by exact prefixLift 3241982
  have htrace : WordTrace (prefixWord ++ tailWord_3241982) baseStart_3241982 baseEnd_3241982 := by
    simpa [prefixWord, tailWord_3241982, baseEnd_3241982] using wordTrace_append hprefix tailTrace_3241982
  have hstable : (prefixWord ++ tailWord_3241982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241982).length < 2 ^ (prefixWord ++ tailWord_3241982).sum := by decide
  have hdescent : baseEnd_3241982 < baseStart_3241982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242000 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 6]
def baseStart_3242000 : Nat := 118140960795 + 3242000 * 2 ^ 59
def prefixEnd_3242000 : Nat := 4983230072969 + 3 ^ 40 * 3242000 * 2
def baseEnd_3242000 : Nat := 1664704281876420893790319

theorem tailTrace_3242000 : CollatzResearch.WordTrace tailWord_3242000 prefixEnd_3242000 1664704281876420893790319 := by
  unfold tailWord_3242000
  simp only [CollatzResearch.WordTrace]
  refine ⟨59122727127397582181817727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78830302836530109575756969 59122727127397582181817727)
  ·
    refine ⟨88684090691096373272726591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59122727127397582181817727 88684090691096373272726591)
    ·
      refine ⟨133026136036644559909089887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88684090691096373272726591 133026136036644559909089887)
      ·
        refine ⟨199539204054966839863634831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133026136036644559909089887 199539204054966839863634831)
        ·
          refine ⟨299308806082450259795452247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199539204054966839863634831 299308806082450259795452247)
          ·
            refine ⟨448963209123675389693178371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299308806082450259795452247 448963209123675389693178371)
            ·
              refine ⟨673444813685513084539767557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448963209123675389693178371 673444813685513084539767557)
              ·
                refine ⟨126270902566033703351206417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 673444813685513084539767557 126270902566033703351206417)
                ·
                  refine ⟨94703176924525277513404813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126270902566033703351206417 94703176924525277513404813)
                  ·
                    refine ⟨35513691346696979067526805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94703176924525277513404813 35513691346696979067526805)
                    ·
                      refine ⟨1664704281876420893790319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35513691346696979067526805 1664704281876420893790319)
                      ·
                        rfl

theorem cell23_3242000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 6].length) (baseStart_3242000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242000 prefixEnd_3242000 := by exact prefixLift 3242000
  have htrace : WordTrace (prefixWord ++ tailWord_3242000) baseStart_3242000 baseEnd_3242000 := by
    simpa [prefixWord, tailWord_3242000, baseEnd_3242000] using wordTrace_append hprefix tailTrace_3242000
  have hstable : (prefixWord ++ tailWord_3242000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242000).length < 2 ^ (prefixWord ++ tailWord_3242000).sum := by decide
  have hdescent : baseEnd_3242000 < baseStart_3242000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242038 : List Nat := [5, 1, 2, 1, 1, 1, 3, 1, 4, 2, 2]
def baseStart_3242038 : Nat := 118140960795 + 3242038 * 2 ^ 59
def prefixEnd_3242038 : Nat := 4983230072969 + 3 ^ 40 * 3242038 * 2
def baseEnd_3242038 : Nat := 1664723794141291745115145

theorem tailTrace_3242038 : CollatzResearch.WordTrace tailWord_3242038 prefixEnd_3242038 1664723794141291745115145 := by
  unfold tailWord_3242038
  simp only [CollatzResearch.WordTrace]
  refine ⟨7390427514291093553344923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78831226819104997902345845 7390427514291093553344923)
  ·
    refine ⟨11085641271436640330017385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7390427514291093553344923 11085641271436640330017385)
    ·
      refine ⟨8314230953577480247513039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11085641271436640330017385 8314230953577480247513039)
      ·
        refine ⟨12471346430366220371269559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8314230953577480247513039 12471346430366220371269559)
        ·
          refine ⟨18707019645549330556904339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12471346430366220371269559 18707019645549330556904339)
          ·
            refine ⟨28060529468323995835356509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18707019645549330556904339 28060529468323995835356509)
            ·
              refine ⟨10522698550621498438258691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28060529468323995835356509 10522698550621498438258691)
              ·
                refine ⟨15784047825932247657388037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10522698550621498438258691 15784047825932247657388037)
                ·
                  refine ⟨2959508967362296435760257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15784047825932247657388037 2959508967362296435760257)
                  ·
                    refine ⟨2219631725521722326820193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2959508967362296435760257 2219631725521722326820193)
                    ·
                      refine ⟨1664723794141291745115145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2219631725521722326820193 1664723794141291745115145)
                      ·
                        rfl

theorem cell23_3242038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_3242038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242038 prefixEnd_3242038 := by exact prefixLift 3242038
  have htrace : WordTrace (prefixWord ++ tailWord_3242038) baseStart_3242038 baseEnd_3242038 := by
    simpa [prefixWord, tailWord_3242038, baseEnd_3242038] using wordTrace_append hprefix tailTrace_3242038
  have hstable : (prefixWord ++ tailWord_3242038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242038).length < 2 ^ (prefixWord ++ tailWord_3242038).sum := by decide
  have hdescent : baseEnd_3242038 < baseStart_3242038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242044 : List Nat := [2, 2, 2, 2, 2, 1, 1, 6, 5]
def baseStart_3242044 : Nat := 118140960795 + 3242044 * 2 ^ 59
def prefixEnd_3242044 : Nat := 4983230072969 + 3 ^ 40 * 3242044 * 2
def baseEnd_3242044 : Nat := 184969652780579857960013

theorem tailTrace_3242044 : CollatzResearch.WordTrace tailWord_3242044 prefixEnd_3242044 184969652780579857960013 := by
  unfold tailWord_3242044
  simp only [CollatzResearch.WordTrace]
  refine ⟨59123529533317879939118593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78831372711090506585491457 59123529533317879939118593)
  ·
    refine ⟨44342647149988409954338945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59123529533317879939118593 44342647149988409954338945)
    ·
      refine ⟨33256985362491307465754209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44342647149988409954338945 33256985362491307465754209)
      ·
        refine ⟨24942739021868480599315657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33256985362491307465754209 24942739021868480599315657)
        ·
          refine ⟨18707054266401360449486743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24942739021868480599315657 18707054266401360449486743)
          ·
            refine ⟨28060581399602040674230115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18707054266401360449486743 28060581399602040674230115)
            ·
              refine ⟨42090872099403061011345173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28060581399602040674230115 42090872099403061011345173)
              ·
                refine ⟨1973009629659518484906805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42090872099403061011345173 1973009629659518484906805)
                ·
                  refine ⟨184969652780579857960013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1973009629659518484906805 184969652780579857960013)
                  ·
                    rfl

theorem cell23_3242044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 6, 5].length) (baseStart_3242044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242044 prefixEnd_3242044 := by exact prefixLift 3242044
  have htrace : WordTrace (prefixWord ++ tailWord_3242044) baseStart_3242044 baseEnd_3242044 := by
    simpa [prefixWord, tailWord_3242044, baseEnd_3242044] using wordTrace_append hprefix tailTrace_3242044
  have hstable : (prefixWord ++ tailWord_3242044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242044).length < 2 ^ (prefixWord ++ tailWord_3242044).sum := by decide
  have hdescent : baseEnd_3242044 < baseStart_3242044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242251 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 6, 1, 3]
def baseStart_3242251 : Nat := 118140960795 + 3242251 * 2 ^ 59
def prefixEnd_3242251 : Nat := 4983230072969 + 3 ^ 40 * 3242251 * 2
def baseEnd_3242251 : Nat := 1664833165520699411751665

theorem tailTrace_3242251 : CollatzResearch.WordTrace tailWord_3242251 prefixEnd_3242251 1664833165520699411751665 := by
  unfold tailWord_3242251
  simp only [CollatzResearch.WordTrace]
  refine ⟨118254608976885834231022607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78836405984590556154015071 118254608976885834231022607)
  ·
    refine ⟨177381913465328751346533911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118254608976885834231022607 177381913465328751346533911)
    ·
      refine ⟨266072870197993127019800867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177381913465328751346533911 266072870197993127019800867)
      ·
        refine ⟨399109305296989690529701301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266072870197993127019800867 399109305296989690529701301)
        ·
          refine ⟨37416497371592783487159497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 399109305296989690529701301 37416497371592783487159497)
          ·
            refine ⟨28062373028694587615369623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37416497371592783487159497 28062373028694587615369623)
            ·
              refine ⟨42093559543041881423054435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28062373028694587615369623 42093559543041881423054435)
              ·
                refine ⟨63140339314562822134581653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42093559543041881423054435 63140339314562822134581653)
                ·
                  refine ⟨2959703405370132287558515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63140339314562822134581653 2959703405370132287558515)
                  ·
                    refine ⟨4439555108055198431337773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2959703405370132287558515 4439555108055198431337773)
                    ·
                      refine ⟨1664833165520699411751665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4439555108055198431337773 1664833165520699411751665)
                      ·
                        rfl

theorem cell23_3242251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 6, 1, 3].length) (baseStart_3242251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242251 prefixEnd_3242251 := by exact prefixLift 3242251
  have htrace : WordTrace (prefixWord ++ tailWord_3242251) baseStart_3242251 baseEnd_3242251 := by
    simpa [prefixWord, tailWord_3242251, baseEnd_3242251] using wordTrace_append hprefix tailTrace_3242251
  have hstable : (prefixWord ++ tailWord_3242251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242251).length < 2 ^ (prefixWord ++ tailWord_3242251).sum := by decide
  have hdescent : baseEnd_3242251 < baseStart_3242251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242264 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 2, 2, 5]
def baseStart_3242264 : Nat := 118140960795 + 3242264 * 2 ^ 59
def prefixEnd_3242264 : Nat := 4983230072969 + 3 ^ 40 * 3242264 * 2
def baseEnd_3242264 : Nat := 1664839840769207860889105

theorem tailTrace_3242264 : CollatzResearch.WordTrace tailWord_3242264 prefixEnd_3242264 1664839840769207860889105 := by
  unfold tailWord_3242264
  simp only [CollatzResearch.WordTrace]
  refine ⟨59127541562919368725622923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78836722083892491634163897 59127541562919368725622923)
  ·
    refine ⟨88691312344379053088434385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59127541562919368725622923 88691312344379053088434385)
    ·
      refine ⟨66518484258284289816325789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88691312344379053088434385 66518484258284289816325789)
      ·
        refine ⟨24944431596856608681122171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66518484258284289816325789 24944431596856608681122171)
        ·
          refine ⟨37416647395284913021683257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24944431596856608681122171 37416647395284913021683257)
          ·
            refine ⟨28062485546463684766262443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37416647395284913021683257 28062485546463684766262443)
            ·
              refine ⟨42093728319695527149393665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28062485546463684766262443 42093728319695527149393665)
              ·
                refine ⟨31570296239771645362045249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42093728319695527149393665 31570296239771645362045249)
                ·
                  refine ⟨23677722179828734021533937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31570296239771645362045249 23677722179828734021533937)
                  ·
                    refine ⟨17758291634871550516150453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23677722179828734021533937 17758291634871550516150453)
                    ·
                      refine ⟨1664839840769207860889105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17758291634871550516150453 1664839840769207860889105)
                      ·
                        rfl

theorem cell23_3242264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_3242264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242264 prefixEnd_3242264 := by exact prefixLift 3242264
  have htrace : WordTrace (prefixWord ++ tailWord_3242264) baseStart_3242264 baseEnd_3242264 := by
    simpa [prefixWord, tailWord_3242264, baseEnd_3242264] using wordTrace_append hprefix tailTrace_3242264
  have hstable : (prefixWord ++ tailWord_3242264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242264).length < 2 ^ (prefixWord ++ tailWord_3242264).sum := by decide
  have hdescent : baseEnd_3242264 < baseStart_3242264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242268 : List Nat := [2, 2, 3, 1, 1, 1, 1, 6, 2, 1, 3]
def baseStart_3242268 : Nat := 118140960795 + 3242268 * 2 ^ 59
def prefixEnd_3242268 : Nat := 4983230072969 + 3 ^ 40 * 3242268 * 2
def baseEnd_3242268 : Nat := 1664841894691825845239087

theorem tailTrace_3242268 : CollatzResearch.WordTrace tailWord_3242268 prefixEnd_3242268 1664841894691825845239087 := by
  unfold tailWord_3242268
  simp only [CollatzResearch.WordTrace]
  refine ⟨59127614508912123067195729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78836819345216164089594305 59127614508912123067195729)
  ·
    refine ⟨44345710881684092300396797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59127614508912123067195729 44345710881684092300396797)
    ·
      refine ⟨16629641580631534612648799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44345710881684092300396797 16629641580631534612648799)
      ·
        refine ⟨24944462370947301918973199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16629641580631534612648799 24944462370947301918973199)
        ·
          refine ⟨37416693556420952878459799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24944462370947301918973199 37416693556420952878459799)
          ·
            refine ⟨56125040334631429317689699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37416693556420952878459799 56125040334631429317689699)
            ·
              refine ⟨84187560501947143976534549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56125040334631429317689699 84187560501947143976534549)
              ·
                refine ⟨3946291898528772373900057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84187560501947143976534549 3946291898528772373900057)
                ·
                  refine ⟨2959718923896579280425043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3946291898528772373900057 2959718923896579280425043)
                  ·
                    refine ⟨4439578385844868920637565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2959718923896579280425043 4439578385844868920637565)
                    ·
                      refine ⟨1664841894691825845239087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4439578385844868920637565 1664841894691825845239087)
                      ·
                        rfl

theorem cell23_3242268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_3242268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242268 prefixEnd_3242268 := by exact prefixLift 3242268
  have htrace : WordTrace (prefixWord ++ tailWord_3242268) baseStart_3242268 baseEnd_3242268 := by
    simpa [prefixWord, tailWord_3242268, baseEnd_3242268] using wordTrace_append hprefix tailTrace_3242268
  have hstable : (prefixWord ++ tailWord_3242268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242268).length < 2 ^ (prefixWord ++ tailWord_3242268).sum := by decide
  have hdescent : baseEnd_3242268 < baseStart_3242268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242269 : List Nat := [1, 4, 2, 3, 3, 1, 1, 1, 3, 2, 2]
def baseStart_3242269 : Nat := 118140960795 + 3242269 * 2 ^ 59
def prefixEnd_3242269 : Nat := 4983230072969 + 3 ^ 40 * 3242269 * 2
def baseEnd_3242269 : Nat := 1664842408172480341326583

theorem tailTrace_3242269 : CollatzResearch.WordTrace tailWord_3242269 prefixEnd_3242269 1664842408172480341326583 := by
  unfold tailWord_3242269
  simp only [CollatzResearch.WordTrace]
  refine ⟨118255265490820623305177861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78836843660547082203451907 118255265490820623305177861)
  ·
    refine ⟨22172862279528866869720849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118255265490820623305177861 22172862279528866869720849)
    ·
      refine ⟨16629646709646650152290637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22172862279528866869720849 16629646709646650152290637)
      ·
        refine ⟨6236117516117493807108989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16629646709646650152290637 6236117516117493807108989)
        ·
          refine ⟨2338544068544060177665871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6236117516117493807108989 2338544068544060177665871)
          ·
            refine ⟨3507816102816090266498807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2338544068544060177665871 3507816102816090266498807)
            ·
              refine ⟨5261724154224135399748211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3507816102816090266498807 5261724154224135399748211)
              ·
                refine ⟨7892586231336203099622317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5261724154224135399748211 7892586231336203099622317)
                ·
                  refine ⟨2959719836751076162358369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7892586231336203099622317 2959719836751076162358369)
                  ·
                    refine ⟨2219789877563307121768777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2959719836751076162358369 2219789877563307121768777)
                    ·
                      refine ⟨1664842408172480341326583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2219789877563307121768777 1664842408172480341326583)
                      ·
                        rfl

theorem cell23_3242269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_3242269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242269 prefixEnd_3242269 := by exact prefixLift 3242269
  have htrace : WordTrace (prefixWord ++ tailWord_3242269) baseStart_3242269 baseEnd_3242269 := by
    simpa [prefixWord, tailWord_3242269, baseEnd_3242269] using wordTrace_append hprefix tailTrace_3242269
  have hstable : (prefixWord ++ tailWord_3242269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242269).length < 2 ^ (prefixWord ++ tailWord_3242269).sum := by decide
  have hdescent : baseEnd_3242269 < baseStart_3242269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242284 : List Nat := [2, 2, 1, 1, 1, 3, 2, 3, 2, 6]
def baseStart_3242284 : Nat := 118140960795 + 3242284 * 2 ^ 59
def prefixEnd_3242284 : Nat := 4983230072969 + 3 ^ 40 * 3242284 * 2
def baseEnd_3242284 : Nat := 554950036794099260879671

theorem tailTrace_3242284 : CollatzResearch.WordTrace tailWord_3242284 prefixEnd_3242284 554950036794099260879671 := by
  unfold tailWord_3242284
  simp only [CollatzResearch.WordTrace]
  refine ⟨59127906292883140433486953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78837208390510853911315937 59127906292883140433486953)
  ·
    refine ⟨44345929719662355325115215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59127906292883140433486953 44345929719662355325115215)
    ·
      refine ⟨66518894579493532987672823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44345929719662355325115215 66518894579493532987672823)
      ·
        refine ⟨99778341869240299481509235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66518894579493532987672823 99778341869240299481509235)
        ·
          refine ⟨149667512803860449222263853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99778341869240299481509235 149667512803860449222263853)
          ·
            refine ⟨56125317301447668458348945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149667512803860449222263853 56125317301447668458348945)
            ·
              refine ⟨42093987976085751343761709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56125317301447668458348945 42093987976085751343761709)
              ·
                refine ⟨15785245491032156753910641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42093987976085751343761709 15785245491032156753910641)
                ·
                  refine ⟨11838934118274117565432981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15785245491032156753910641 11838934118274117565432981)
                  ·
                    refine ⟨554950036794099260879671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11838934118274117565432981 554950036794099260879671)
                    ·
                      rfl

theorem cell23_3242284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 6].length) (baseStart_3242284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242284 prefixEnd_3242284 := by exact prefixLift 3242284
  have htrace : WordTrace (prefixWord ++ tailWord_3242284) baseStart_3242284 baseEnd_3242284 := by
    simpa [prefixWord, tailWord_3242284, baseEnd_3242284] using wordTrace_append hprefix tailTrace_3242284
  have hstable : (prefixWord ++ tailWord_3242284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242284).length < 2 ^ (prefixWord ++ tailWord_3242284).sum := by decide
  have hdescent : baseEnd_3242284 < baseStart_3242284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242304 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 4]
def baseStart_3242304 : Nat := 118140960795 + 3242304 * 2 ^ 59
def prefixEnd_3242304 : Nat := 4983230072969 + 3 ^ 40 * 3242304 * 2
def baseEnd_3242304 : Nat := 1664860379995387704388921

theorem tailTrace_3242304 : CollatzResearch.WordTrace tailWord_3242304 prefixEnd_3242304 1664860379995387704388921 := by
  unfold tailWord_3242304
  simp only [CollatzResearch.WordTrace]
  refine ⟨59128271022846912141350983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78837694697129216188467977 59128271022846912141350983)
  ·
    refine ⟨88692406534270368212026475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59128271022846912141350983 88692406534270368212026475)
    ·
      refine ⟨133038609801405552318039713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88692406534270368212026475 133038609801405552318039713)
      ·
        refine ⟨99778957351054164238529785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133038609801405552318039713 99778957351054164238529785)
        ·
          refine ⟨74834218013290623178897339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99778957351054164238529785 74834218013290623178897339)
          ·
            refine ⟨112251327019935934768346009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74834218013290623178897339 112251327019935934768346009)
            ·
              refine ⟨84188495264951951076259507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112251327019935934768346009 84188495264951951076259507)
              ·
                refine ⟨126282742897427926614389261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84188495264951951076259507 126282742897427926614389261)
                ·
                  refine ⟨47356028586535472480395973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126282742897427926614389261 47356028586535472480395973)
                  ·
                    refine ⟨8879255359975401090074245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47356028586535472480395973 8879255359975401090074245)
                    ·
                      refine ⟨1664860379995387704388921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8879255359975401090074245 1664860379995387704388921)
                      ·
                        rfl

theorem cell23_3242304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_3242304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242304 prefixEnd_3242304 := by exact prefixLift 3242304
  have htrace : WordTrace (prefixWord ++ tailWord_3242304) baseStart_3242304 baseEnd_3242304 := by
    simpa [prefixWord, tailWord_3242304, baseEnd_3242304] using wordTrace_append hprefix tailTrace_3242304
  have hstable : (prefixWord ++ tailWord_3242304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242304).length < 2 ^ (prefixWord ++ tailWord_3242304).sum := by decide
  have hdescent : baseEnd_3242304 < baseStart_3242304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242338 : List Nat := [3, 3, 2, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_3242338 : Nat := 118140960795 + 3242338 * 2 ^ 59
def prefixEnd_3242338 : Nat := 4983230072969 + 3 ^ 40 * 3242338 * 2
def baseEnd_3242338 : Nat := 1664877838337640571363765

theorem tailTrace_3242338 : CollatzResearch.WordTrace tailWord_3242338 prefixEnd_3242338 1664877838337640571363765 := by
  unfold tailWord_3242338
  simp only [CollatzResearch.WordTrace]
  refine ⟨29564445531892662022359917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78838521418380432059626445 29564445531892662022359917)
  ·
    refine ⟨11086667074459748258384969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29564445531892662022359917 11086667074459748258384969)
    ·
      refine ⟨8315000305844811193788727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11086667074459748258384969 8315000305844811193788727)
      ·
        refine ⟨12472500458767216790683091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8315000305844811193788727 12472500458767216790683091)
        ·
          refine ⟨18708750688150825186024637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12472500458767216790683091 18708750688150825186024637)
          ·
            refine ⟨7015781508056559444759239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18708750688150825186024637 7015781508056559444759239)
            ·
              refine ⟨10523672262084839167138859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7015781508056559444759239 10523672262084839167138859)
              ·
                refine ⟨15785508393127258750708289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10523672262084839167138859 15785508393127258750708289)
                ·
                  refine ⟨11839131294845444063031217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15785508393127258750708289 11839131294845444063031217)
                  ·
                    refine ⟨8879348471134083047273413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11839131294845444063031217 8879348471134083047273413)
                    ·
                      refine ⟨1664877838337640571363765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8879348471134083047273413 1664877838337640571363765)
                      ·
                        rfl

theorem cell23_3242338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_3242338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242338 prefixEnd_3242338 := by exact prefixLift 3242338
  have htrace : WordTrace (prefixWord ++ tailWord_3242338) baseStart_3242338 baseEnd_3242338 := by
    simpa [prefixWord, tailWord_3242338, baseEnd_3242338] using wordTrace_append hprefix tailTrace_3242338
  have hstable : (prefixWord ++ tailWord_3242338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242338).length < 2 ^ (prefixWord ++ tailWord_3242338).sum := by decide
  have hdescent : baseEnd_3242338 < baseStart_3242338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242341 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 3]
def baseStart_3242341 : Nat := 118140960795 + 3242341 * 2 ^ 59
def prefixEnd_3242341 : Nat := 4983230072969 + 3 ^ 40 * 3242341 * 2
def baseEnd_3242341 : Nat := 1664879378779604059626251

theorem tailTrace_3242341 : CollatzResearch.WordTrace tailWord_3242341 prefixEnd_3242341 1664879378779604059626251 := by
  unfold tailWord_3242341
  simp only [CollatzResearch.WordTrace]
  refine ⟨118257891546559779601798877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78838594364373186401199251 118257891546559779601798877)
  ·
    refine ⟨44346709329959917350674579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118257891546559779601798877 44346709329959917350674579)
    ·
      refine ⟨66520063994939876026011869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44346709329959917350674579 66520063994939876026011869)
      ·
        refine ⟨24945023998102453509754451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66520063994939876026011869 24945023998102453509754451)
        ·
          refine ⟨37417535997153680264631677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24945023998102453509754451 37417535997153680264631677)
          ·
            refine ⟨14031575998932630099236879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37417535997153680264631677 14031575998932630099236879)
            ·
              refine ⟨21047363998398945148855319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14031575998932630099236879 21047363998398945148855319)
              ·
                refine ⟨31571045997598417723282979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21047363998398945148855319 31571045997598417723282979)
                ·
                  refine ⟨47356568996397626584924469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31571045997598417723282979 47356568996397626584924469)
                  ·
                    refine ⟨4439678343412277492336669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47356568996397626584924469 4439678343412277492336669)
                    ·
                      refine ⟨1664879378779604059626251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4439678343412277492336669 1664879378779604059626251)
                      ·
                        rfl

theorem cell23_3242341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_3242341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242341 prefixEnd_3242341 := by exact prefixLift 3242341
  have htrace : WordTrace (prefixWord ++ tailWord_3242341) baseStart_3242341 baseEnd_3242341 := by
    simpa [prefixWord, tailWord_3242341, baseEnd_3242341] using wordTrace_append hprefix tailTrace_3242341
  have hstable : (prefixWord ++ tailWord_3242341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242341).length < 2 ^ (prefixWord ++ tailWord_3242341).sum := by decide
  have hdescent : baseEnd_3242341 < baseStart_3242341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242418 : List Nat := [3, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3]
def baseStart_3242418 : Nat := 118140960795 + 3242418 * 2 ^ 59
def prefixEnd_3242418 : Nat := 4983230072969 + 3 ^ 40 * 3242418 * 2
def baseEnd_3242418 : Nat := 1664918916790000258363397

theorem tailTrace_3242418 : CollatzResearch.WordTrace tailWord_3242418 prefixEnd_3242418 1664918916790000258363397 := by
  unfold tailWord_3242418
  simp only [CollatzResearch.WordTrace]
  refine ⟨29565174991820205438087977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78840466644853881168234605 29565174991820205438087977)
  ·
    refine ⟨22173881243865154078565983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29565174991820205438087977 22173881243865154078565983)
    ·
      refine ⟨33260821865797731117848975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22173881243865154078565983 33260821865797731117848975)
      ·
        refine ⟨49891232798696596676773463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33260821865797731117848975 49891232798696596676773463)
        ·
          refine ⟨74836849198044895015160195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49891232798696596676773463 74836849198044895015160195)
          ·
            refine ⟨112255273797067342522740293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74836849198044895015160195 112255273797067342522740293)
            ·
              refine ⟨21047863836950126723013805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112255273797067342522740293 21047863836950126723013805)
              ·
                refine ⟨7892948938856297521130177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21047863836950126723013805 7892948938856297521130177)
                ·
                  refine ⟨5919711704142223140847633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7892948938856297521130177 5919711704142223140847633)
                  ·
                    refine ⟨4439783778106667355635725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5919711704142223140847633 4439783778106667355635725)
                    ·
                      refine ⟨1664918916790000258363397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4439783778106667355635725 1664918916790000258363397)
                      ·
                        rfl

theorem cell23_3242418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_3242418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242418 prefixEnd_3242418 := by exact prefixLift 3242418
  have htrace : WordTrace (prefixWord ++ tailWord_3242418) baseStart_3242418 baseEnd_3242418 := by
    simpa [prefixWord, tailWord_3242418, baseEnd_3242418] using wordTrace_append hprefix tailTrace_3242418
  have hstable : (prefixWord ++ tailWord_3242418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242418).length < 2 ^ (prefixWord ++ tailWord_3242418).sum := by decide
  have hdescent : baseEnd_3242418 < baseStart_3242418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242442 : List Nat := [3, 1, 2, 1, 2, 2, 5, 2, 1, 4]
def baseStart_3242442 : Nat := 118140960795 + 3242442 * 2 ^ 59
def prefixEnd_3242442 : Nat := 4983230072969 + 3 ^ 40 * 3242442 * 2
def baseEnd_3242442 : Nat := 554977080108569388154429

theorem tailTrace_3242442 : CollatzResearch.WordTrace tailWord_3242442 prefixEnd_3242442 554977080108569388154429 := by
  unfold tailWord_3242442
  simp only [CollatzResearch.WordTrace]
  refine ⟨29565393829798468462806395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78841050212795915900817053 29565393829798468462806395)
  ·
    refine ⟨44348090744697702694209593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29565393829798468462806395 44348090744697702694209593)
    ·
      refine ⟨33261068058523277020657195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44348090744697702694209593 33261068058523277020657195)
      ·
        refine ⟨49891602087784915530985793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33261068058523277020657195 49891602087784915530985793)
        ·
          refine ⟨37418701565838686648239345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49891602087784915530985793 37418701565838686648239345)
          ·
            refine ⟨28064026174379014986179509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37418701565838686648239345 28064026174379014986179509)
            ·
              refine ⟨2631002453848032654954329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28064026174379014986179509 2631002453848032654954329)
              ·
                refine ⟨1973251840386024491215747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2631002453848032654954329 1973251840386024491215747)
                ·
                  refine ⟨2959877760579036736823621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1973251840386024491215747 2959877760579036736823621)
                  ·
                    refine ⟨554977080108569388154429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2959877760579036736823621 554977080108569388154429)
                    ·
                      rfl

theorem cell23_3242442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_3242442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242442 prefixEnd_3242442 := by exact prefixLift 3242442
  have htrace : WordTrace (prefixWord ++ tailWord_3242442) baseStart_3242442 baseEnd_3242442 := by
    simpa [prefixWord, tailWord_3242442, baseEnd_3242442] using wordTrace_append hprefix tailTrace_3242442
  have hstable : (prefixWord ++ tailWord_3242442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242442).length < 2 ^ (prefixWord ++ tailWord_3242442).sum := by decide
  have hdescent : baseEnd_3242442 < baseStart_3242442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242475 : List Nat := [1, 1, 1, 1, 2, 3, 6, 1, 2, 3, 2]
def baseStart_3242475 : Nat := 118140960795 + 3242475 * 2 ^ 59
def prefixEnd_3242475 : Nat := 4983230072969 + 3 ^ 40 * 3242475 * 2
def baseEnd_3242475 : Nat := 1664948185187306535350635

theorem tailTrace_3242475 : CollatzResearch.WordTrace tailWord_3242475 prefixEnd_3242475 1664948185187306535350635 := by
  unfold tailWord_3242475
  simp only [CollatzResearch.WordTrace]
  refine ⟨118262778928074320487176879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78841852618716213658117919 118262778928074320487176879)
  ·
    refine ⟨177394168392111480730765319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118262778928074320487176879 177394168392111480730765319)
    ·
      refine ⟨266091252588167221096147979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177394168392111480730765319 266091252588167221096147979)
      ·
        refine ⟨399136878882250831644221969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266091252588167221096147979 399136878882250831644221969)
        ·
          refine ⟨299352659161688123733166477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399136878882250831644221969 299352659161688123733166477)
          ·
            refine ⟨112257247185633046399937429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 299352659161688123733166477 112257247185633046399937429)
            ·
              refine ⟨5262058461826549049997067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 112257247185633046399937429 5262058461826549049997067)
              ·
                refine ⟨7893087692739823574995601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5262058461826549049997067 7893087692739823574995601)
                ·
                  refine ⟨5919815769554867681246701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7893087692739823574995601 5919815769554867681246701)
                  ·
                    refine ⟨2219930913583075380467513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5919815769554867681246701 2219930913583075380467513)
                    ·
                      refine ⟨1664948185187306535350635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2219930913583075380467513 1664948185187306535350635)
                      ·
                        rfl

theorem cell23_3242475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 3, 2].length) (baseStart_3242475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242475 prefixEnd_3242475 := by exact prefixLift 3242475
  have htrace : WordTrace (prefixWord ++ tailWord_3242475) baseStart_3242475 baseEnd_3242475 := by
    simpa [prefixWord, tailWord_3242475, baseEnd_3242475] using wordTrace_append hprefix tailTrace_3242475
  have hstable : (prefixWord ++ tailWord_3242475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242475).length < 2 ^ (prefixWord ++ tailWord_3242475).sum := by decide
  have hdescent : baseEnd_3242475 < baseStart_3242475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242501 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 3, 1, 6]
def baseStart_3242501 : Nat := 118140960795 + 3242501 * 2 ^ 59
def prefixEnd_3242501 : Nat := 4983230072969 + 3 ^ 40 * 3242501 * 2
def baseEnd_3242501 : Nat := 1664961535684323433625515

theorem tailTrace_3242501 : CollatzResearch.WordTrace tailWord_3242501 prefixEnd_3242501 1664961535684323433625515 := by
  unfold tailWord_3242501
  simp only [CollatzResearch.WordTrace]
  refine ⟨118263727225980126927623357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78842484817320084618415571 118263727225980126927623357)
  ·
    refine ⟨44348897709742547597858759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118263727225980126927623357 44348897709742547597858759)
    ·
      refine ⟨66523346564613821396788139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44348897709742547597858759 66523346564613821396788139)
      ·
        refine ⟨99785019846920732095182209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66523346564613821396788139 99785019846920732095182209)
        ·
          refine ⟨74838764885190549071386657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99785019846920732095182209 74838764885190549071386657)
          ·
            refine ⟨56129073663892911803539993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74838764885190549071386657 56129073663892911803539993)
            ·
              refine ⟨42096805247919683852654995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56129073663892911803539993 42096805247919683852654995)
              ·
                refine ⟨63145207871879525778982493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42096805247919683852654995 63145207871879525778982493)
                ·
                  refine ⟨23679452951954822167118435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63145207871879525778982493 23679452951954822167118435)
                  ·
                    refine ⟨35519179427932233250677653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23679452951954822167118435 35519179427932233250677653)
                    ·
                      refine ⟨1664961535684323433625515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35519179427932233250677653 1664961535684323433625515)
                      ·
                        rfl

theorem cell23_3242501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_3242501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242501 prefixEnd_3242501 := by exact prefixLift 3242501
  have htrace : WordTrace (prefixWord ++ tailWord_3242501) baseStart_3242501 baseEnd_3242501 := by
    simpa [prefixWord, tailWord_3242501, baseEnd_3242501] using wordTrace_append hprefix tailTrace_3242501
  have hstable : (prefixWord ++ tailWord_3242501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242501).length < 2 ^ (prefixWord ++ tailWord_3242501).sum := by decide
  have hdescent : baseEnd_3242501 < baseStart_3242501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242525 : List Nat := [1, 4, 2, 2, 1, 2, 2, 1, 3, 2, 3]
def baseStart_3242525 : Nat := 118140960795 + 3242525 * 2 ^ 59
def prefixEnd_3242525 : Nat := 4983230072969 + 3 ^ 40 * 3242525 * 2
def baseEnd_3242525 : Nat := 1664973859220031339725405

theorem tailTrace_3242525 : CollatzResearch.WordTrace tailWord_3242525 prefixEnd_3242525 1664973859220031339725405 := by
  unfold tailWord_3242525
  simp only [CollatzResearch.WordTrace]
  refine ⟨118264602577893179026497029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78843068385262119350998019 118264602577893179026497029)
  ·
    refine ⟨22174612983354971067468193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118264602577893179026497029 22174612983354971067468193)
    ·
      refine ⟨16630959737516228300601145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22174612983354971067468193 16630959737516228300601145)
      ·
        refine ⟨12473219803137171225450859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16630959737516228300601145 12473219803137171225450859)
        ·
          refine ⟨18709829704705756838176289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12473219803137171225450859 18709829704705756838176289)
          ·
            refine ⟨14032372278529317628632217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18709829704705756838176289 14032372278529317628632217)
            ·
              refine ⟨10524279208896988221474163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14032372278529317628632217 10524279208896988221474163)
              ·
                refine ⟨15786418813345482332211245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10524279208896988221474163 15786418813345482332211245)
                ·
                  refine ⟨5919907055004555874579217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15786418813345482332211245 5919907055004555874579217)
                  ·
                    refine ⟨4439930291253416905934413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5919907055004555874579217 4439930291253416905934413)
                    ·
                      refine ⟨1664973859220031339725405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4439930291253416905934413 1664973859220031339725405)
                      ·
                        rfl

theorem cell23_3242525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_3242525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242525 prefixEnd_3242525 := by exact prefixLift 3242525
  have htrace : WordTrace (prefixWord ++ tailWord_3242525) baseStart_3242525 baseEnd_3242525 := by
    simpa [prefixWord, tailWord_3242525, baseEnd_3242525] using wordTrace_append hprefix tailTrace_3242525
  have hstable : (prefixWord ++ tailWord_3242525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242525).length < 2 ^ (prefixWord ++ tailWord_3242525).sum := by decide
  have hdescent : baseEnd_3242525 < baseStart_3242525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242566 : List Nat := [6, 1, 1, 1, 2, 2, 3, 1, 2, 4]
def baseStart_3242566 : Nat := 118140960795 + 3242566 * 2 ^ 59
def prefixEnd_3242566 : Nat := 4983230072969 + 3 ^ 40 * 3242566 * 2
def baseEnd_3242566 : Nat := 554998303975621893104239

theorem tailTrace_3242566 : CollatzResearch.WordTrace tailWord_3242566 prefixEnd_3242566 554998303975621893104239 := by
  unfold tailWord_3242566
  simp only [CollatzResearch.WordTrace]
  refine ⟨3695815561585770094648111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78844065313829762019159701 3695815561585770094648111)
  ·
    refine ⟨5543723342378655141972167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3695815561585770094648111 5543723342378655141972167)
    ·
      refine ⟨8315585013567982712958251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5543723342378655141972167 8315585013567982712958251)
      ·
        refine ⟨12473377520351974069437377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8315585013567982712958251 12473377520351974069437377)
        ·
          refine ⟨9355033140263980552078033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12473377520351974069437377 9355033140263980552078033)
          ·
            refine ⟨7016274855197985414058525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9355033140263980552078033 7016274855197985414058525)
            ·
              refine ⟨2631103070699244530271947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7016274855197985414058525 2631103070699244530271947)
              ·
                refine ⟨3946654606048866795407921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2631103070699244530271947 3946654606048866795407921)
                ·
                  refine ⟨2959990954536650096555941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3946654606048866795407921 2959990954536650096555941)
                  ·
                    refine ⟨554998303975621893104239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2959990954536650096555941 554998303975621893104239)
                    ·
                      rfl

theorem cell23_3242566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_3242566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242566 prefixEnd_3242566 := by exact prefixLift 3242566
  have htrace : WordTrace (prefixWord ++ tailWord_3242566) baseStart_3242566 baseEnd_3242566 := by
    simpa [prefixWord, tailWord_3242566, baseEnd_3242566] using wordTrace_append hprefix tailTrace_3242566
  have hstable : (prefixWord ++ tailWord_3242566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242566).length < 2 ^ (prefixWord ++ tailWord_3242566).sum := by decide
  have hdescent : baseEnd_3242566 < baseStart_3242566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242595 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 3, 4, 2]
def baseStart_3242595 : Nat := 118140960795 + 3242595 * 2 ^ 59
def prefixEnd_3242595 : Nat := 4983230072969 + 3 ^ 40 * 3242595 * 2
def baseEnd_3242595 : Nat := 1665009802865846065850083

theorem tailTrace_3242595 : CollatzResearch.WordTrace tailWord_3242595 prefixEnd_3242595 1665009802865846065850083 := by
  unfold tailWord_3242595
  simp only [CollatzResearch.WordTrace]
  refine ⟨118267155687639580981545239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78844770458426387321030159 118267155687639580981545239)
  ·
    refine ⟨177400733531459371472317859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118267155687639580981545239 177400733531459371472317859)
    ·
      refine ⟨266101100297189057208476789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177400733531459371472317859 266101100297189057208476789)
      ·
        refine ⟨24946978152861474113294699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 266101100297189057208476789 24946978152861474113294699)
        ·
          refine ⟨37420467229292211169942049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24946978152861474113294699 37420467229292211169942049)
          ·
            refine ⟨28065350421969158377456537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37420467229292211169942049 28065350421969158377456537)
            ·
              refine ⟨21049012816476868783092403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28065350421969158377456537 21049012816476868783092403)
              ·
                refine ⟨31573519224715303174638605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21049012816476868783092403 31573519224715303174638605)
                ·
                  refine ⟨11840069709268238690489477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31573519224715303174638605 11840069709268238690489477)
                  ·
                    refine ⟨2220013070487794754466777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11840069709268238690489477 2220013070487794754466777)
                    ·
                      refine ⟨1665009802865846065850083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2220013070487794754466777 1665009802865846065850083)
                      ·
                        rfl

theorem cell23_3242595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_3242595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242595 prefixEnd_3242595 := by exact prefixLift 3242595
  have htrace : WordTrace (prefixWord ++ tailWord_3242595) baseStart_3242595 baseEnd_3242595 := by
    simpa [prefixWord, tailWord_3242595, baseEnd_3242595] using wordTrace_append hprefix tailTrace_3242595
  have hstable : (prefixWord ++ tailWord_3242595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242595).length < 2 ^ (prefixWord ++ tailWord_3242595).sum := by decide
  have hdescent : baseEnd_3242595 < baseStart_3242595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242629 : List Nat := [1, 3, 1, 1, 4, 3, 1, 3, 2, 2, 2]
def baseStart_3242629 : Nat := 118140960795 + 3242629 * 2 ^ 59
def prefixEnd_3242629 : Nat := 4983230072969 + 3 ^ 40 * 3242629 * 2
def baseEnd_3242629 : Nat := 1665027261208098932824927

theorem tailTrace_3242629 : CollatzResearch.WordTrace tailWord_3242629 prefixEnd_3242629 1665027261208098932824927 := by
  unfold tailWord_3242629
  simp only [CollatzResearch.WordTrace]
  refine ⟨118268395769516404788282941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78845597179677603192188627 118268395769516404788282941)
  ·
    refine ⟨44350648413568651795606103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118268395769516404788282941 44350648413568651795606103)
    ·
      refine ⟨66525972620352977693409155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44350648413568651795606103 66525972620352977693409155)
      ·
        refine ⟨99788958930529466540113733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66525972620352977693409155 99788958930529466540113733)
        ·
          refine ⟨18710429799474274976271325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99788958930529466540113733 18710429799474274976271325)
          ·
            refine ⟨7016411174802853116101747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18710429799474274976271325 7016411174802853116101747)
            ·
              refine ⟨10524616762204279674152621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7016411174802853116101747 10524616762204279674152621)
              ·
                refine ⟨3946731285826604877807233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10524616762204279674152621 3946731285826604877807233)
                ·
                  refine ⟨2960048464369953658355425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3946731285826604877807233 2960048464369953658355425)
                  ·
                    refine ⟨2220036348277465243766569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2960048464369953658355425 2220036348277465243766569)
                    ·
                      refine ⟨1665027261208098932824927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2220036348277465243766569 1665027261208098932824927)
                      ·
                        rfl

theorem cell23_3242629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 2, 2, 2].length) (baseStart_3242629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242629 prefixEnd_3242629 := by exact prefixLift 3242629
  have htrace : WordTrace (prefixWord ++ tailWord_3242629) baseStart_3242629 baseEnd_3242629 := by
    simpa [prefixWord, tailWord_3242629, baseEnd_3242629] using wordTrace_append hprefix tailTrace_3242629
  have hstable : (prefixWord ++ tailWord_3242629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242629).length < 2 ^ (prefixWord ++ tailWord_3242629).sum := by decide
  have hdescent : baseEnd_3242629 < baseStart_3242629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242663 : List Nat := [1, 1, 6, 3, 1, 1, 2, 2, 2, 2, 2]
def baseStart_3242663 : Nat := 118140960795 + 3242663 * 2 ^ 59
def prefixEnd_3242663 : Nat := 4983230072969 + 3 ^ 40 * 3242663 * 2
def baseEnd_3242663 : Nat := 1665044719550351799799771

theorem tailTrace_3242663 : CollatzResearch.WordTrace tailWord_3242663 prefixEnd_3242663 1665044719550351799799771 := by
  unfold tailWord_3242663
  simp only [CollatzResearch.WordTrace]
  refine ⟨118269635851393228595020643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78846423900928819063347095 118269635851393228595020643)
  ·
    refine ⟨177404453777089842892530965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118269635851393228595020643 177404453777089842892530965)
    ·
      refine ⟨8315833770801086385587389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 177404453777089842892530965 8315833770801086385587389)
      ·
        refine ⟨3118437664050407394595271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8315833770801086385587389 3118437664050407394595271)
        ·
          refine ⟨4677656496075611091892907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3118437664050407394595271 4677656496075611091892907)
          ·
            refine ⟨7016484744113416637839361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4677656496075611091892907 7016484744113416637839361)
            ·
              refine ⟨5262363558085062478379521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7016484744113416637839361 5262363558085062478379521)
              ·
                refine ⟨3946772668563796858784641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5262363558085062478379521 3946772668563796858784641)
                ·
                  refine ⟨2960079501422847644088481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3946772668563796858784641 2960079501422847644088481)
                  ·
                    refine ⟨2220059626067135733066361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2960079501422847644088481 2220059626067135733066361)
                    ·
                      refine ⟨1665044719550351799799771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2220059626067135733066361 1665044719550351799799771)
                      ·
                        rfl

theorem cell23_3242663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_3242663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242663 prefixEnd_3242663 := by exact prefixLift 3242663
  have htrace : WordTrace (prefixWord ++ tailWord_3242663) baseStart_3242663 baseEnd_3242663 := by
    simpa [prefixWord, tailWord_3242663, baseEnd_3242663] using wordTrace_append hprefix tailTrace_3242663
  have hstable : (prefixWord ++ tailWord_3242663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242663).length < 2 ^ (prefixWord ++ tailWord_3242663).sum := by decide
  have hdescent : baseEnd_3242663 < baseStart_3242663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242669 : List Nat := [1, 5, 2, 1, 1, 2, 4, 2, 5]
def baseStart_3242669 : Nat := 118140960795 + 3242669 * 2 ^ 59
def prefixEnd_3242669 : Nat := 4983230072969 + 3 ^ 40 * 3242669 * 2
def baseEnd_3242669 : Nat := 185005311159364308480527

theorem tailTrace_3242669 : CollatzResearch.WordTrace tailWord_3242669 prefixEnd_3242669 185005311159364308480527 := by
  unfold tailWord_3242669
  simp only [CollatzResearch.WordTrace]
  refine ⟨118269854689371491619739061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78846569792914327746492707 118269854689371491619739061)
  ·
    refine ⟨11087798877128577339350537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118269854689371491619739061 11087798877128577339350537)
    ·
      refine ⟨8315849157846433004512903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11087798877128577339350537 8315849157846433004512903)
      ·
        refine ⟨12473773736769649506769355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8315849157846433004512903 12473773736769649506769355)
        ·
          refine ⟨18710660605154474260154033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12473773736769649506769355 18710660605154474260154033)
          ·
            refine ⟨14032995453865855695115525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18710660605154474260154033 14032995453865855695115525)
            ·
              refine ⟨2631186647599847942834161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14032995453865855695115525 2631186647599847942834161)
              ·
                refine ⟨1973389985699885957125621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2631186647599847942834161 1973389985699885957125621)
                ·
                  refine ⟨185005311159364308480527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1973389985699885957125621 185005311159364308480527)
                  ·
                    rfl

theorem cell23_3242669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_3242669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242669 prefixEnd_3242669 := by exact prefixLift 3242669
  have htrace : WordTrace (prefixWord ++ tailWord_3242669) baseStart_3242669 baseEnd_3242669 := by
    simpa [prefixWord, tailWord_3242669, baseEnd_3242669] using wordTrace_append hprefix tailTrace_3242669
  have hstable : (prefixWord ++ tailWord_3242669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242669).length < 2 ^ (prefixWord ++ tailWord_3242669).sum := by decide
  have hdescent : baseEnd_3242669 < baseStart_3242669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242702 : List Nat := [4, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4]
def baseStart_3242702 : Nat := 118140960795 + 3242702 * 2 ^ 59
def prefixEnd_3242702 : Nat := 4983230072969 + 3 ^ 40 * 3242702 * 2
def baseEnd_3242702 : Nat := 1665064745295877147212091

theorem tailTrace_3242702 : CollatzResearch.WordTrace tailWord_3242702 prefixEnd_3242702 1665064745295877147212091 := by
  unfold tailWord_3242702
  simp only [CollatzResearch.WordTrace]
  refine ⟨14783882287281492281961295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78847372198834625503793573 14783882287281492281961295)
  ·
    refine ⟨22175823430922238422941943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14783882287281492281961295 22175823430922238422941943)
    ·
      refine ⟨33263735146383357634412915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22175823430922238422941943 33263735146383357634412915)
      ·
        refine ⟨49895602719575036451619373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33263735146383357634412915 49895602719575036451619373)
        ·
          refine ⟨18710851019840638669357265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49895602719575036451619373 18710851019840638669357265)
          ·
            refine ⟨14033138264880479002017949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18710851019840638669357265 14033138264880479002017949)
            ·
              refine ⟨5262426849330179625756731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14033138264880479002017949 5262426849330179625756731)
              ·
                refine ⟨7893640273995269438635097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5262426849330179625756731 7893640273995269438635097)
                ·
                  refine ⟨5920230205496452078976323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7893640273995269438635097 5920230205496452078976323)
                  ·
                    refine ⟨8880345308244678118464485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5920230205496452078976323 8880345308244678118464485)
                    ·
                      refine ⟨1665064745295877147212091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8880345308244678118464485 1665064745295877147212091)
                      ·
                        rfl

theorem cell23_3242702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_3242702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242702 prefixEnd_3242702 := by exact prefixLift 3242702
  have htrace : WordTrace (prefixWord ++ tailWord_3242702) baseStart_3242702 baseEnd_3242702 := by
    simpa [prefixWord, tailWord_3242702, baseEnd_3242702] using wordTrace_append hprefix tailTrace_3242702
  have hstable : (prefixWord ++ tailWord_3242702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242702).length < 2 ^ (prefixWord ++ tailWord_3242702).sum := by decide
  have hdescent : baseEnd_3242702 < baseStart_3242702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242705 : List Nat := [1, 2, 2, 1, 2, 3, 3, 1, 1, 4, 3]
def baseStart_3242705 : Nat := 118140960795 + 3242705 * 2 ^ 59
def prefixEnd_3242705 : Nat := 4983230072969 + 3 ^ 40 * 3242705 * 2
def baseEnd_3242705 : Nat := 1665066285737840635474577

theorem tailTrace_3242705 : CollatzResearch.WordTrace tailWord_3242705 prefixEnd_3242705 1665066285737840635474577 := by
  unfold tailWord_3242705
  simp only [CollatzResearch.WordTrace]
  refine ⟨118271167717241069768049569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78847445144827379845366379 118271167717241069768049569)
  ·
    refine ⟨88703375787930802326037177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118271167717241069768049569 88703375787930802326037177)
    ·
      refine ⟨66527531840948101744527883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88703375787930802326037177 66527531840948101744527883)
      ·
        refine ⟨99791297761422152616791825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66527531840948101744527883 99791297761422152616791825)
        ·
          refine ⟨74843473321066614462593869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99791297761422152616791825 74843473321066614462593869)
          ·
            refine ⟨28066302495399980423472701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74843473321066614462593869 28066302495399980423472701)
            ·
              refine ⟨10524863435774992658802263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28066302495399980423472701 10524863435774992658802263)
              ·
                refine ⟨15787295153662488988203395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10524863435774992658802263 15787295153662488988203395)
                ·
                  refine ⟨23680942730493733482305093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15787295153662488988203395 23680942730493733482305093)
                  ·
                    refine ⟨4440176761967575027932205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23680942730493733482305093 4440176761967575027932205)
                    ·
                      refine ⟨1665066285737840635474577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4440176761967575027932205 1665066285737840635474577)
                      ·
                        rfl

theorem cell23_3242705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 4, 3].length) (baseStart_3242705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242705 prefixEnd_3242705 := by exact prefixLift 3242705
  have htrace : WordTrace (prefixWord ++ tailWord_3242705) baseStart_3242705 baseEnd_3242705 := by
    simpa [prefixWord, tailWord_3242705, baseEnd_3242705] using wordTrace_append hprefix tailTrace_3242705
  have hstable : (prefixWord ++ tailWord_3242705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242705).length < 2 ^ (prefixWord ++ tailWord_3242705).sum := by decide
  have hdescent : baseEnd_3242705 < baseStart_3242705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242725 : List Nat := [1, 3, 1, 4, 1, 3, 1, 1, 8]
def baseStart_3242725 : Nat := 118140960795 + 3242725 * 2 ^ 59
def prefixEnd_3242725 : Nat := 4983230072969 + 3 ^ 40 * 3242725 * 2
def baseEnd_3242725 : Nat := 185008506150103395247165

theorem tailTrace_3242725 : CollatzResearch.WordTrace tailWord_3242725 prefixEnd_3242725 185008506150103395247165 := by
  unfold tailWord_3242725
  simp only [CollatzResearch.WordTrace]
  refine ⟨118271897177168613183777629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78847931451445742122518419 118271897177168613183777629)
  ·
    refine ⟨44351961441438229943916611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118271897177168613183777629 44351961441438229943916611)
    ·
      refine ⟨66527942162157344915874917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44351961441438229943916611 66527942162157344915874917)
      ·
        refine ⟨12473989155404502171726547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66527942162157344915874917 12473989155404502171726547)
        ·
          refine ⟨18710983733106753257589821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12473989155404502171726547 18710983733106753257589821)
          ·
            refine ⟨7016618899915032471596183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18710983733106753257589821 7016618899915032471596183)
            ·
              refine ⟨10524928349872548707394275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7016618899915032471596183 10524928349872548707394275)
              ·
                refine ⟨15787392524808823061091413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10524928349872548707394275 15787392524808823061091413)
                ·
                  refine ⟨185008506150103395247165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15787392524808823061091413 185008506150103395247165)
                  ·
                    rfl

theorem cell23_3242725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 8].length) (baseStart_3242725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242725 prefixEnd_3242725 := by exact prefixLift 3242725
  have htrace : WordTrace (prefixWord ++ tailWord_3242725) baseStart_3242725 baseEnd_3242725 := by
    simpa [prefixWord, tailWord_3242725, baseEnd_3242725] using wordTrace_append hprefix tailTrace_3242725
  have hstable : (prefixWord ++ tailWord_3242725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242725).length < 2 ^ (prefixWord ++ tailWord_3242725).sum := by decide
  have hdescent : baseEnd_3242725 < baseStart_3242725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242762 : List Nat := [3, 1, 2, 2, 1, 2, 1, 3, 1, 5, 2]
def baseStart_3242762 : Nat := 118140960795 + 3242762 * 2 ^ 59
def prefixEnd_3242762 : Nat := 4983230072969 + 3 ^ 40 * 3242762 * 2
def baseEnd_3242762 : Nat := 1665095554135146912461815

theorem tailTrace_3242762 : CollatzResearch.WordTrace tailWord_3242762 prefixEnd_3242762 1665095554135146912461815 := by
  unfold tailWord_3242762
  simp only [CollatzResearch.WordTrace]
  refine ⟨29568311669508642125718635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78848831118689712335249693 29568311669508642125718635)
  ·
    refine ⟨44352467504262963188577953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29568311669508642125718635 44352467504262963188577953)
    ·
      refine ⟨33264350628197222391433465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44352467504262963188577953 33264350628197222391433465)
      ·
        refine ⟨24948262971147916793575099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33264350628197222391433465 24948262971147916793575099)
        ·
          refine ⟨37422394456721875190362649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24948262971147916793575099 37422394456721875190362649)
          ·
            refine ⟨28066795842541406392771987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37422394456721875190362649 28066795842541406392771987)
            ·
              refine ⟨42100193763812109589157981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28066795842541406392771987 42100193763812109589157981)
              ·
                refine ⟨15787572661429541095934243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42100193763812109589157981 15787572661429541095934243)
                ·
                  refine ⟨23681358992144311643901365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15787572661429541095934243 23681358992144311643901365)
                  ·
                    refine ⟨2220127405513529216615753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23681358992144311643901365 2220127405513529216615753)
                    ·
                      refine ⟨1665095554135146912461815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2220127405513529216615753 1665095554135146912461815)
                      ·
                        rfl

theorem cell23_3242762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_3242762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242762 prefixEnd_3242762 := by exact prefixLift 3242762
  have htrace : WordTrace (prefixWord ++ tailWord_3242762) baseStart_3242762 baseEnd_3242762 := by
    simpa [prefixWord, tailWord_3242762, baseEnd_3242762] using wordTrace_append hprefix tailTrace_3242762
  have hstable : (prefixWord ++ tailWord_3242762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242762).length < 2 ^ (prefixWord ++ tailWord_3242762).sum := by decide
  have hdescent : baseEnd_3242762 < baseStart_3242762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242786 : List Nat := [3, 3, 1, 1, 2, 4, 1, 1, 3, 1, 3]
def baseStart_3242786 : Nat := 118140960795 + 3242786 * 2 ^ 59
def prefixEnd_3242786 : Nat := 4983230072969 + 3 ^ 40 * 3242786 * 2
def baseEnd_3242786 : Nat := 1665107877670854818561705

theorem tailTrace_3242786 : CollatzResearch.WordTrace tailWord_3242786 prefixEnd_3242786 1665107877670854818561705 := by
  unfold tailWord_3242786
  simp only [CollatzResearch.WordTrace]
  refine ⟨29568530507486905150437053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78849414686631747067832141 29568530507486905150437053)
  ·
    refine ⟨11088198940307589431413895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29568530507486905150437053 11088198940307589431413895)
    ·
      refine ⟨16632298410461384147120843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11088198940307589431413895 16632298410461384147120843)
      ·
        refine ⟨24948447615692076220681265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16632298410461384147120843 24948447615692076220681265)
        ·
          refine ⟨18711335711769057165510949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24948447615692076220681265 18711335711769057165510949)
          ·
            refine ⟨3508375445956698218533303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18711335711769057165510949 3508375445956698218533303)
            ·
              refine ⟨5262563168935047327799955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3508375445956698218533303 5262563168935047327799955)
              ·
                refine ⟨7893844753402570991699933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5262563168935047327799955 7893844753402570991699933)
                ·
                  refine ⟨2960191782525964121887475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7893844753402570991699933 2960191782525964121887475)
                  ·
                    refine ⟨4440287673788946182831213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2960191782525964121887475 4440287673788946182831213)
                    ·
                      refine ⟨1665107877670854818561705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4440287673788946182831213 1665107877670854818561705)
                      ·
                        rfl

theorem cell23_3242786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_3242786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242786 prefixEnd_3242786 := by exact prefixLift 3242786
  have htrace : WordTrace (prefixWord ++ tailWord_3242786) baseStart_3242786 baseEnd_3242786 := by
    simpa [prefixWord, tailWord_3242786, baseEnd_3242786] using wordTrace_append hprefix tailTrace_3242786
  have hstable : (prefixWord ++ tailWord_3242786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242786).length < 2 ^ (prefixWord ++ tailWord_3242786).sum := by decide
  have hdescent : baseEnd_3242786 < baseStart_3242786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242792 : List Nat := [2, 1, 5, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_3242792 : Nat := 118140960795 + 3242792 * 2 ^ 59
def prefixEnd_3242792 : Nat := 4983230072969 + 3 ^ 40 * 3242792 * 2
def baseEnd_3242792 : Nat := 1665110958554781795086677

theorem tailTrace_3242792 : CollatzResearch.WordTrace tailWord_3242792 prefixEnd_3242792 1665110958554781795086677 := by
  unfold tailWord_3242792
  simp only [CollatzResearch.WordTrace]
  refine ⟨59137170433962941813233315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78849560578617255750977753 59137170433962941813233315)
  ·
    refine ⟨88705755650944412719849973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59137170433962941813233315 88705755650944412719849973)
    ·
      refine ⟨8316164592276038692485935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88705755650944412719849973 8316164592276038692485935)
      ·
        refine ⟨12474246888414058038728903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8316164592276038692485935 12474246888414058038728903)
        ·
          refine ⟨18711370332621087058093355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12474246888414058038728903 18711370332621087058093355)
          ·
            refine ⟨28067055498931630587140033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18711370332621087058093355 28067055498931630587140033)
            ·
              refine ⟨21050291624198722940355025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28067055498931630587140033 21050291624198722940355025)
              ·
                refine ⟨15787718718149042205266269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21050291624198722940355025 15787718718149042205266269)
                ·
                  refine ⟨5920394519305890826974851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15787718718149042205266269 5920394519305890826974851)
                  ·
                    refine ⟨8880591778958836240462277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5920394519305890826974851 8880591778958836240462277)
                    ·
                      refine ⟨1665110958554781795086677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8880591778958836240462277 1665110958554781795086677)
                      ·
                        rfl

theorem cell23_3242792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_3242792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242792 prefixEnd_3242792 := by exact prefixLift 3242792
  have htrace : WordTrace (prefixWord ++ tailWord_3242792) baseStart_3242792 baseEnd_3242792 := by
    simpa [prefixWord, tailWord_3242792, baseEnd_3242792] using wordTrace_append hprefix tailTrace_3242792
  have hstable : (prefixWord ++ tailWord_3242792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242792).length < 2 ^ (prefixWord ++ tailWord_3242792).sum := by decide
  have hdescent : baseEnd_3242792 < baseStart_3242792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242815 : List Nat := [1, 1, 2, 2, 5, 1, 2, 9]
def baseStart_3242815 : Nat := 118140960795 + 3242815 * 2 ^ 59
def prefixEnd_3242815 : Nat := 4983230072969 + 3 ^ 40 * 3242815 * 2
def baseEnd_3242815 : Nat := 61671213652216118707373

theorem tailTrace_3242815 : CollatzResearch.WordTrace tailWord_3242815 prefixEnd_3242815 61671213652216118707373 := by
  unfold tailWord_3242815
  simp only [CollatzResearch.WordTrace]
  refine ⟨118275179746842558554553899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78850119831228372369702599 118275179746842558554553899)
  ·
    refine ⟨177412769620263837831830849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118275179746842558554553899 177412769620263837831830849)
    ·
      refine ⟨133059577215197878373873137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177412769620263837831830849 133059577215197878373873137)
      ·
        refine ⟨99794682911398408780404853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133059577215197878373873137 99794682911398408780404853)
        ·
          refine ⟨9355751522943600823162955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99794682911398408780404853 9355751522943600823162955)
          ·
            refine ⟨14033627284415401234744433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9355751522943600823162955 14033627284415401234744433)
            ·
              refine ⟨10525220463311550926058325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14033627284415401234744433 10525220463311550926058325)
              ·
                refine ⟨61671213652216118707373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10525220463311550926058325 61671213652216118707373)
                ·
                  rfl

theorem cell23_3242815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 9].length) (baseStart_3242815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242815 prefixEnd_3242815 := by exact prefixLift 3242815
  have htrace : WordTrace (prefixWord ++ tailWord_3242815) baseStart_3242815 baseEnd_3242815 := by
    simpa [prefixWord, tailWord_3242815, baseEnd_3242815] using wordTrace_append hprefix tailTrace_3242815
  have hstable : (prefixWord ++ tailWord_3242815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242815).length < 2 ^ (prefixWord ++ tailWord_3242815).sum := by decide
  have hdescent : baseEnd_3242815 < baseStart_3242815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242836 : List Nat := [2, 4, 1, 1, 4, 1, 2, 2, 2, 4]
def baseStart_3242836 : Nat := 118140960795 + 3242836 * 2 ^ 59
def prefixEnd_3242836 : Nat := 4983230072969 + 3 ^ 40 * 3242836 * 2
def baseEnd_3242836 : Nat := 555044517234526540978825

theorem tailTrace_3242836 : CollatzResearch.WordTrace tailWord_3242836 prefixEnd_3242836 555044517234526540978825 := by
  unfold tailWord_3242836
  simp only [CollatzResearch.WordTrace]
  refine ⟨59137972839883239570534181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78850630453177652760712241 59137972839883239570534181)
  ·
    refine ⟨11088369907478107419475159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59137972839883239570534181 11088369907478107419475159)
    ·
      refine ⟨16632554861217161129212739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11088369907478107419475159 16632554861217161129212739)
      ·
        refine ⟨24948832291825741693819109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16632554861217161129212739 24948832291825741693819109)
        ·
          refine ⟨4677906054717326567591083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24948832291825741693819109 4677906054717326567591083)
          ·
            refine ⟨7016859082075989851386625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4677906054717326567591083 7016859082075989851386625)
            ·
              refine ⟨5262644311556992388539969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7016859082075989851386625 5262644311556992388539969)
              ·
                refine ⟨3946983233667744291404977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5262644311556992388539969 3946983233667744291404977)
                ·
                  refine ⟨2960237425250808218553733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3946983233667744291404977 2960237425250808218553733)
                  ·
                    refine ⟨555044517234526540978825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2960237425250808218553733 555044517234526540978825)
                    ·
                      rfl

theorem cell23_3242836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_3242836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242836 prefixEnd_3242836 := by exact prefixLift 3242836
  have htrace : WordTrace (prefixWord ++ tailWord_3242836) baseStart_3242836 baseEnd_3242836 := by
    simpa [prefixWord, tailWord_3242836, baseEnd_3242836] using wordTrace_append hprefix tailTrace_3242836
  have hstable : (prefixWord ++ tailWord_3242836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242836).length < 2 ^ (prefixWord ++ tailWord_3242836).sum := by decide
  have hdescent : baseEnd_3242836 < baseStart_3242836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242859 : List Nat := [1, 1, 1, 1, 2, 2, 6, 3, 2, 1, 3]
def baseStart_3242859 : Nat := 118140960795 + 3242859 * 2 ^ 59
def prefixEnd_3242859 : Nat := 4983230072969 + 3 ^ 40 * 3242859 * 2
def baseEnd_3242859 : Nat := 1665145361758633032948869

theorem tailTrace_3242859 : CollatzResearch.WordTrace tailWord_3242859 prefixEnd_3242859 1665145361758633032948869 := by
  unfold tailWord_3242859
  simp only [CollatzResearch.WordTrace]
  refine ⟨118276784558683154069155631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78851189705788769379437087 118276784558683154069155631)
  ·
    refine ⟨177415176838024731103733447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118276784558683154069155631 177415176838024731103733447)
    ·
      refine ⟨266122765257037096655600171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177415176838024731103733447 266122765257037096655600171)
      ·
        refine ⟨399184147885555644983400257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266122765257037096655600171 399184147885555644983400257)
        ·
          refine ⟨299388110914166733737550193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399184147885555644983400257 299388110914166733737550193)
          ·
            refine ⟨224541083185625050303162645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299388110914166733737550193 224541083185625050303162645)
            ·
              refine ⟨10525363274326174232960749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 224541083185625050303162645 10525363274326174232960749)
              ·
                refine ⟨3947011227872315337360281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10525363274326174232960749 3947011227872315337360281)
                ·
                  refine ⟨2960258420904236503020211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3947011227872315337360281 2960258420904236503020211)
                  ·
                    refine ⟨4440387631356354754530317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2960258420904236503020211 4440387631356354754530317)
                    ·
                      refine ⟨1665145361758633032948869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4440387631356354754530317 1665145361758633032948869)
                      ·
                        rfl

theorem cell23_3242859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 2, 1, 3].length) (baseStart_3242859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242859 prefixEnd_3242859 := by exact prefixLift 3242859
  have htrace : WordTrace (prefixWord ++ tailWord_3242859) baseStart_3242859 baseEnd_3242859 := by
    simpa [prefixWord, tailWord_3242859, baseEnd_3242859] using wordTrace_append hprefix tailTrace_3242859
  have hstable : (prefixWord ++ tailWord_3242859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242859).length < 2 ^ (prefixWord ++ tailWord_3242859).sum := by decide
  have hdescent : baseEnd_3242859 < baseStart_3242859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242895 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 4]
def baseStart_3242895 : Nat := 118140960795 + 3242895 * 2 ^ 59
def prefixEnd_3242895 : Nat := 4983230072969 + 3 ^ 40 * 3242895 * 2
def baseEnd_3242895 : Nat := 1665163847062194892098703

theorem tailTrace_3242895 : CollatzResearch.WordTrace tailWord_3242895 prefixEnd_3242895 1665163847062194892098703 := by
  unfold tailWord_3242895
  simp only [CollatzResearch.WordTrace]
  refine ⟨118278097586552732217466139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78852065057701821478310759 118278097586552732217466139)
  ·
    refine ⟨177417146379829098326199209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118278097586552732217466139 177417146379829098326199209)
    ·
      refine ⟨133062859784871823744649407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177417146379829098326199209 133062859784871823744649407)
      ·
        refine ⟨199594289677307735616974111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133062859784871823744649407 199594289677307735616974111)
        ·
          refine ⟨299391434515961603425461167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199594289677307735616974111 299391434515961603425461167)
          ·
            refine ⟨449087151773942405138191751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299391434515961603425461167 449087151773942405138191751)
            ·
              refine ⟨673630727660913607707287627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449087151773942405138191751 673630727660913607707287627)
              ·
                refine ⟨1010446091491370411560931441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 673630727660913607707287627 1010446091491370411560931441)
                ·
                  refine ⟨757834568618527808670698581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1010446091491370411560931441 757834568618527808670698581)
                  ·
                    refine ⟨8880873850998372757859749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 757834568618527808670698581 8880873850998372757859749)
                    ·
                      refine ⟨1665163847062194892098703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8880873850998372757859749 1665163847062194892098703)
                      ·
                        rfl

theorem cell23_3242895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 4].length) (baseStart_3242895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242895 prefixEnd_3242895 := by exact prefixLift 3242895
  have htrace : WordTrace (prefixWord ++ tailWord_3242895) baseStart_3242895 baseEnd_3242895 := by
    simpa [prefixWord, tailWord_3242895, baseEnd_3242895] using wordTrace_append hprefix tailTrace_3242895
  have hstable : (prefixWord ++ tailWord_3242895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242895).length < 2 ^ (prefixWord ++ tailWord_3242895).sum := by decide
  have hdescent : baseEnd_3242895 < baseStart_3242895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242912 : List Nat := [2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 4]
def baseStart_3242912 : Nat := 118140960795 + 3242912 * 2 ^ 59
def prefixEnd_3242912 : Nat := 4983230072969 + 3 ^ 40 * 3242912 * 2
def baseEnd_3242912 : Nat := 1665172576233321325586125

theorem tailTrace_3242912 : CollatzResearch.WordTrace tailWord_3242912 prefixEnd_3242912 1665172576233321325586125 := by
  unfold tailWord_3242912
  simp only [CollatzResearch.WordTrace]
  refine ⟨59139358813745572060417495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78852478418327429413889993 59139358813745572060417495)
  ·
    refine ⟨88709038220618358090626243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59139358813745572060417495 88709038220618358090626243)
    ·
      refine ⟨133063557330927537135939365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88709038220618358090626243 133063557330927537135939365)
      ·
        refine ⟨24949416999548913212988631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133063557330927537135939365 24949416999548913212988631)
        ·
          refine ⟨37424125499323369819482947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24949416999548913212988631 37424125499323369819482947)
          ·
            refine ⟨56136188248985054729224421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37424125499323369819482947 56136188248985054729224421)
            ·
              refine ⟨10525535296684697761729579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56136188248985054729224421 10525535296684697761729579)
              ·
                refine ⟨15788302945027046642594369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10525535296684697761729579 15788302945027046642594369)
                ·
                  refine ⟨11841227208770284981945777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15788302945027046642594369 11841227208770284981945777)
                  ·
                    refine ⟨8880920406577713736459333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11841227208770284981945777 8880920406577713736459333)
                    ·
                      refine ⟨1665172576233321325586125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8880920406577713736459333 1665172576233321325586125)
                      ·
                        rfl

theorem cell23_3242912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_3242912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242912 prefixEnd_3242912 := by exact prefixLift 3242912
  have htrace : WordTrace (prefixWord ++ tailWord_3242912) baseStart_3242912 baseEnd_3242912 := by
    simpa [prefixWord, tailWord_3242912, baseEnd_3242912] using wordTrace_append hprefix tailTrace_3242912
  have hstable : (prefixWord ++ tailWord_3242912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242912).length < 2 ^ (prefixWord ++ tailWord_3242912).sum := by decide
  have hdescent : baseEnd_3242912 < baseStart_3242912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242956 : List Nat := [2, 2, 1, 4, 1, 1, 5, 2, 5]
def baseStart_3242956 : Nat := 118140960795 + 3242956 * 2 ^ 59
def prefixEnd_3242956 : Nat := 4983230072969 + 3 ^ 40 * 3242956 * 2
def baseEnd_3242956 : Nat := 185021685486902128159547

theorem tailTrace_3242956 : CollatzResearch.WordTrace tailWord_3242956 prefixEnd_3242956 185021685486902128159547 := by
  unfold tailWord_3242956
  simp only [CollatzResearch.WordTrace]
  refine ⟨59140161219665869817718361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78853548292887826423624481 59140161219665869817718361)
  ·
    refine ⟨44355120914749402363288771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59140161219665869817718361 44355120914749402363288771)
    ·
      refine ⟨66532681372124103544933157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44355120914749402363288771 66532681372124103544933157)
      ·
        refine ⟨12474877757273269414674967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66532681372124103544933157 12474877757273269414674967)
        ·
          refine ⟨18712316635909904122012451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12474877757273269414674967 18712316635909904122012451)
          ·
            refine ⟨28068474953864856183018677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18712316635909904122012451 28068474953864856183018677)
            ·
              refine ⟨2631419526924830267158001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28068474953864856183018677 2631419526924830267158001)
              ·
                refine ⟨1973564645193622700368501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2631419526924830267158001 1973564645193622700368501)
                ·
                  refine ⟨185021685486902128159547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1973564645193622700368501 185021685486902128159547)
                  ·
                    rfl

theorem cell23_3242956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 2, 5].length) (baseStart_3242956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3242956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3242956 prefixEnd_3242956 := by exact prefixLift 3242956
  have htrace : WordTrace (prefixWord ++ tailWord_3242956) baseStart_3242956 baseEnd_3242956 := by
    simpa [prefixWord, tailWord_3242956, baseEnd_3242956] using wordTrace_append hprefix tailTrace_3242956
  have hstable : (prefixWord ++ tailWord_3242956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242956).length < 2 ^ (prefixWord ++ tailWord_3242956).sum := by decide
  have hdescent : baseEnd_3242956 < baseStart_3242956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243029 : List Nat := [1, 3, 2, 1, 4, 1, 2, 3, 6]
def baseStart_3243029 : Nat := 118140960795 + 3243029 * 2 ^ 59
def prefixEnd_3243029 : Nat := 4983230072969 + 3 ^ 40 * 3243029 * 2
def baseEnd_3243029 : Nat := 185025850385544151980343

theorem tailTrace_3243029 : CollatzResearch.WordTrace tailWord_3243029 prefixEnd_3243029 185025850385544151980343 := by
  unfold tailWord_3243029
  simp only [CollatzResearch.WordTrace]
  refine ⟨118282984968067273102844141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78855323312044848735229427 118282984968067273102844141)
  ·
    refine ⟨44356119363025227413566553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118282984968067273102844141 44356119363025227413566553)
    ·
      refine ⟨33267089522268920560174915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44356119363025227413566553 33267089522268920560174915)
      ·
        refine ⟨49900634283403380840262373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33267089522268920560174915 49900634283403380840262373)
        ·
          refine ⟨9356368928138133907549195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49900634283403380840262373 9356368928138133907549195)
          ·
            refine ⟨14034553392207200861323793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9356368928138133907549195 14034553392207200861323793)
            ·
              refine ⟨10525915044155400645992845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14034553392207200861323793 10525915044155400645992845)
              ·
                refine ⟨3947218141558275242247317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10525915044155400645992845 3947218141558275242247317)
                ·
                  refine ⟨185025850385544151980343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3947218141558275242247317 185025850385544151980343)
                  ·
                    rfl

theorem cell23_3243029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 6].length) (baseStart_3243029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243029 prefixEnd_3243029 := by exact prefixLift 3243029
  have htrace : WordTrace (prefixWord ++ tailWord_3243029) baseStart_3243029 baseEnd_3243029 := by
    simpa [prefixWord, tailWord_3243029, baseEnd_3243029] using wordTrace_append hprefix tailTrace_3243029
  have hstable : (prefixWord ++ tailWord_3243029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243029).length < 2 ^ (prefixWord ++ tailWord_3243029).sum := by decide
  have hdescent : baseEnd_3243029 < baseStart_3243029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243040 : List Nat := [2, 1, 1, 7, 2, 1, 1, 1, 2, 1, 4]
def baseStart_3243040 : Nat := 118140960795 + 3243040 * 2 ^ 59
def prefixEnd_3243040 : Nat := 4983230072969 + 3 ^ 40 * 3243040 * 2
def baseEnd_3243040 : Nat := 1665238301757096824785537

theorem tailTrace_3243040 : CollatzResearch.WordTrace tailWord_3243040 prefixEnd_3243040 1665238301757096824785537 := by
  unfold tailWord_3243040
  simp only [CollatzResearch.WordTrace]
  refine ⟨59141693085513710990747287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78855590780684947987663049 59141693085513710990747287)
  ·
    refine ⟨88712539628270566486120931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59141693085513710990747287 88712539628270566486120931)
    ·
      refine ⟨133068809442405849729181397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88712539628270566486120931 133068809442405849729181397)
      ·
        refine ⟨3118800221306387103027689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 133068809442405849729181397 3118800221306387103027689)
        ·
          refine ⟨2339100165979790327270767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3118800221306387103027689 2339100165979790327270767)
          ·
            refine ⟨3508650248969685490906151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2339100165979790327270767 3508650248969685490906151)
            ·
              refine ⟨5262975373454528236359227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3508650248969685490906151 5262975373454528236359227)
              ·
                refine ⟨7894463060181792354538841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5262975373454528236359227 7894463060181792354538841)
                ·
                  refine ⟨5920847295136344265904131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7894463060181792354538841 5920847295136344265904131)
                  ·
                    refine ⟨8881270942704516398856197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5920847295136344265904131 8881270942704516398856197)
                    ·
                      refine ⟨1665238301757096824785537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8881270942704516398856197 1665238301757096824785537)
                      ·
                        rfl

theorem cell23_3243040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_3243040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243040 prefixEnd_3243040 := by exact prefixLift 3243040
  have htrace : WordTrace (prefixWord ++ tailWord_3243040) baseStart_3243040 baseEnd_3243040 := by
    simpa [prefixWord, tailWord_3243040, baseEnd_3243040] using wordTrace_append hprefix tailTrace_3243040
  have hstable : (prefixWord ++ tailWord_3243040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243040).length < 2 ^ (prefixWord ++ tailWord_3243040).sum := by decide
  have hdescent : baseEnd_3243040 < baseStart_3243040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243050 : List Nat := [3, 1, 4, 1, 3, 1, 2, 3, 1, 4]
def baseStart_3243050 : Nat := 118140960795 + 3243050 * 2 ^ 59
def prefixEnd_3243050 : Nat := 4983230072969 + 3 ^ 40 * 3243050 * 2
def baseEnd_3243050 : Nat := 555081145521213928553497

theorem tailTrace_3243050 : CollatzResearch.WordTrace tailWord_3243050 prefixEnd_3243050 555081145521213928553497 := by
  unfold tailWord_3243050
  simp only [CollatzResearch.WordTrace]
  refine ⟨29570937725247798422339651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78855833933994129126239069 29570937725247798422339651)
  ·
    refine ⟨44356406587871697633509477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29570937725247798422339651 44356406587871697633509477)
    ·
      refine ⟨8316826235225943306283027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44356406587871697633509477 8316826235225943306283027)
      ·
        refine ⟨12475239352838914959424541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8316826235225943306283027 12475239352838914959424541)
        ·
          refine ⟨4678214757314593109784203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12475239352838914959424541 4678214757314593109784203)
          ·
            refine ⟨7017322135971889664676305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4678214757314593109784203 7017322135971889664676305)
            ·
              refine ⟨5262991601978917248507229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7017322135971889664676305 5262991601978917248507229)
              ·
                refine ⟨1973621850742093968190211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5262991601978917248507229 1973621850742093968190211)
                ·
                  refine ⟨2960432776113140952285317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1973621850742093968190211 2960432776113140952285317)
                  ·
                    refine ⟨555081145521213928553497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2960432776113140952285317 555081145521213928553497)
                    ·
                      rfl

theorem cell23_3243050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_3243050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243050 prefixEnd_3243050 := by exact prefixLift 3243050
  have htrace : WordTrace (prefixWord ++ tailWord_3243050) baseStart_3243050 baseEnd_3243050 := by
    simpa [prefixWord, tailWord_3243050, baseEnd_3243050] using wordTrace_append hprefix tailTrace_3243050
  have hstable : (prefixWord ++ tailWord_3243050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243050).length < 2 ^ (prefixWord ++ tailWord_3243050).sum := by decide
  have hdescent : baseEnd_3243050 < baseStart_3243050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243066 : List Nat := [3, 1, 1, 1, 3, 1, 2, 4, 2, 3, 2]
def baseStart_3243066 : Nat := 118140960795 + 3243066 * 2 ^ 59
def prefixEnd_3243066 : Nat := 4983230072969 + 3 ^ 40 * 3243066 * 2
def baseEnd_3243066 : Nat := 1665251652254113723060417

theorem tailTrace_3243066 : CollatzResearch.WordTrace tailWord_3243066 prefixEnd_3243066 1665251652254113723060417 := by
  unfold tailWord_3243066
  simp only [CollatzResearch.WordTrace]
  refine ⟨29571083617233307105485263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78856222979288818947960701 29571083617233307105485263)
  ·
    refine ⟨44356625425849960658227895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29571083617233307105485263 44356625425849960658227895)
    ·
      refine ⟨66534938138774940987341843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44356625425849960658227895 66534938138774940987341843)
      ·
        refine ⟨99802407208162411481012765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66534938138774940987341843 99802407208162411481012765)
        ·
          refine ⟨37425902703060904305379787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99802407208162411481012765 37425902703060904305379787)
          ·
            refine ⟨56138854054591356458069681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37425902703060904305379787 56138854054591356458069681)
            ·
              refine ⟨42104140540943517343552261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56138854054591356458069681 42104140540943517343552261)
              ·
                refine ⟨7894526351426909501916049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42104140540943517343552261 7894526351426909501916049)
                ·
                  refine ⟨5920894763570182126437037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7894526351426909501916049 5920894763570182126437037)
                  ·
                    refine ⟨2220335536338818297413889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5920894763570182126437037 2220335536338818297413889)
                    ·
                      refine ⟨1665251652254113723060417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2220335536338818297413889 1665251652254113723060417)
                      ·
                        rfl

theorem cell23_3243066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 2, 3, 2].length) (baseStart_3243066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243066 prefixEnd_3243066 := by exact prefixLift 3243066
  have htrace : WordTrace (prefixWord ++ tailWord_3243066) baseStart_3243066 baseEnd_3243066 := by
    simpa [prefixWord, tailWord_3243066, baseEnd_3243066] using wordTrace_append hprefix tailTrace_3243066
  have hstable : (prefixWord ++ tailWord_3243066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243066).length < 2 ^ (prefixWord ++ tailWord_3243066).sum := by decide
  have hdescent : baseEnd_3243066 < baseStart_3243066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243089 : List Nat := [1, 2, 2, 1, 3, 1, 5, 1, 1, 6]
def baseStart_3243089 : Nat := 118140960795 + 3243089 * 2 ^ 59
def prefixEnd_3243089 : Nat := 4983230072969 + 3 ^ 40 * 3243089 * 2
def baseEnd_3243089 : Nat := 555087820769722377690937

theorem tailTrace_3243089 : CollatzResearch.WordTrace tailWord_3243089 prefixEnd_3243089 555087820769722377690937 := by
  unfold tailWord_3243089
  simp only [CollatzResearch.WordTrace]
  refine ⟨118285173347849903350028321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78856782231899935566685547 118285173347849903350028321)
  ·
    refine ⟨88713880010887427512521241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118285173347849903350028321 88713880010887427512521241)
    ·
      refine ⟨66535410008165570634390931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88713880010887427512521241 66535410008165570634390931)
      ·
        refine ⟨99803115012248355951586397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66535410008165570634390931 99803115012248355951586397)
        ·
          refine ⟨37426168129593133481844899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99803115012248355951586397 37426168129593133481844899)
          ·
            refine ⟨56139252194389700222767349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37426168129593133481844899 56139252194389700222767349)
            ·
              refine ⟨5263054893224034395884439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56139252194389700222767349 5263054893224034395884439)
              ·
                refine ⟨7894582339836051593826659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5263054893224034395884439 7894582339836051593826659)
                ·
                  refine ⟨11841873509754077390739989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7894582339836051593826659 11841873509754077390739989)
                  ·
                    refine ⟨555087820769722377690937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11841873509754077390739989 555087820769722377690937)
                    ·
                      rfl

theorem cell23_3243089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 6].length) (baseStart_3243089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243089 prefixEnd_3243089 := by exact prefixLift 3243089
  have htrace : WordTrace (prefixWord ++ tailWord_3243089) baseStart_3243089 baseEnd_3243089 := by
    simpa [prefixWord, tailWord_3243089, baseEnd_3243089] using wordTrace_append hprefix tailTrace_3243089
  have hstable : (prefixWord ++ tailWord_3243089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243089).length < 2 ^ (prefixWord ++ tailWord_3243089).sum := by decide
  have hdescent : baseEnd_3243089 < baseStart_3243089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243096 : List Nat := [2, 1, 2, 2, 1, 3, 4, 2, 1, 1, 4]
def baseStart_3243096 : Nat := 118140960795 + 3243096 * 2 ^ 59
def prefixEnd_3243096 : Nat := 4983230072969 + 3 ^ 40 * 3243096 * 2
def baseEnd_3243096 : Nat := 1665267056673748605685279

theorem tailTrace_3243096 : CollatzResearch.WordTrace tailWord_3243096 prefixEnd_3243096 1665267056673748605685279 := by
  unfold tailWord_3243096
  simp only [CollatzResearch.WordTrace]
  refine ⟨59142714329412271772766571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78856952439216362363688761 59142714329412271772766571)
  ·
    refine ⟨88714071494118407659149857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59142714329412271772766571 88714071494118407659149857)
    ·
      refine ⟨66535553620588805744362393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88714071494118407659149857 66535553620588805744362393)
      ·
        refine ⟨49901665215441604308271795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66535553620588805744362393 49901665215441604308271795)
        ·
          refine ⟨74852497823162406462407693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49901665215441604308271795 74852497823162406462407693)
          ·
            refine ⟨28069686683685902423402885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74852497823162406462407693 28069686683685902423402885)
            ·
              refine ⟨5263066253191106704388041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28069686683685902423402885 5263066253191106704388041)
              ·
                refine ⟨3947299689893330028291031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5263066253191106704388041 3947299689893330028291031)
                ·
                  refine ⟨5920949534839995042436547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3947299689893330028291031 5920949534839995042436547)
                  ·
                    refine ⟨8881424302259992563654821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5920949534839995042436547 8881424302259992563654821)
                    ·
                      refine ⟨1665267056673748605685279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8881424302259992563654821 1665267056673748605685279)
                      ·
                        rfl

theorem cell23_3243096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_3243096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243096 prefixEnd_3243096 := by exact prefixLift 3243096
  have htrace : WordTrace (prefixWord ++ tailWord_3243096) baseStart_3243096 baseEnd_3243096 := by
    simpa [prefixWord, tailWord_3243096, baseEnd_3243096] using wordTrace_append hprefix tailTrace_3243096
  have hstable : (prefixWord ++ tailWord_3243096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243096).length < 2 ^ (prefixWord ++ tailWord_3243096).sum := by decide
  have hdescent : baseEnd_3243096 < baseStart_3243096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243109 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 3, 2, 4]
def baseStart_3243109 : Nat := 118140960795 + 3243109 * 2 ^ 59
def prefixEnd_3243109 : Nat := 4983230072969 + 3 ^ 40 * 3243109 * 2
def baseEnd_3243109 : Nat := 1665273731922257054822719

theorem tailTrace_3243109 : CollatzResearch.WordTrace tailWord_3243109 prefixEnd_3243109 1665273731922257054822719 := by
  unfold tailWord_3243109
  simp only [CollatzResearch.WordTrace]
  refine ⟨118285902807777446765756381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78857268538518297843837587 118285902807777446765756381)
  ·
    refine ⟨44357213552916542537158643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118285902807777446765756381 44357213552916542537158643)
    ·
      refine ⟨66535820329374813805737965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44357213552916542537158643 66535820329374813805737965)
      ·
        refine ⟨24950932623515555177151737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66535820329374813805737965 24950932623515555177151737)
        ·
          refine ⟨18713199467636666382863803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24950932623515555177151737 18713199467636666382863803)
          ·
            refine ⟨28069799201454999574295705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18713199467636666382863803 28069799201454999574295705)
            ·
              refine ⟨21052349401091249680721779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28069799201454999574295705 21052349401091249680721779)
              ·
                refine ⟨31578524101636874521082669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21052349401091249680721779 31578524101636874521082669)
                ·
                  refine ⟨11841946538113827945406001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31578524101636874521082669 11841946538113827945406001)
                  ·
                    refine ⟨8881459903585370959054501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11841946538113827945406001 8881459903585370959054501)
                    ·
                      refine ⟨1665273731922257054822719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8881459903585370959054501 1665273731922257054822719)
                      ·
                        rfl

theorem cell23_3243109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_3243109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243109 prefixEnd_3243109 := by exact prefixLift 3243109
  have htrace : WordTrace (prefixWord ++ tailWord_3243109) baseStart_3243109 baseEnd_3243109 := by
    simpa [prefixWord, tailWord_3243109, baseEnd_3243109] using wordTrace_append hprefix tailTrace_3243109
  have hstable : (prefixWord ++ tailWord_3243109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243109).length < 2 ^ (prefixWord ++ tailWord_3243109).sum := by decide
  have hdescent : baseEnd_3243109 < baseStart_3243109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243116 : List Nat := [2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 3]
def baseStart_3243116 : Nat := 118140960795 + 3243116 * 2 ^ 59
def prefixEnd_3243116 : Nat := 4983230072969 + 3 ^ 40 * 3243116 * 2
def baseEnd_3243116 : Nat := 1665277326286838527435187

theorem tailTrace_3243116 : CollatzResearch.WordTrace tailWord_3243116 prefixEnd_3243116 1665277326286838527435187 := by
  unfold tailWord_3243116
  simp only [CollatzResearch.WordTrace]
  refine ⟨59143079059376043480630601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78857438745834724640840801 59143079059376043480630601)
  ·
    refine ⟨44357309294532032610472951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59143079059376043480630601 44357309294532032610472951)
    ·
      refine ⟨66535963941798048915709427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44357309294532032610472951 66535963941798048915709427)
      ·
        refine ⟨99803945912697073373564141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66535963941798048915709427 99803945912697073373564141)
        ·
          refine ⟨37426479717261402515086553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99803945912697073373564141 37426479717261402515086553)
          ·
            refine ⟨28069859787946051886314915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37426479717261402515086553 28069859787946051886314915)
            ·
              refine ⟨42104789681919077829472373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28069859787946051886314915 42104789681919077829472373)
              ·
                refine ⟨3947324032679913546513035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42104789681919077829472373 3947324032679913546513035)
                ·
                  refine ⟨5920986049019870319769553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3947324032679913546513035 5920986049019870319769553)
                  ·
                    refine ⟨4440739536764902739827165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5920986049019870319769553 4440739536764902739827165)
                    ·
                      refine ⟨1665277326286838527435187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4440739536764902739827165 1665277326286838527435187)
                      ·
                        rfl

theorem cell23_3243116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 3].length) (baseStart_3243116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243116 prefixEnd_3243116 := by exact prefixLift 3243116
  have htrace : WordTrace (prefixWord ++ tailWord_3243116) baseStart_3243116 baseEnd_3243116 := by
    simpa [prefixWord, tailWord_3243116, baseEnd_3243116] using wordTrace_append hprefix tailTrace_3243116
  have hstable : (prefixWord ++ tailWord_3243116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243116).length < 2 ^ (prefixWord ++ tailWord_3243116).sum := by decide
  have hdescent : baseEnd_3243116 < baseStart_3243116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243140 : List Nat := [2, 3, 2, 1, 2, 4, 2, 1, 2, 4]
def baseStart_3243140 : Nat := 118140960795 + 3243140 * 2 ^ 59
def prefixEnd_3243140 : Nat := 4983230072969 + 3 ^ 40 * 3243140 * 2
def baseEnd_3243140 : Nat := 555096549940848811178359

theorem tailTrace_3243140 : CollatzResearch.WordTrace tailWord_3243140 prefixEnd_3243140 555096549940848811178359 := by
  unfold tailWord_3243140
  simp only [CollatzResearch.WordTrace]
  refine ⟨59143516735332569530067437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78858022313776759373423249 59143516735332569530067437)
  ·
    refine ⟨22178818775749713573775289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59143516735332569530067437 22178818775749713573775289)
    ·
      refine ⟨16634114081812285180331467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22178818775749713573775289 16634114081812285180331467)
      ·
        refine ⟨24951171122718427770497201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16634114081812285180331467 24951171122718427770497201)
        ·
          refine ⟨18713378342038820827872901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24951171122718427770497201 18713378342038820827872901)
          ·
            refine ⟨3508758439132278905226169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18713378342038820827872901 3508758439132278905226169)
            ·
              refine ⟨2631568829349209178919627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3508758439132278905226169 2631568829349209178919627)
              ·
                refine ⟨3947353244023813768379441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2631568829349209178919627 3947353244023813768379441)
                ·
                  refine ⟨2960514933017860326284581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3947353244023813768379441 2960514933017860326284581)
                  ·
                    refine ⟨555096549940848811178359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2960514933017860326284581 555096549940848811178359)
                    ·
                      rfl

theorem cell23_3243140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_3243140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243140 prefixEnd_3243140 := by exact prefixLift 3243140
  have htrace : WordTrace (prefixWord ++ tailWord_3243140) baseStart_3243140 baseEnd_3243140 := by
    simpa [prefixWord, tailWord_3243140, baseEnd_3243140] using wordTrace_append hprefix tailTrace_3243140
  have hstable : (prefixWord ++ tailWord_3243140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243140).length < 2 ^ (prefixWord ++ tailWord_3243140).sum := by decide
  have hdescent : baseEnd_3243140 < baseStart_3243140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243146 : List Nat := [3, 1, 2, 3, 1, 1, 2, 3, 1, 3, 3]
def baseStart_3243146 : Nat := 118140960795 + 3243146 * 2 ^ 59
def prefixEnd_3243146 : Nat := 4983230072969 + 3 ^ 40 * 3243146 * 2
def baseEnd_3243146 : Nat := 1665292730706473410060049

theorem tailTrace_3243146 : CollatzResearch.WordTrace tailWord_3243146 prefixEnd_3243146 1665292730706473410060049 := by
  unfold tailWord_3243146
  simp only [CollatzResearch.WordTrace]
  refine ⟨29571813077160850521213323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78858168205762268056568861 29571813077160850521213323)
  ·
    refine ⟨44357719615741275781819985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29571813077160850521213323 44357719615741275781819985)
    ·
      refine ⟨33268289711805956836364989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44357719615741275781819985 33268289711805956836364989)
      ·
        refine ⟨12475608641927233813636871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33268289711805956836364989 12475608641927233813636871)
        ·
          refine ⟨18713412962890850720455307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12475608641927233813636871 18713412962890850720455307)
          ·
            refine ⟨28070119444336276080682961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18713412962890850720455307 28070119444336276080682961)
            ·
              refine ⟨21052589583252207060512221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28070119444336276080682961 21052589583252207060512221)
              ·
                refine ⟨7894721093719577647692083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21052589583252207060512221 7894721093719577647692083)
                ·
                  refine ⟨11842081640579366471538125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7894721093719577647692083 11842081640579366471538125)
                  ·
                    refine ⟨4440780615217262426826797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11842081640579366471538125 4440780615217262426826797)
                    ·
                      refine ⟨1665292730706473410060049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4440780615217262426826797 1665292730706473410060049)
                      ·
                        rfl

theorem cell23_3243146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_3243146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243146 prefixEnd_3243146 := by exact prefixLift 3243146
  have htrace : WordTrace (prefixWord ++ tailWord_3243146) baseStart_3243146 baseEnd_3243146 := by
    simpa [prefixWord, tailWord_3243146, baseEnd_3243146] using wordTrace_append hprefix tailTrace_3243146
  have hstable : (prefixWord ++ tailWord_3243146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243146).length < 2 ^ (prefixWord ++ tailWord_3243146).sum := by decide
  have hdescent : baseEnd_3243146 < baseStart_3243146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243150 : List Nat := [4, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3]
def baseStart_3243150 : Nat := 118140960795 + 3243150 * 2 ^ 59
def prefixEnd_3243150 : Nat := 4983230072969 + 3 ^ 40 * 3243150 * 2
def baseEnd_3243150 : Nat := 1665294784629091394410031

theorem tailTrace_3243150 : CollatzResearch.WordTrace tailWord_3243150 prefixEnd_3243150 1665294784629091394410031 := by
  unfold tailWord_3243150
  simp only [CollatzResearch.WordTrace]
  refine ⟨14785924775078613845999863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78858265467085940511999269 14785924775078613845999863)
  ·
    refine ⟨22178887162617920768999795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14785924775078613845999863 22178887162617920768999795)
    ·
      refine ⟨33268330743926881153499693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22178887162617920768999795 33268330743926881153499693)
      ·
        refine ⟨12475624028972580432562385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33268330743926881153499693 12475624028972580432562385)
        ·
          refine ⟨9356718021729435324421789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12475624028972580432562385 9356718021729435324421789)
          ·
            refine ⟨3508769258148538246658171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9356718021729435324421789 3508769258148538246658171)
            ·
              refine ⟨5263153887222807369987257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3508769258148538246658171 5263153887222807369987257)
              ·
                refine ⟨3947365415417105527490443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5263153887222807369987257 3947365415417105527490443)
                ·
                  refine ⟨5921048123125658291235665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3947365415417105527490443 5921048123125658291235665)
                  ·
                    refine ⟨4440786092344243718426749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5921048123125658291235665 4440786092344243718426749)
                    ·
                      refine ⟨1665294784629091394410031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4440786092344243718426749 1665294784629091394410031)
                      ·
                        rfl

theorem cell23_3243150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_3243150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243150 prefixEnd_3243150 := by exact prefixLift 3243150
  have htrace : WordTrace (prefixWord ++ tailWord_3243150) baseStart_3243150 baseEnd_3243150 := by
    simpa [prefixWord, tailWord_3243150, baseEnd_3243150] using wordTrace_append hprefix tailTrace_3243150
  have hstable : (prefixWord ++ tailWord_3243150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243150).length < 2 ^ (prefixWord ++ tailWord_3243150).sum := by decide
  have hdescent : baseEnd_3243150 < baseStart_3243150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243181 : List Nat := [1, 5, 2, 1, 3, 2, 2, 2, 1, 2, 2]
def baseStart_3243181 : Nat := 118140960795 + 3243181 * 2 ^ 59
def prefixEnd_3243181 : Nat := 4983230072969 + 3 ^ 40 * 3243181 * 2
def baseEnd_3243181 : Nat := 1665310702529380773122389

theorem tailTrace_3243181 : CollatzResearch.WordTrace tailWord_3243181 prefixEnd_3243181 1665310702529380773122389 := by
  unfold tailWord_3243181
  simp only [CollatzResearch.WordTrace]
  refine ⟨118288528863516603062377397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78859019242344402041584931 118288528863516603062377397)
  ·
    refine ⟨11089549580954681537097881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118288528863516603062377397 11089549580954681537097881)
    ·
      refine ⟨8317162185716011152823411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11089549580954681537097881 8317162185716011152823411)
      ·
        refine ⟨12475743278574016729235117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8317162185716011152823411 12475743278574016729235117)
        ·
          refine ⟨4678403729465256273463169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12475743278574016729235117 4678403729465256273463169)
          ·
            refine ⟨3508802797098942205097377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4678403729465256273463169 3508802797098942205097377)
            ·
              refine ⟨2631602097824206653823033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3508802797098942205097377 2631602097824206653823033)
              ·
                refine ⟨1973701573368154990367275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2631602097824206653823033 1973701573368154990367275)
                ·
                  refine ⟨2960552360052232485550913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1973701573368154990367275 2960552360052232485550913)
                  ·
                    refine ⟨2220414270039174364163185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2960552360052232485550913 2220414270039174364163185)
                    ·
                      refine ⟨1665310702529380773122389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2220414270039174364163185 1665310702529380773122389)
                      ·
                        rfl

theorem cell23_3243181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_3243181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243181 prefixEnd_3243181 := by exact prefixLift 3243181
  have htrace : WordTrace (prefixWord ++ tailWord_3243181) baseStart_3243181 baseEnd_3243181 := by
    simpa [prefixWord, tailWord_3243181, baseEnd_3243181] using wordTrace_append hprefix tailTrace_3243181
  have hstable : (prefixWord ++ tailWord_3243181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243181).length < 2 ^ (prefixWord ++ tailWord_3243181).sum := by decide
  have hdescent : baseEnd_3243181 < baseStart_3243181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243196 : List Nat := [2, 2, 2, 3, 2, 2, 1, 1, 2, 6]
def baseStart_3243196 : Nat := 118140960795 + 3243196 * 2 ^ 59
def prefixEnd_3243196 : Nat := 4983230072969 + 3 ^ 40 * 3243196 * 2
def baseEnd_3243196 : Nat := 555106134913066071478273

theorem tailTrace_3243196 : CollatzResearch.WordTrace tailWord_3243196 prefixEnd_3243196 555106134913066071478273 := by
  unfold tailWord_3243196
  simp only [CollatzResearch.WordTrace]
  refine ⟨59144537979231130312086721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78859383972308173749448961 59144537979231130312086721)
  ·
    refine ⟨44358403484423347734065041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59144537979231130312086721 44358403484423347734065041)
    ·
      refine ⟨33268802613317510800548781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44358403484423347734065041 33268802613317510800548781)
      ·
        refine ⟨12475800979994066550205793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33268802613317510800548781 12475800979994066550205793)
        ·
          refine ⟨9356850734995549912654345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12475800979994066550205793 9356850734995549912654345)
          ·
            refine ⟨7017638051246662434490759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9356850734995549912654345 7017638051246662434490759)
            ·
              refine ⟨10526457076869993651736139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7017638051246662434490759 10526457076869993651736139)
              ·
                refine ⟨15789685615304990477604209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10526457076869993651736139 15789685615304990477604209)
                ·
                  refine ⟨11842264211478742858203157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15789685615304990477604209 11842264211478742858203157)
                  ·
                    refine ⟨555106134913066071478273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11842264211478742858203157 555106134913066071478273)
                    ·
                      rfl

theorem cell23_3243196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_3243196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243196 prefixEnd_3243196 := by exact prefixLift 3243196
  have htrace : WordTrace (prefixWord ++ tailWord_3243196) baseStart_3243196 baseEnd_3243196 := by
    simpa [prefixWord, tailWord_3243196, baseEnd_3243196] using wordTrace_append hprefix tailTrace_3243196
  have hstable : (prefixWord ++ tailWord_3243196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243196).length < 2 ^ (prefixWord ++ tailWord_3243196).sum := by decide
  have hdescent : baseEnd_3243196 < baseStart_3243196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243199 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 4]
def baseStart_3243199 : Nat := 118140960795 + 3243199 * 2 ^ 59
def prefixEnd_3243199 : Nat := 4983230072969 + 3 ^ 40 * 3243199 * 2
def baseEnd_3243199 : Nat := 1665319945181161702697305

theorem tailTrace_3243199 : CollatzResearch.WordTrace tailWord_3243199 prefixEnd_3243199 1665319945181161702697305 := by
  unfold tailWord_3243199
  simp only [CollatzResearch.WordTrace]
  refine ⟨118289185377451392136532651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78859456918300928091021767 118289185377451392136532651)
  ·
    refine ⟨177433778066177088204798977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118289185377451392136532651 177433778066177088204798977)
    ·
      refine ⟨133075333549632816153599233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177433778066177088204798977 133075333549632816153599233)
      ·
        refine ⟨99806500162224612115199425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133075333549632816153599233 99806500162224612115199425)
        ·
          refine ⟨74854875121668459086399569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99806500162224612115199425 74854875121668459086399569)
          ·
            refine ⟨56141156341251344314799677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74854875121668459086399569 56141156341251344314799677)
            ·
              refine ⟨21052933627969254118049879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56141156341251344314799677 21052933627969254118049879)
              ·
                refine ⟨31579400441953881177074819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21052933627969254118049879 31579400441953881177074819)
                ·
                  refine ⟨47369100662930821765612229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31579400441953881177074819 47369100662930821765612229)
                  ·
                    refine ⟨8881706374299529081052293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47369100662930821765612229 8881706374299529081052293)
                    ·
                      refine ⟨1665319945181161702697305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8881706374299529081052293 1665319945181161702697305)
                      ·
                        rfl

theorem cell23_3243199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_3243199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243199 prefixEnd_3243199 := by exact prefixLift 3243199
  have htrace : WordTrace (prefixWord ++ tailWord_3243199) baseStart_3243199 baseEnd_3243199 := by
    simpa [prefixWord, tailWord_3243199, baseEnd_3243199] using wordTrace_append hprefix tailTrace_3243199
  have hstable : (prefixWord ++ tailWord_3243199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243199).length < 2 ^ (prefixWord ++ tailWord_3243199).sum := by decide
  have hdescent : baseEnd_3243199 < baseStart_3243199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243224 : List Nat := [2, 1, 2, 2, 6, 1, 2, 1, 1, 3, 2]
def baseStart_3243224 : Nat := 118140960795 + 3243224 * 2 ^ 59
def prefixEnd_3243224 : Nat := 4983230072969 + 3 ^ 40 * 3243224 * 2
def baseEnd_3243224 : Nat := 1665332782197524104884691

theorem tailTrace_3243224 : CollatzResearch.WordTrace tailWord_3243224 prefixEnd_3243224 1665332782197524104884691 := by
  unfold tailWord_3243224
  simp only [CollatzResearch.WordTrace]
  refine ⟨59145048601180410703096363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78860064801573880937461817 59145048601180410703096363)
  ·
    refine ⟨88717572901770616054644545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59145048601180410703096363 88717572901770616054644545)
    ·
      refine ⟨66538179676327962040983409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88717572901770616054644545 66538179676327962040983409)
      ·
        refine ⟨49903634757245971530737557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66538179676327962040983409 49903634757245971530737557)
        ·
          refine ⟨2339232879245904915503323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49903634757245971530737557 2339232879245904915503323)
          ·
            refine ⟨3508849318868857373254985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2339232879245904915503323 3508849318868857373254985)
            ·
              refine ⟨2631636989151643029941239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3508849318868857373254985 2631636989151643029941239)
              ·
                refine ⟨3947455483727464544911859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2631636989151643029941239 3947455483727464544911859)
                ·
                  refine ⟨5921183225591196817367789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3947455483727464544911859 5921183225591196817367789)
                  ·
                    refine ⟨2220443709596698806512921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5921183225591196817367789 2220443709596698806512921)
                    ·
                      refine ⟨1665332782197524104884691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2220443709596698806512921 1665332782197524104884691)
                      ·
                        rfl

theorem cell23_3243224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 1, 3, 2].length) (baseStart_3243224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243224 prefixEnd_3243224 := by exact prefixLift 3243224
  have htrace : WordTrace (prefixWord ++ tailWord_3243224) baseStart_3243224 baseEnd_3243224 := by
    simpa [prefixWord, tailWord_3243224, baseEnd_3243224] using wordTrace_append hprefix tailTrace_3243224
  have hstable : (prefixWord ++ tailWord_3243224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243224).length < 2 ^ (prefixWord ++ tailWord_3243224).sum := by decide
  have hdescent : baseEnd_3243224 < baseStart_3243224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243236 : List Nat := [2, 3, 1, 1, 1, 2, 3, 2, 2, 3, 3]
def baseStart_3243236 : Nat := 118140960795 + 3243236 * 2 ^ 59
def prefixEnd_3243236 : Nat := 4983230072969 + 3 ^ 40 * 3243236 * 2
def baseEnd_3243236 : Nat := 1665338943965378057934635

theorem tailTrace_3243236 : CollatzResearch.WordTrace tailWord_3243236 prefixEnd_3243236 1665338943965378057934635 := by
  unfold tailWord_3243236
  simp only [CollatzResearch.WordTrace]
  refine ⟨59145267439158673727814781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78860356585544898303753041 59145267439158673727814781)
  ·
    refine ⟨22179475289684502647930543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59145267439158673727814781 22179475289684502647930543)
    ·
      refine ⟨33269212934526753971895815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22179475289684502647930543 33269212934526753971895815)
      ·
        refine ⟨49903819401790130957843723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33269212934526753971895815 49903819401790130957843723)
        ·
          refine ⟨74855729102685196436765585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49903819401790130957843723 74855729102685196436765585)
          ·
            refine ⟨56141796827013897327574189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74855729102685196436765585 56141796827013897327574189)
            ·
              refine ⟨21053173810130211497840321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56141796827013897327574189 21053173810130211497840321)
              ·
                refine ⟨15789880357597658623380241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21053173810130211497840321 15789880357597658623380241)
                ·
                  refine ⟨11842410268198243967535181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15789880357597658623380241 11842410268198243967535181)
                  ·
                    refine ⟨4440903850574341487825693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11842410268198243967535181 4440903850574341487825693)
                    ·
                      refine ⟨1665338943965378057934635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4440903850574341487825693 1665338943965378057934635)
                      ·
                        rfl

theorem cell23_3243236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_3243236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243236 prefixEnd_3243236 := by exact prefixLift 3243236
  have htrace : WordTrace (prefixWord ++ tailWord_3243236) baseStart_3243236 baseEnd_3243236 := by
    simpa [prefixWord, tailWord_3243236, baseEnd_3243236] using wordTrace_append hprefix tailTrace_3243236
  have hstable : (prefixWord ++ tailWord_3243236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243236).length < 2 ^ (prefixWord ++ tailWord_3243236).sum := by decide
  have hdescent : baseEnd_3243236 < baseStart_3243236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243249 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 1, 1, 7]
def baseStart_3243249 : Nat := 118140960795 + 3243249 * 2 ^ 59
def prefixEnd_3243249 : Nat := 4983230072969 + 3 ^ 40 * 3243249 * 2
def baseEnd_3243249 : Nat := 1665345619213886507072075

theorem tailTrace_3243249 : CollatzResearch.WordTrace tailWord_3243249 prefixEnd_3243249 1665345619213886507072075 := by
  unfold tailWord_3243249
  simp only [CollatzResearch.WordTrace]
  refine ⟨118291009027270250675852801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78860672684846833783901867 118291009027270250675852801)
  ·
    refine ⟨88718256770452688006889601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118291009027270250675852801 88718256770452688006889601)
    ·
      refine ⟨66538692577839516005167201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88718256770452688006889601 66538692577839516005167201)
      ·
        refine ⟨49904019433379637003875401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66538692577839516005167201 49904019433379637003875401)
        ·
          refine ⟨37428014575034727752906551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49904019433379637003875401 37428014575034727752906551)
          ·
            refine ⟨56142021862552091629359827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37428014575034727752906551 56142021862552091629359827)
            ·
              refine ⟨84213032793828137444039741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56142021862552091629359827 84213032793828137444039741)
              ·
                refine ⟨31579887297685551541514903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84213032793828137444039741 31579887297685551541514903)
                ·
                  refine ⟨47369830946528327312272355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31579887297685551541514903 47369830946528327312272355)
                  ·
                    refine ⟨71054746419792490968408533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47369830946528327312272355 71054746419792490968408533)
                    ·
                      refine ⟨1665345619213886507072075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 71054746419792490968408533 1665345619213886507072075)
                      ·
                        rfl

theorem cell23_3243249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_3243249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243249 prefixEnd_3243249 := by exact prefixLift 3243249
  have htrace : WordTrace (prefixWord ++ tailWord_3243249) baseStart_3243249 baseEnd_3243249 := by
    simpa [prefixWord, tailWord_3243249, baseEnd_3243249] using wordTrace_append hprefix tailTrace_3243249
  have hstable : (prefixWord ++ tailWord_3243249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243249).length < 2 ^ (prefixWord ++ tailWord_3243249).sum := by decide
  have hdescent : baseEnd_3243249 < baseStart_3243249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243269 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 2, 8]
def baseStart_3243269 : Nat := 118140960795 + 3243269 * 2 ^ 59
def prefixEnd_3243269 : Nat := 4983230072969 + 3 ^ 40 * 3243269 * 2
def baseEnd_3243269 : Nat := 555118629608992142940661

theorem tailTrace_3243269 : CollatzResearch.WordTrace tailWord_3243269 prefixEnd_3243269 555118629608992142940661 := by
  unfold tailWord_3243269
  simp only [CollatzResearch.WordTrace]
  refine ⟨118291738487197794091580861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78861158991465196061053907 118291738487197794091580861)
  ·
    refine ⟨44359401932699172784342823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118291738487197794091580861 44359401932699172784342823)
    ·
      refine ⟨66539102899048759176514235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44359401932699172784342823 66539102899048759176514235)
      ·
        refine ⟨99808654348573138764771353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66539102899048759176514235 99808654348573138764771353)
        ·
          refine ⟨74856490761429854073578515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99808654348573138764771353 74856490761429854073578515)
          ·
            refine ⟨112284736142144781110367773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74856490761429854073578515 112284736142144781110367773)
            ·
              refine ⟨42106776053304292916387915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112284736142144781110367773 42106776053304292916387915)
              ·
                refine ⟨63160164079956439374581873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42106776053304292916387915 63160164079956439374581873)
                ·
                  refine ⟨47370123059967329530936405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63160164079956439374581873 47370123059967329530936405)
                  ·
                    refine ⟨555118629608992142940661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47370123059967329530936405 555118629608992142940661)
                    ·
                      rfl

theorem cell23_3243269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 8].length) (baseStart_3243269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243269 prefixEnd_3243269 := by exact prefixLift 3243269
  have htrace : WordTrace (prefixWord ++ tailWord_3243269) baseStart_3243269 baseEnd_3243269 := by
    simpa [prefixWord, tailWord_3243269, baseEnd_3243269] using wordTrace_append hprefix tailTrace_3243269
  have hstable : (prefixWord ++ tailWord_3243269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243269).length < 2 ^ (prefixWord ++ tailWord_3243269).sum := by decide
  have hdescent : baseEnd_3243269 < baseStart_3243269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243276 : List Nat := [2, 2, 1, 2, 2, 3, 2, 1, 1, 3, 4]
def baseStart_3243276 : Nat := 118140960795 + 3243276 * 2 ^ 59
def prefixEnd_3243276 : Nat := 4983230072969 + 3 ^ 40 * 3243276 * 2
def baseEnd_3243276 : Nat := 1665359483191557901434451

theorem tailTrace_3243276 : CollatzResearch.WordTrace tailWord_3243276 prefixEnd_3243276 1665359483191557901434451 := by
  unfold tailWord_3243276
  simp only [CollatzResearch.WordTrace]
  refine ⟨59145996899086217143542841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78861329198781622858057121 59145996899086217143542841)
  ·
    refine ⟨44359497674314662857657131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59145996899086217143542841 44359497674314662857657131)
    ·
      refine ⟨66539246511471994286485697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44359497674314662857657131 66539246511471994286485697)
      ·
        refine ⟨49904434883603995714864273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66539246511471994286485697 49904434883603995714864273)
        ·
          refine ⟨37428326162702996786148205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49904434883603995714864273 37428326162702996786148205)
          ·
            refine ⟨14035622311013623794805577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37428326162702996786148205 14035622311013623794805577)
            ·
              refine ⟨10526716733260217846104183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14035622311013623794805577 10526716733260217846104183)
              ·
                refine ⟨15790075099890326769156275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10526716733260217846104183 15790075099890326769156275)
                ·
                  refine ⟨23685112649835490153734413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15790075099890326769156275 23685112649835490153734413)
                  ·
                    refine ⟨8881917243688308807650405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23685112649835490153734413 8881917243688308807650405)
                    ·
                      refine ⟨1665359483191557901434451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8881917243688308807650405 1665359483191557901434451)
                      ·
                        rfl

theorem cell23_3243276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_3243276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243276 prefixEnd_3243276 := by exact prefixLift 3243276
  have htrace : WordTrace (prefixWord ++ tailWord_3243276) baseStart_3243276 baseEnd_3243276 := by
    simpa [prefixWord, tailWord_3243276, baseEnd_3243276] using wordTrace_append hprefix tailTrace_3243276
  have hstable : (prefixWord ++ tailWord_3243276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243276).length < 2 ^ (prefixWord ++ tailWord_3243276).sum := by decide
  have hdescent : baseEnd_3243276 < baseStart_3243276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243279 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 5]
def baseStart_3243279 : Nat := 118140960795 + 3243279 * 2 ^ 59
def prefixEnd_3243279 : Nat := 4983230072969 + 3 ^ 40 * 3243279 * 2
def baseEnd_3243279 : Nat := 1665361023633521389696937

theorem tailTrace_3243279 : CollatzResearch.WordTrace tailWord_3243279 prefixEnd_3243279 1665361023633521389696937 := by
  unfold tailWord_3243279
  simp only [CollatzResearch.WordTrace]
  refine ⟨118292103217161565799444891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78861402144774377199629927 118292103217161565799444891)
  ·
    refine ⟨177438154825742348699167337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118292103217161565799444891 177438154825742348699167337)
    ·
      refine ⟨133078616119306761524375503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177438154825742348699167337 133078616119306761524375503)
      ·
        refine ⟨199617924178960142286563255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133078616119306761524375503 199617924178960142286563255)
        ·
          refine ⟨299426886268440213429844883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199617924178960142286563255 299426886268440213429844883)
          ·
            refine ⟨449140329402660320144767325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299426886268440213429844883 449140329402660320144767325)
            ·
              refine ⟨168427623525997620054287747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 449140329402660320144767325 168427623525997620054287747)
              ·
                refine ⟨252641435288996430081431621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168427623525997620054287747 252641435288996430081431621)
                ·
                  refine ⟨47370269116686830640268429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 252641435288996430081431621 47370269116686830640268429)
                  ·
                    refine ⟨17763850918757561490100661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47370269116686830640268429 17763850918757561490100661)
                    ·
                      refine ⟨1665361023633521389696937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17763850918757561490100661 1665361023633521389696937)
                      ·
                        rfl

theorem cell23_3243279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 5].length) (baseStart_3243279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243279 prefixEnd_3243279 := by exact prefixLift 3243279
  have htrace : WordTrace (prefixWord ++ tailWord_3243279) baseStart_3243279 baseEnd_3243279 := by
    simpa [prefixWord, tailWord_3243279, baseEnd_3243279] using wordTrace_append hprefix tailTrace_3243279
  have hstable : (prefixWord ++ tailWord_3243279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243279).length < 2 ^ (prefixWord ++ tailWord_3243279).sum := by decide
  have hdescent : baseEnd_3243279 < baseStart_3243279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243293 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 4, 1, 4]
def baseStart_3243293 : Nat := 118140960795 + 3243293 * 2 ^ 59
def prefixEnd_3243293 : Nat := 4983230072969 + 3 ^ 40 * 3243293 * 2
def baseEnd_3243293 : Nat := 1665368212362684334921873

theorem tailTrace_3243293 : CollatzResearch.WordTrace tailWord_3243293 prefixEnd_3243293 1665368212362684334921873 := by
  unfold tailWord_3243293
  simp only [CollatzResearch.WordTrace]
  refine ⟨118292613839110846190454533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78861742559407230793636355 118292613839110846190454533)
  ·
    refine ⟨22179865094833283660710225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118292613839110846190454533 22179865094833283660710225)
    ·
      refine ⟨16634898821124962745532669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22179865094833283660710225 16634898821124962745532669)
      ·
        refine ⟨6238087057921861029574751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16634898821124962745532669 6238087057921861029574751)
        ·
          refine ⟨9357130586882791544362127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6238087057921861029574751 9357130586882791544362127)
          ·
            refine ⟨14035695880324187316543191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9357130586882791544362127 14035695880324187316543191)
            ·
              refine ⟨21053543820486280974814787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14035695880324187316543191 21053543820486280974814787)
              ·
                refine ⟨31580315730729421462222181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21053543820486280974814787 31580315730729421462222181)
                ·
                  refine ⟨5921309199511766524166659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31580315730729421462222181 5921309199511766524166659)
                  ·
                    refine ⟨8881963799267649786249989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5921309199511766524166659 8881963799267649786249989)
                    ·
                      refine ⟨1665368212362684334921873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8881963799267649786249989 1665368212362684334921873)
                      ·
                        rfl

theorem cell23_3243293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_3243293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243293 prefixEnd_3243293 := by exact prefixLift 3243293
  have htrace : WordTrace (prefixWord ++ tailWord_3243293) baseStart_3243293 baseEnd_3243293 := by
    simpa [prefixWord, tailWord_3243293, baseEnd_3243293] using wordTrace_append hprefix tailTrace_3243293
  have hstable : (prefixWord ++ tailWord_3243293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243293).length < 2 ^ (prefixWord ++ tailWord_3243293).sum := by decide
  have hdescent : baseEnd_3243293 < baseStart_3243293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243294 : List Nat := [4, 3, 2, 1, 2, 1, 3, 2, 5]
def baseStart_3243294 : Nat := 118140960795 + 3243294 * 2 ^ 59
def prefixEnd_3243294 : Nat := 4983230072969 + 3 ^ 40 * 3243294 * 2
def baseEnd_3243294 : Nat := 185040969538148759001041

theorem tailTrace_3243294 : CollatzResearch.WordTrace tailWord_3243294 prefixEnd_3243294 185040969538148759001041 := by
  unfold tailWord_3243294
  simp only [CollatzResearch.WordTrace]
  refine ⟨14786581289013402920155117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78861766874738148907493957 14786581289013402920155117)
  ·
    refine ⟨5544967983380026095058169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14786581289013402920155117 5544967983380026095058169)
    ·
      refine ⟨4158725987535019571293627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5544967983380026095058169 4158725987535019571293627)
      ·
        refine ⟨6238088981302529356940441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4158725987535019571293627 6238088981302529356940441)
        ·
          refine ⟨4678566735976897017705331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6238088981302529356940441 4678566735976897017705331)
          ·
            refine ⟨7017850103965345526557997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4678566735976897017705331 7017850103965345526557997)
            ·
              refine ⟨2631693788987004572459249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7017850103965345526557997 2631693788987004572459249)
              ·
                refine ⟨1973770341740253429344437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2631693788987004572459249 1973770341740253429344437)
                ·
                  refine ⟨185040969538148759001041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1973770341740253429344437 185040969538148759001041)
                  ·
                    rfl

theorem cell23_3243294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_3243294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243294 prefixEnd_3243294 := by exact prefixLift 3243294
  have htrace : WordTrace (prefixWord ++ tailWord_3243294) baseStart_3243294 baseEnd_3243294 := by
    simpa [prefixWord, tailWord_3243294, baseEnd_3243294] using wordTrace_append hprefix tailTrace_3243294
  have hstable : (prefixWord ++ tailWord_3243294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243294).length < 2 ^ (prefixWord ++ tailWord_3243294).sum := by decide
  have hdescent : baseEnd_3243294 < baseStart_3243294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243383 : List Nat := [1, 1, 3, 1, 1, 2, 4, 4, 1, 1, 4]
def baseStart_3243383 : Nat := 118140960795 + 3243383 * 2 ^ 59
def prefixEnd_3243383 : Nat := 4983230072969 + 3 ^ 40 * 3243383 * 2
def baseEnd_3243383 : Nat := 1665414425621588982796459

theorem tailTrace_3243383 : CollatzResearch.WordTrace tailWord_3243383 prefixEnd_3243383 1665414425621588982796459 := by
  unfold tailWord_3243383
  simp only [CollatzResearch.WordTrace]
  refine ⟨118295896408784791561230803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78863930939189861040820535 118295896408784791561230803)
  ·
    refine ⟨177443844613177187341846205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118295896408784791561230803 177443844613177187341846205)
    ·
      refine ⟨66541441729941445253192327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177443844613177187341846205 66541441729941445253192327)
      ·
        refine ⟨99812162594912167879788491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66541441729941445253192327 99812162594912167879788491)
        ·
          refine ⟨149718243892368251819682737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99812162594912167879788491 149718243892368251819682737)
          ·
            refine ⟨112288682919276188864762053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149718243892368251819682737 112288682919276188864762053)
            ·
              refine ⟨21054128047364285412142885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112288682919276188864762053 21054128047364285412142885)
              ·
                refine ⟨3947649008880803514776791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21054128047364285412142885 3947649008880803514776791)
                ·
                  refine ⟨5921473513321205272165187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3947649008880803514776791 5921473513321205272165187)
                  ·
                    refine ⟨8882210269981807908247781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5921473513321205272165187 8882210269981807908247781)
                    ·
                      refine ⟨1665414425621588982796459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8882210269981807908247781 1665414425621588982796459)
                      ·
                        rfl

theorem cell23_3243383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 1, 4].length) (baseStart_3243383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243383 prefixEnd_3243383 := by exact prefixLift 3243383
  have htrace : WordTrace (prefixWord ++ tailWord_3243383) baseStart_3243383 baseEnd_3243383 := by
    simpa [prefixWord, tailWord_3243383, baseEnd_3243383] using wordTrace_append hprefix tailTrace_3243383
  have hstable : (prefixWord ++ tailWord_3243383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243383).length < 2 ^ (prefixWord ++ tailWord_3243383).sum := by decide
  have hdescent : baseEnd_3243383 < baseStart_3243383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243386 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 3, 1, 5]
def baseStart_3243386 : Nat := 118140960795 + 3243386 * 2 ^ 59
def prefixEnd_3243386 : Nat := 4983230072969 + 3 ^ 40 * 3243386 * 2
def baseEnd_3243386 : Nat := 1665415966063552471058945

theorem tailTrace_3243386 : CollatzResearch.WordTrace tailWord_3243386 prefixEnd_3243386 1665415966063552471058945 := by
  unfold tailWord_3243386
  simp only [CollatzResearch.WordTrace]
  refine ⟨29574001456943480768397503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78864003885182615382393341 29574001456943480768397503)
  ·
    refine ⟨44361002185415221152596255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29574001456943480768397503 44361002185415221152596255)
    ·
      refine ⟨66541503278122831728894383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44361002185415221152596255 66541503278122831728894383)
      ·
        refine ⟨99812254917184247593341575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66541503278122831728894383 99812254917184247593341575)
        ·
          refine ⟨149718382375776371390012363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99812254917184247593341575 149718382375776371390012363)
          ·
            refine ⟨224577573563664557085018545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149718382375776371390012363 224577573563664557085018545)
            ·
              refine ⟨168433180172748417813763909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224577573563664557085018545 168433180172748417813763909)
              ·
                refine ⟨31581221282390328340080733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 168433180172748417813763909 31581221282390328340080733)
                ·
                  refine ⟨11842957980896373127530275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31581221282390328340080733 11842957980896373127530275)
                  ·
                    refine ⟨17764436971344559691295413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11842957980896373127530275 17764436971344559691295413)
                    ·
                      refine ⟨1665415966063552471058945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17764436971344559691295413 1665415966063552471058945)
                      ·
                        rfl

theorem cell23_3243386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_3243386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243386 prefixEnd_3243386 := by exact prefixLift 3243386
  have htrace : WordTrace (prefixWord ++ tailWord_3243386) baseStart_3243386 baseEnd_3243386 := by
    simpa [prefixWord, tailWord_3243386, baseEnd_3243386] using wordTrace_append hprefix tailTrace_3243386
  have hstable : (prefixWord ++ tailWord_3243386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243386).length < 2 ^ (prefixWord ++ tailWord_3243386).sum := by decide
  have hdescent : baseEnd_3243386 < baseStart_3243386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243400 : List Nat := [2, 1, 3, 3, 1, 3, 1, 3, 1, 1, 4]
def baseStart_3243400 : Nat := 118140960795 + 3243400 * 2 ^ 59
def prefixEnd_3243400 : Nat := 4983230072969 + 3 ^ 40 * 3243400 * 2
def baseEnd_3243400 : Nat := 1665423154792715416283881

theorem tailTrace_3243400 : CollatzResearch.WordTrace tailWord_3243400 prefixEnd_3243400 1665423154792715416283881 := by
  unfold tailWord_3243400
  simp only [CollatzResearch.WordTrace]
  refine ⟨59148258224861601732299827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78864344299815468976399769 59148258224861601732299827)
  ·
    refine ⟨88722387337292402598449741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59148258224861601732299827 88722387337292402598449741)
    ·
      refine ⟨33270895251484650974418653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88722387337292402598449741 33270895251484650974418653)
      ·
        refine ⟨12476585719306744115406995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33270895251484650974418653 12476585719306744115406995)
        ·
          refine ⟨18714878578960116173110493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12476585719306744115406995 18714878578960116173110493)
          ·
            refine ⟨7018079467110043564916435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18714878578960116173110493 7018079467110043564916435)
            ·
              refine ⟨10527119200665065347374653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7018079467110043564916435 10527119200665065347374653)
              ·
                refine ⟨3947669700249399505265495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10527119200665065347374653 3947669700249399505265495)
                ·
                  refine ⟨5921504550374099257898243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3947669700249399505265495 5921504550374099257898243)
                  ·
                    refine ⟨8882256825561148886847365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5921504550374099257898243 8882256825561148886847365)
                    ·
                      refine ⟨1665423154792715416283881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8882256825561148886847365 1665423154792715416283881)
                      ·
                        rfl

theorem cell23_3243400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_3243400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243400 prefixEnd_3243400 := by exact prefixLift 3243400
  have htrace : WordTrace (prefixWord ++ tailWord_3243400) baseStart_3243400 baseEnd_3243400 := by
    simpa [prefixWord, tailWord_3243400, baseEnd_3243400] using wordTrace_append hprefix tailTrace_3243400
  have hstable : (prefixWord ++ tailWord_3243400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243400).length < 2 ^ (prefixWord ++ tailWord_3243400).sum := by decide
  have hdescent : baseEnd_3243400 < baseStart_3243400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243417 : List Nat := [1, 2, 1, 2, 1, 6, 2, 1, 3, 2, 2]
def baseStart_3243417 : Nat := 118140960795 + 3243417 * 2 ^ 59
def prefixEnd_3243417 : Nat := 4983230072969 + 3 ^ 40 * 3243417 * 2
def baseEnd_3243417 : Nat := 1665431883963841849771303

theorem tailTrace_3243417 : CollatzResearch.WordTrace tailWord_3243417 prefixEnd_3243417 1665431883963841849771303 := by
  unfold tailWord_3243417
  simp only [CollatzResearch.WordTrace]
  refine ⟨118297136490661615367968505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78864757660441076911979003 118297136490661615367968505)
  ·
    refine ⟨88722852367996211525976379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118297136490661615367968505 88722852367996211525976379)
    ·
      refine ⟨133084278551994317288964569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88722852367996211525976379 133084278551994317288964569)
      ·
        refine ⟨99813208913995737966723427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133084278551994317288964569 99813208913995737966723427)
        ·
          refine ⟨149719813370993606950085141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99813208913995737966723427 149719813370993606950085141)
          ·
            refine ⟨7018116251765325325785241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 149719813370993606950085141 7018116251765325325785241)
            ·
              refine ⟨5263587188823993994338931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7018116251765325325785241 5263587188823993994338931)
              ·
                refine ⟨7895380783235990991508397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5263587188823993994338931 7895380783235990991508397)
                ·
                  refine ⟨2960767793713496621815649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7895380783235990991508397 2960767793713496621815649)
                  ·
                    refine ⟨2220575845285122466361737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2960767793713496621815649 2220575845285122466361737)
                    ·
                      refine ⟨1665431883963841849771303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2220575845285122466361737 1665431883963841849771303)
                      ·
                        rfl

theorem cell23_3243417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 3, 2, 2].length) (baseStart_3243417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243417 prefixEnd_3243417 := by exact prefixLift 3243417
  have htrace : WordTrace (prefixWord ++ tailWord_3243417) baseStart_3243417 baseEnd_3243417 := by
    simpa [prefixWord, tailWord_3243417, baseEnd_3243417] using wordTrace_append hprefix tailTrace_3243417
  have hstable : (prefixWord ++ tailWord_3243417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243417).length < 2 ^ (prefixWord ++ tailWord_3243417).sum := by decide
  have hdescent : baseEnd_3243417 < baseStart_3243417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243436 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 2, 7]
def baseStart_3243436 : Nat := 118140960795 + 3243436 * 2 ^ 59
def prefixEnd_3243436 : Nat := 4983230072969 + 3 ^ 40 * 3243436 * 2
def baseEnd_3243436 : Nat := 555147213365425758477905

theorem tailTrace_3243436 : CollatzResearch.WordTrace tailWord_3243436 prefixEnd_3243436 555147213365425758477905 := by
  unfold tailWord_3243436
  simp only [CollatzResearch.WordTrace]
  refine ⟨59148914738796390806455081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78865219651728521075273441 59148914738796390806455081)
  ·
    refine ⟨44361686054097293104841311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59148914738796390806455081 44361686054097293104841311)
    ·
      refine ⟨66542529081145939657261967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44361686054097293104841311 66542529081145939657261967)
      ·
        refine ⟨99813793621718909485892951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66542529081145939657261967 99813793621718909485892951)
        ·
          refine ⟨149720690432578364228839427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99813793621718909485892951 149720690432578364228839427)
          ·
            refine ⟨224581035648867546343259141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149720690432578364228839427 224581035648867546343259141)
            ·
              refine ⟨42108944184162664939361089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 224581035648867546343259141 42108944184162664939361089)
              ·
                refine ⟨31581708138121998704520817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42108944184162664939361089 31581708138121998704520817)
                ·
                  refine ⟨23686281103591499028390613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31581708138121998704520817 23686281103591499028390613)
                  ·
                    refine ⟨555147213365425758477905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23686281103591499028390613 555147213365425758477905)
                    ·
                      rfl

theorem cell23_3243436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 7].length) (baseStart_3243436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243436 prefixEnd_3243436 := by exact prefixLift 3243436
  have htrace : WordTrace (prefixWord ++ tailWord_3243436) baseStart_3243436 baseEnd_3243436 := by
    simpa [prefixWord, tailWord_3243436, baseEnd_3243436] using wordTrace_append hprefix tailTrace_3243436
  have hstable : (prefixWord ++ tailWord_3243436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243436).length < 2 ^ (prefixWord ++ tailWord_3243436).sum := by decide
  have hdescent : baseEnd_3243436 < baseStart_3243436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243437 : List Nat := [1, 5, 2, 2, 1, 1, 1, 4, 1, 2, 3]
def baseStart_3243437 : Nat := 118140960795 + 3243437 * 2 ^ 59
def prefixEnd_3243437 : Nat := 4983230072969 + 3 ^ 40 * 3243437 * 2
def baseEnd_3243437 : Nat := 1665442153576931771521211

theorem tailTrace_3243437 : CollatzResearch.WordTrace tailWord_3243437 prefixEnd_3243437 1665442153576931771521211 := by
  unfold tailWord_3243437
  simp only [CollatzResearch.WordTrace]
  refine ⟨118297865950589158783696565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78865243967059439189131043 118297865950589158783696565)
  ·
    refine ⟨11090424932867733635971553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118297865950589158783696565 11090424932867733635971553)
    ·
      refine ⟨8317818699650800226978665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11090424932867733635971553 8317818699650800226978665)
      ·
        refine ⟨6238364024738100170233999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8317818699650800226978665 6238364024738100170233999)
        ·
          refine ⟨9357546037107150255350999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6238364024738100170233999 9357546037107150255350999)
          ·
            refine ⟨14036319055660725383026499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9357546037107150255350999 14036319055660725383026499)
            ·
              refine ⟨21054478583491088074539749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14036319055660725383026499 21054478583491088074539749)
              ·
                refine ⟨3947714734404579013976203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21054478583491088074539749 3947714734404579013976203)
                ·
                  refine ⟨5921572101606868520964305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3947714734404579013976203 5921572101606868520964305)
                  ·
                    refine ⟨4441179076205151390723229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5921572101606868520964305 4441179076205151390723229)
                    ·
                      refine ⟨1665442153576931771521211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4441179076205151390723229 1665442153576931771521211)
                      ·
                        rfl

theorem cell23_3243437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_3243437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243437 prefixEnd_3243437 := by exact prefixLift 3243437
  have htrace : WordTrace (prefixWord ++ tailWord_3243437) baseStart_3243437 baseEnd_3243437 := by
    simpa [prefixWord, tailWord_3243437, baseEnd_3243437] using wordTrace_append hprefix tailTrace_3243437
  have hstable : (prefixWord ++ tailWord_3243437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243437).length < 2 ^ (prefixWord ++ tailWord_3243437).sum := by decide
  have hdescent : baseEnd_3243437 < baseStart_3243437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243443 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 2, 7, 2]
def baseStart_3243443 : Nat := 118140960795 + 3243443 * 2 ^ 59
def prefixEnd_3243443 : Nat := 4983230072969 + 3 ^ 40 * 3243443 * 2
def baseEnd_3243443 : Nat := 1665445234460858748046183

theorem tailTrace_3243443 : CollatzResearch.WordTrace tailWord_3243443 prefixEnd_3243443 1665445234460858748046183 := by
  unfold tailWord_3243443
  simp only [CollatzResearch.WordTrace]
  refine ⟨118298084788567421808414983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78865389859044947872276655 118298084788567421808414983)
  ·
    refine ⟨177447127182851132712622475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118298084788567421808414983 177447127182851132712622475)
    ·
      refine ⟨266170690774276699068933713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177447127182851132712622475 266170690774276699068933713)
      ·
        refine ⟨199628018080707524301700285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266170690774276699068933713 199628018080707524301700285)
        ·
          refine ⟨74860506780265321613137607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199628018080707524301700285 74860506780265321613137607)
          ·
            refine ⟨112290760170397982419706411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74860506780265321613137607 112290760170397982419706411)
            ·
              refine ⟨168436140255596973629559617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112290760170397982419706411 168436140255596973629559617)
              ·
                refine ⟨126327105191697730222169713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168436140255596973629559617 126327105191697730222169713)
                ·
                  refine ⟨94745328893773297666627285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126327105191697730222169713 94745328893773297666627285)
                  ·
                    refine ⟨2220593645947811664061577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 94745328893773297666627285 2220593645947811664061577)
                    ·
                      refine ⟨1665445234460858748046183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2220593645947811664061577 1665445234460858748046183)
                      ·
                        rfl

theorem cell23_3243443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 7, 2].length) (baseStart_3243443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243443 prefixEnd_3243443 := by exact prefixLift 3243443
  have htrace : WordTrace (prefixWord ++ tailWord_3243443) baseStart_3243443 baseEnd_3243443 := by
    simpa [prefixWord, tailWord_3243443, baseEnd_3243443] using wordTrace_append hprefix tailTrace_3243443
  have hstable : (prefixWord ++ tailWord_3243443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243443).length < 2 ^ (prefixWord ++ tailWord_3243443).sum := by decide
  have hdescent : baseEnd_3243443 < baseStart_3243443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243510 : List Nat := [5, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5]
def baseStart_3243510 : Nat := 118140960795 + 3243510 * 2 ^ 59
def prefixEnd_3243510 : Nat := 4983230072969 + 3 ^ 40 * 3243510 * 2
def baseEnd_3243510 : Nat := 1665479637664709985908375

theorem tailTrace_3243510 : CollatzResearch.WordTrace tailWord_3243510 prefixEnd_3243510 1665479637664709985908375 := by
  unfold tailWord_3243510
  simp only [CollatzResearch.WordTrace]
  refine ⟨7393783029957793265693999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78867018986216461500735989 7393783029957793265693999)
  ·
    refine ⟨11090674544936689898540999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7393783029957793265693999 11090674544936689898540999)
    ·
      refine ⟨16636011817405034847811499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11090674544936689898540999 16636011817405034847811499)
      ·
        refine ⟨24954017726107552271717249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16636011817405034847811499 24954017726107552271717249)
        ·
          refine ⟨18715513294580664203787937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24954017726107552271717249 18715513294580664203787937)
          ·
            refine ⟨14036634970935498152840953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18715513294580664203787937 14036634970935498152840953)
            ·
              refine ⟨10527476228201623614630715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14036634970935498152840953 10527476228201623614630715)
              ·
                refine ⟨15791214342302435421946073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10527476228201623614630715 15791214342302435421946073)
                ·
                  refine ⟨11843410756726826566459555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15791214342302435421946073 11843410756726826566459555)
                  ·
                    refine ⟨17765116135090239849689333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11843410756726826566459555 17765116135090239849689333)
                    ·
                      refine ⟨1665479637664709985908375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17765116135090239849689333 1665479637664709985908375)
                      ·
                        rfl

theorem cell23_3243510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_3243510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243510 prefixEnd_3243510 := by exact prefixLift 3243510
  have htrace : WordTrace (prefixWord ++ tailWord_3243510) baseStart_3243510 baseEnd_3243510 := by
    simpa [prefixWord, tailWord_3243510, baseEnd_3243510] using wordTrace_append hprefix tailTrace_3243510
  have hstable : (prefixWord ++ tailWord_3243510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243510).length < 2 ^ (prefixWord ++ tailWord_3243510).sum := by decide
  have hdescent : baseEnd_3243510 < baseStart_3243510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243680 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 3, 6]
def baseStart_3243680 : Nat := 118140960795 + 3243680 * 2 ^ 59
def prefixEnd_3243680 : Nat := 4983230072969 + 3 ^ 40 * 3243680 * 2
def baseEnd_3243680 : Nat := 555188976458658106927531

theorem tailTrace_3243680 : CollatzResearch.WordTrace tailWord_3243680 prefixEnd_3243680 555188976458658106927531 := by
  unfold tailWord_3243680
  simp only [CollatzResearch.WordTrace]
  refine ⟨59153364444354405642396247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78871152592472540856528329 59153364444354405642396247)
  ·
    refine ⟨88730046666531608463594371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59153364444354405642396247 88730046666531608463594371)
    ·
      refine ⟨133095069999797412695391557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88730046666531608463594371 133095069999797412695391557)
      ·
        refine ⟨24955325624962014880385917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133095069999797412695391557 24955325624962014880385917)
        ·
          refine ⟨9358247109360755580144719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24955325624962014880385917 9358247109360755580144719)
          ·
            refine ⟨14037370664041133370217079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9358247109360755580144719 14037370664041133370217079)
            ·
              refine ⟨21056055996061700055325619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14037370664041133370217079 21056055996061700055325619)
              ·
                refine ⟨31584083994092550082988429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21056055996061700055325619 31584083994092550082988429)
                ·
                  refine ⟨11844031497784706281120661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31584083994092550082988429 11844031497784706281120661)
                  ·
                    refine ⟨555188976458658106927531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11844031497784706281120661 555188976458658106927531)
                    ·
                      rfl

theorem cell23_3243680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 3, 6].length) (baseStart_3243680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243680 prefixEnd_3243680 := by exact prefixLift 3243680
  have htrace : WordTrace (prefixWord ++ tailWord_3243680) baseStart_3243680 baseEnd_3243680 := by
    simpa [prefixWord, tailWord_3243680, baseEnd_3243680] using wordTrace_append hprefix tailTrace_3243680
  have hstable : (prefixWord ++ tailWord_3243680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243680).length < 2 ^ (prefixWord ++ tailWord_3243680).sum := by decide
  have hdescent : baseEnd_3243680 < baseStart_3243680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243684 : List Nat := [2, 3, 1, 2, 2, 3, 3, 1, 1, 5]
def baseStart_3243684 : Nat := 118140960795 + 3243684 * 2 ^ 59
def prefixEnd_3243684 : Nat := 4983230072969 + 3 ^ 40 * 3243684 * 2
def baseEnd_3243684 : Nat := 555189661099530768377525

theorem tailTrace_3243684 : CollatzResearch.WordTrace tailWord_3243684 prefixEnd_3243684 555189661099530768377525 := by
  unfold tailWord_3243684
  simp only [CollatzResearch.WordTrace]
  refine ⟨59153437390347159983969053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78871249853796213311958737 59153437390347159983969053)
  ·
    refine ⟨22182539021380184993988395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59153437390347159983969053 22182539021380184993988395)
    ·
      refine ⟨33273808532070277490982593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22182539021380184993988395 33273808532070277490982593)
      ·
        refine ⟨24955356399052708118236945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33273808532070277490982593 24955356399052708118236945)
        ·
          refine ⟨18716517299289531088677709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24955356399052708118236945 18716517299289531088677709)
          ·
            refine ⟨7018693987233574158254141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18716517299289531088677709 7018693987233574158254141)
            ·
              refine ⟨2632010245212590309345303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7018693987233574158254141 2632010245212590309345303)
              ·
                refine ⟨3948015367818885464017955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2632010245212590309345303 3948015367818885464017955)
                ·
                  refine ⟨5922023051728328196026933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3948015367818885464017955 5922023051728328196026933)
                  ·
                    refine ⟨555189661099530768377525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5922023051728328196026933 555189661099530768377525)
                    ·
                      rfl

theorem cell23_3243684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_3243684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243684 prefixEnd_3243684 := by exact prefixLift 3243684
  have htrace : WordTrace (prefixWord ++ tailWord_3243684) baseStart_3243684 baseEnd_3243684 := by
    simpa [prefixWord, tailWord_3243684, baseEnd_3243684] using wordTrace_append hprefix tailTrace_3243684
  have hstable : (prefixWord ++ tailWord_3243684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243684).length < 2 ^ (prefixWord ++ tailWord_3243684).sum := by decide
  have hdescent : baseEnd_3243684 < baseStart_3243684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243737 : List Nat := [1, 2, 1, 2, 3, 3, 2, 2, 1, 3, 3]
def baseStart_3243737 : Nat := 118140960795 + 3243737 * 2 ^ 59
def prefixEnd_3243737 : Nat := 4983230072969 + 3 ^ 40 * 3243737 * 2
def baseEnd_3243737 : Nat := 1665596197773280597769831

theorem tailTrace_3243737 : CollatzResearch.WordTrace tailWord_3243737 prefixEnd_3243737 1665596197773280597769831 := by
  unfold tailWord_3243737
  simp only [CollatzResearch.WordTrace]
  refine ⟨118308807849502310019617465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78872538566334873346411643 118308807849502310019617465)
  ·
    refine ⟨88731605887126732514713099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118308807849502310019617465 88731605887126732514713099)
    ·
      refine ⟨133097408830690098772069649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88731605887126732514713099 133097408830690098772069649)
      ·
        refine ⟨99823056623017574079052237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133097408830690098772069649 99823056623017574079052237)
        ·
          refine ⟨37433646233631590279644589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99823056623017574079052237 37433646233631590279644589)
          ·
            refine ⟨14037617337611846354866721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37433646233631590279644589 14037617337611846354866721)
            ·
              refine ⟨10528213003208884766150041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14037617337611846354866721 10528213003208884766150041)
              ·
                refine ⟨7896159752406663574612531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10528213003208884766150041 7896159752406663574612531)
                ·
                  refine ⟨11844239628609995361918797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7896159752406663574612531 11844239628609995361918797)
                  ·
                    refine ⟨4441589860728748260719549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11844239628609995361918797 4441589860728748260719549)
                    ·
                      refine ⟨1665596197773280597769831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4441589860728748260719549 1665596197773280597769831)
                      ·
                        rfl

theorem cell23_3243737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 3, 3].length) (baseStart_3243737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243737 prefixEnd_3243737 := by exact prefixLift 3243737
  have htrace : WordTrace (prefixWord ++ tailWord_3243737) baseStart_3243737 baseEnd_3243737 := by
    simpa [prefixWord, tailWord_3243737, baseEnd_3243737] using wordTrace_append hprefix tailTrace_3243737
  have hstable : (prefixWord ++ tailWord_3243737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243737).length < 2 ^ (prefixWord ++ tailWord_3243737).sum := by decide
  have hdescent : baseEnd_3243737 < baseStart_3243737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243738 : List Nat := [3, 1, 1, 2, 2, 4, 2, 3, 1, 2, 2]
def baseStart_3243738 : Nat := 118140960795 + 3243738 * 2 ^ 59
def prefixEnd_3243738 : Nat := 4983230072969 + 3 ^ 40 * 3243738 * 2
def baseEnd_3243738 : Nat := 1665596711253935093857327

theorem tailTrace_3243738 : CollatzResearch.WordTrace tailWord_3243738 prefixEnd_3243738 1665596711253935093857327 := by
  unfold tailWord_3243738
  simp only [CollatzResearch.WordTrace]
  refine ⟨29577211080624671797600967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78872562881665791460269245 29577211080624671797600967)
  ·
    refine ⟨44365816620937007696401451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29577211080624671797600967 44365816620937007696401451)
    ·
      refine ⟨66548724931405511544602177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44365816620937007696401451 66548724931405511544602177)
      ·
        refine ⟨49911543698554133658451633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66548724931405511544602177 49911543698554133658451633)
        ·
          refine ⟨37433657773915600243838725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49911543698554133658451633 37433657773915600243838725)
          ·
            refine ⟨7018810832609175045719761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37433657773915600243838725 7018810832609175045719761)
            ·
              refine ⟨5264108124456881284289821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7018810832609175045719761 5264108124456881284289821)
              ·
                refine ⟨1974040546671330481608683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5264108124456881284289821 1974040546671330481608683)
                ·
                  refine ⟨2961060820006995722413025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1974040546671330481608683 2961060820006995722413025)
                  ·
                    refine ⟨2220795615005246791809769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2961060820006995722413025 2220795615005246791809769)
                    ·
                      refine ⟨1665596711253935093857327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2220795615005246791809769 1665596711253935093857327)
                      ·
                        rfl

theorem cell23_3243738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 3, 1, 2, 2].length) (baseStart_3243738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243738 prefixEnd_3243738 := by exact prefixLift 3243738
  have htrace : WordTrace (prefixWord ++ tailWord_3243738) baseStart_3243738 baseEnd_3243738 := by
    simpa [prefixWord, tailWord_3243738, baseEnd_3243738] using wordTrace_append hprefix tailTrace_3243738
  have hstable : (prefixWord ++ tailWord_3243738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243738).length < 2 ^ (prefixWord ++ tailWord_3243738).sum := by decide
  have hdescent : baseEnd_3243738 < baseStart_3243738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243760 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 4]
def baseStart_3243760 : Nat := 118140960795 + 3243760 * 2 ^ 59
def prefixEnd_3243760 : Nat := 4983230072969 + 3 ^ 40 * 3243760 * 2
def baseEnd_3243760 : Nat := 1665608007828334007782225

theorem tailTrace_3243760 : CollatzResearch.WordTrace tailWord_3243760 prefixEnd_3243760 1665608007828334007782225 := by
  unfold tailWord_3243760
  simp only [CollatzResearch.WordTrace]
  refine ⟨59154823364209492473852367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78873097818945989965136489 59154823364209492473852367)
  ·
    refine ⟨88732235046314238710778551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59154823364209492473852367 88732235046314238710778551)
    ·
      refine ⟨133098352569471358066167827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88732235046314238710778551 133098352569471358066167827)
      ·
        refine ⟨199647528854207037099251741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133098352569471358066167827 199647528854207037099251741)
        ·
          refine ⟨74867823320327638912219403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199647528854207037099251741 74867823320327638912219403)
          ·
            refine ⟨112301734980491458368329105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74867823320327638912219403 112301734980491458368329105)
            ·
              refine ⟨84226301235368593776246829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112301734980491458368329105 84226301235368593776246829)
              ·
                refine ⟨31584862963263222666092561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84226301235368593776246829 31584862963263222666092561)
                ·
                  refine ⟨23688647222447416999569421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31584862963263222666092561 23688647222447416999569421)
                  ·
                    refine ⟨8883242708417781374838533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23688647222447416999569421 8883242708417781374838533)
                    ·
                      refine ⟨1665608007828334007782225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8883242708417781374838533 1665608007828334007782225)
                      ·
                        rfl

theorem cell23_3243760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 4].length) (baseStart_3243760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243760 prefixEnd_3243760 := by exact prefixLift 3243760
  have htrace : WordTrace (prefixWord ++ tailWord_3243760) baseStart_3243760 baseEnd_3243760 := by
    simpa [prefixWord, tailWord_3243760, baseEnd_3243760] using wordTrace_append hprefix tailTrace_3243760
  have hstable : (prefixWord ++ tailWord_3243760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243760).length < 2 ^ (prefixWord ++ tailWord_3243760).sum := by decide
  have hdescent : baseEnd_3243760 < baseStart_3243760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243797 : List Nat := [1, 3, 2, 1, 2, 4, 1, 1, 2, 1, 5]
def baseStart_3243797 : Nat := 118140960795 + 3243797 * 2 ^ 59
def prefixEnd_3243797 : Nat := 4983230072969 + 3 ^ 40 * 3243797 * 2
def baseEnd_3243797 : Nat := 1665627006612550363019555

theorem tailTrace_3243797 : CollatzResearch.WordTrace tailWord_3243797 prefixEnd_3243797 1665627006612550363019555 := by
  unfold tailWord_3243797
  simp only [CollatzResearch.WordTrace]
  refine ⟨118310996229284940266801645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78873997486189960177867763 118310996229284940266801645)
  ·
    refine ⟨44366623585981852600050617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118310996229284940266801645 44366623585981852600050617)
    ·
      refine ⟨33274967689486389450037963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44366623585981852600050617 33274967689486389450037963)
      ·
        refine ⟨49912451534229584175056945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33274967689486389450037963 49912451534229584175056945)
        ·
          refine ⟨37434338650672188131292709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49912451534229584175056945 37434338650672188131292709)
          ·
            refine ⟨7018938497001035274617383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37434338650672188131292709 7018938497001035274617383)
            ·
              refine ⟨10528407745501552911926075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7018938497001035274617383 10528407745501552911926075)
              ·
                refine ⟨15792611618252329367889113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10528407745501552911926075 15792611618252329367889113)
                ·
                  refine ⟨11844458713689247025916835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15792611618252329367889113 11844458713689247025916835)
                  ·
                    refine ⟨17766688070533870538875253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11844458713689247025916835 17766688070533870538875253)
                    ·
                      refine ⟨1665627006612550363019555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17766688070533870538875253 1665627006612550363019555)
                      ·
                        rfl

theorem cell23_3243797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_3243797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243797 prefixEnd_3243797 := by exact prefixLift 3243797
  have htrace : WordTrace (prefixWord ++ tailWord_3243797) baseStart_3243797 baseEnd_3243797 := by
    simpa [prefixWord, tailWord_3243797, baseEnd_3243797] using wordTrace_append hprefix tailTrace_3243797
  have hstable : (prefixWord ++ tailWord_3243797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243797).length < 2 ^ (prefixWord ++ tailWord_3243797).sum := by decide
  have hdescent : baseEnd_3243797 < baseStart_3243797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243800 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 9]
def baseStart_3243800 : Nat := 118140960795 + 3243800 * 2 ^ 59
def prefixEnd_3243800 : Nat := 4983230072969 + 3 ^ 40 * 3243800 * 2
def baseEnd_3243800 : Nat := 185069838561612650142449

theorem tailTrace_3243800 : CollatzResearch.WordTrace tailWord_3243800 prefixEnd_3243800 185069838561612650142449 := by
  unfold tailWord_3243800
  simp only [CollatzResearch.WordTrace]
  refine ⟨59155552824137035889580427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78874070432182714519440569 59155552824137035889580427)
  ·
    refine ⟨88733329236205553834370641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59155552824137035889580427 88733329236205553834370641)
    ·
      refine ⟨66549996927154165375777981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88733329236205553834370641 66549996927154165375777981)
      ·
        refine ⟨24956248847682812015916743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66549996927154165375777981 24956248847682812015916743)
        ·
          refine ⟨37434373271524218023875115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24956248847682812015916743 37434373271524218023875115)
          ·
            refine ⟨56151559907286327035812673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37434373271524218023875115 56151559907286327035812673)
            ·
              refine ⟨42113669930464745276859505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56151559907286327035812673 42113669930464745276859505)
              ·
                refine ⟨31585252447848558957644629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42113669930464745276859505 31585252447848558957644629)
                ·
                  refine ⟨185069838561612650142449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31585252447848558957644629 185069838561612650142449)
                  ·
                    rfl

theorem cell23_3243800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 9].length) (baseStart_3243800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243800 prefixEnd_3243800 := by exact prefixLift 3243800
  have htrace : WordTrace (prefixWord ++ tailWord_3243800) baseStart_3243800 baseEnd_3243800 := by
    simpa [prefixWord, tailWord_3243800, baseEnd_3243800] using wordTrace_append hprefix tailTrace_3243800
  have hstable : (prefixWord ++ tailWord_3243800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243800).length < 2 ^ (prefixWord ++ tailWord_3243800).sum := by decide
  have hdescent : baseEnd_3243800 < baseStart_3243800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243822 : List Nat := [4, 1, 3, 2, 3, 1, 2, 1, 2, 1, 3]
def baseStart_3243822 : Nat := 118140960795 + 3243822 * 2 ^ 59
def prefixEnd_3243822 : Nat := 4983230072969 + 3 ^ 40 * 3243822 * 2
def baseEnd_3243822 : Nat := 1665639843628912765206941

theorem tailTrace_3243822 : CollatzResearch.WordTrace tailWord_3243822 prefixEnd_3243822 1665639843628912765206941 := by
  unfold tailWord_3243822
  simp only [CollatzResearch.WordTrace]
  refine ⟨14788988506774296192057715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78874605369462913024307813 14788988506774296192057715)
  ·
    refine ⟨22183482760161444288086573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14788988506774296192057715 22183482760161444288086573)
    ·
      refine ⟨8318806035060541608032465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22183482760161444288086573 8318806035060541608032465)
      ·
        refine ⟨6239104526295406206024349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8318806035060541608032465 6239104526295406206024349)
        ·
          refine ⟨2339664197360777327259131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6239104526295406206024349 2339664197360777327259131)
          ·
            refine ⟨3509496296041165990888697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2339664197360777327259131 3509496296041165990888697)
            ·
              refine ⟨2632122222030874493166523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3509496296041165990888697 2632122222030874493166523)
              ·
                refine ⟨3948183333046311739749785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2632122222030874493166523 3948183333046311739749785)
                ·
                  refine ⟨2961137499784733804812339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3948183333046311739749785 2961137499784733804812339)
                  ·
                    refine ⟨4441706249677100707218509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2961137499784733804812339 4441706249677100707218509)
                    ·
                      refine ⟨1665639843628912765206941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4441706249677100707218509 1665639843628912765206941)
                      ·
                        rfl

theorem cell23_3243822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_3243822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243822 prefixEnd_3243822 := by exact prefixLift 3243822
  have htrace : WordTrace (prefixWord ++ tailWord_3243822) baseStart_3243822 baseEnd_3243822 := by
    simpa [prefixWord, tailWord_3243822, baseEnd_3243822] using wordTrace_append hprefix tailTrace_3243822
  have hstable : (prefixWord ++ tailWord_3243822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243822).length < 2 ^ (prefixWord ++ tailWord_3243822).sum := by decide
  have hdescent : baseEnd_3243822 < baseStart_3243822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243847 : List Nat := [1, 1, 4, 1, 2, 1, 3, 3, 2, 5]
def baseStart_3243847 : Nat := 118140960795 + 3243847 * 2 ^ 59
def prefixEnd_3243847 : Nat := 4983230072969 + 3 ^ 40 * 3243847 * 2
def baseEnd_3243847 : Nat := 555217560215091722464775

theorem tailTrace_3243847 : CollatzResearch.WordTrace tailWord_3243847 prefixEnd_3243847 555217560215091722464775 := by
  unfold tailWord_3243847
  simp only [CollatzResearch.WordTrace]
  refine ⟨118312819879103798806121795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78875213252735865870747863 118312819879103798806121795)
  ·
    refine ⟨177469229818655698209182693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118312819879103798806121795 177469229818655698209182693)
    ·
      refine ⟨33275480590997943414221755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177469229818655698209182693 33275480590997943414221755)
      ·
        refine ⟨49913220886496915121332633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33275480590997943414221755 49913220886496915121332633)
        ·
          refine ⟨37434915664872686340999475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49913220886496915121332633 37434915664872686340999475)
          ·
            refine ⟨56152373497309029511499213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37434915664872686340999475 56152373497309029511499213)
            ·
              refine ⟨21057140061490886066812205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56152373497309029511499213 21057140061490886066812205)
              ·
                refine ⟨7896427523059082275054577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21057140061490886066812205 7896427523059082275054577)
                ·
                  refine ⟨5922320642294311706290933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7896427523059082275054577 5922320642294311706290933)
                  ·
                    refine ⟨555217560215091722464775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5922320642294311706290933 555217560215091722464775)
                    ·
                      rfl

theorem cell23_3243847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_3243847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243847 prefixEnd_3243847 := by exact prefixLift 3243847
  have htrace : WordTrace (prefixWord ++ tailWord_3243847) baseStart_3243847 baseEnd_3243847 := by
    simpa [prefixWord, tailWord_3243847, baseEnd_3243847] using wordTrace_append hprefix tailTrace_3243847
  have hstable : (prefixWord ++ tailWord_3243847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243847).length < 2 ^ (prefixWord ++ tailWord_3243847).sum := by decide
  have hdescent : baseEnd_3243847 < baseStart_3243847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243857 : List Nat := [1, 2, 2, 1, 5, 1, 1, 2, 1, 2, 5]
def baseStart_3243857 : Nat := 118140960795 + 3243857 * 2 ^ 59
def prefixEnd_3243857 : Nat := 4983230072969 + 3 ^ 40 * 3243857 * 2
def baseEnd_3243857 : Nat := 1665657815451820128269279

theorem tailTrace_3243857 : CollatzResearch.WordTrace tailWord_3243857 prefixEnd_3243857 1665657815451820128269279 := by
  unfold tailWord_3243857
  simp only [CollatzResearch.WordTrace]
  refine ⟨118313184609067570513985825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78875456406045047009323883 118313184609067570513985825)
  ·
    refine ⟨88734888456800677885489369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118313184609067570513985825 88734888456800677885489369)
    ·
      refine ⟨66551166342600508414117027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88734888456800677885489369 66551166342600508414117027)
      ·
        refine ⟨99826749513900762621175541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66551166342600508414117027 99826749513900762621175541)
        ·
          refine ⟨9358757766928196495735207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99826749513900762621175541 9358757766928196495735207)
          ·
            refine ⟨14038136650392294743602811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9358757766928196495735207 14038136650392294743602811)
            ·
              refine ⟨21057204975588442115404217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14038136650392294743602811 21057204975588442115404217)
              ·
                refine ⟨15792903731691331586553163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21057204975588442115404217 15792903731691331586553163)
                ·
                  refine ⟨23689355597536997379829745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15792903731691331586553163 23689355597536997379829745)
                  ·
                    refine ⟨17767016698152748034872309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23689355597536997379829745 17767016698152748034872309)
                    ·
                      refine ⟨1665657815451820128269279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17767016698152748034872309 1665657815451820128269279)
                      ·
                        rfl

theorem cell23_3243857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_3243857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243857 prefixEnd_3243857 := by exact prefixLift 3243857
  have htrace : WordTrace (prefixWord ++ tailWord_3243857) baseStart_3243857 baseEnd_3243857 := by
    simpa [prefixWord, tailWord_3243857, baseEnd_3243857] using wordTrace_append hprefix tailTrace_3243857
  have hstable : (prefixWord ++ tailWord_3243857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243857).length < 2 ^ (prefixWord ++ tailWord_3243857).sum := by decide
  have hdescent : baseEnd_3243857 < baseStart_3243857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243874 : List Nat := [3, 3, 2, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_3243874 : Nat := 118140960795 + 3243874 * 2 ^ 59
def prefixEnd_3243874 : Nat := 4983230072969 + 3 ^ 40 * 3243874 * 2
def baseEnd_3243874 : Nat := 1665666544622946561756701

theorem tailTrace_3243874 : CollatzResearch.WordTrace tailWord_3243874 prefixEnd_3243874 1665666544622946561756701 := by
  unfold tailWord_3243874
  simp only [CollatzResearch.WordTrace]
  refine ⟨29578451162501495604338669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78875869766670654944903117 29578451162501495604338669)
  ·
    refine ⟨11091919185938060851627001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29578451162501495604338669 11091919185938060851627001)
    ·
      refine ⟨8318939389453545638720251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11091919185938060851627001 8318939389453545638720251)
      ·
        refine ⟨12478409084180318458080377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8318939389453545638720251 12478409084180318458080377)
        ·
          refine ⟨9358806813135238843560283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12478409084180318458080377 9358806813135238843560283)
          ·
            refine ⟨14038210219702858265340425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9358806813135238843560283 14038210219702858265340425)
            ·
              refine ⟨10528657664777143699005319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14038210219702858265340425 10528657664777143699005319)
              ·
                refine ⟨15792986497165715548507979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10528657664777143699005319 15792986497165715548507979)
                ·
                  refine ⟨23689479745748573322761969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15792986497165715548507979 23689479745748573322761969)
                  ·
                    refine ⟨17767109809311429992071477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23689479745748573322761969 17767109809311429992071477)
                    ·
                      refine ⟨1665666544622946561756701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17767109809311429992071477 1665666544622946561756701)
                      ·
                        rfl

theorem cell23_3243874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_3243874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243874 prefixEnd_3243874 := by exact prefixLift 3243874
  have htrace : WordTrace (prefixWord ++ tailWord_3243874) baseStart_3243874 baseEnd_3243874 := by
    simpa [prefixWord, tailWord_3243874, baseEnd_3243874] using wordTrace_append hprefix tailTrace_3243874
  have hstable : (prefixWord ++ tailWord_3243874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243874).length < 2 ^ (prefixWord ++ tailWord_3243874).sum := by decide
  have hdescent : baseEnd_3243874 < baseStart_3243874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243884 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 1, 6, 2]
def baseStart_3243884 : Nat := 118140960795 + 3243884 * 2 ^ 59
def prefixEnd_3243884 : Nat := 4983230072969 + 3 ^ 40 * 3243884 * 2
def baseEnd_3243884 : Nat := 1665671679429491522631655

theorem tailTrace_3243884 : CollatzResearch.WordTrace tailWord_3243884 prefixEnd_3243884 1665671679429491522631655 := by
  unfold tailWord_3243884
  simp only [CollatzResearch.WordTrace]
  refine ⟨59157084689984877062609353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78876112919979836083479137 59157084689984877062609353)
  ·
    refine ⟨44367813517488657796957015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59157084689984877062609353 44367813517488657796957015)
    ·
      refine ⟨66551720276232986695435523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44367813517488657796957015 66551720276232986695435523)
      ·
        refine ⟨99827580414349480043153285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66551720276232986695435523 99827580414349480043153285)
        ·
          refine ⟨18717671327690527508091241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99827580414349480043153285 18717671327690527508091241)
          ·
            refine ⟨14038253495767895631068431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18717671327690527508091241 14038253495767895631068431)
            ·
              refine ⟨21057380243651843446602647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14038253495767895631068431 21057380243651843446602647)
              ·
                refine ⟨31586070365477765169903971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21057380243651843446602647 31586070365477765169903971)
                ·
                  refine ⟨47379105548216647754855957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31586070365477765169903971 47379105548216647754855957)
                  ·
                    refine ⟨2220895572572655363508873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 47379105548216647754855957 2220895572572655363508873)
                    ·
                      refine ⟨1665671679429491522631655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2220895572572655363508873 1665671679429491522631655)
                      ·
                        rfl

theorem cell23_3243884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 6, 2].length) (baseStart_3243884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243884 prefixEnd_3243884 := by exact prefixLift 3243884
  have htrace : WordTrace (prefixWord ++ tailWord_3243884) baseStart_3243884 baseEnd_3243884 := by
    simpa [prefixWord, tailWord_3243884, baseEnd_3243884] using wordTrace_append hprefix tailTrace_3243884
  have hstable : (prefixWord ++ tailWord_3243884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243884).length < 2 ^ (prefixWord ++ tailWord_3243884).sum := by decide
  have hdescent : baseEnd_3243884 < baseStart_3243884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243924 : List Nat := [2, 4, 2, 1, 1, 3, 1, 1, 8]
def baseStart_3243924 : Nat := 118140960795 + 3243924 * 2 ^ 59
def prefixEnd_3243924 : Nat := 4983230072969 + 3 ^ 40 * 3243924 * 2
def baseEnd_3243924 : Nat := 185076913183963485125719

theorem tailTrace_3243924 : CollatzResearch.WordTrace tailWord_3243924 prefixEnd_3243924 185076913183963485125719 := by
  unfold tailWord_3243924
  simp only [CollatzResearch.WordTrace]
  refine ⟨59157814149912420478337413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78877085533216560637783217 59157814149912420478337413)
  ·
    refine ⟨11092090153108578839688265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59157814149912420478337413 11092090153108578839688265)
    ·
      refine ⟨8319067614831434129766199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11092090153108578839688265 8319067614831434129766199)
      ·
        refine ⟨12478601422247151194649299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8319067614831434129766199 12478601422247151194649299)
        ·
          refine ⟨18717902133370726791973949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12478601422247151194649299 18717902133370726791973949)
          ·
            refine ⟨7019213300014022546990231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18717902133370726791973949 7019213300014022546990231)
            ·
              refine ⟨10528819950021033820485347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7019213300014022546990231 10528819950021033820485347)
              ·
                refine ⟨15793229925031550730728021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10528819950021033820485347 15793229925031550730728021)
                ·
                  refine ⟨185076913183963485125719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15793229925031550730728021 185076913183963485125719)
                  ·
                    rfl

theorem cell23_3243924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_3243924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243924 prefixEnd_3243924 := by exact prefixLift 3243924
  have htrace : WordTrace (prefixWord ++ tailWord_3243924) baseStart_3243924 baseEnd_3243924 := by
    simpa [prefixWord, tailWord_3243924, baseEnd_3243924] using wordTrace_append hprefix tailTrace_3243924
  have hstable : (prefixWord ++ tailWord_3243924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243924).length < 2 ^ (prefixWord ++ tailWord_3243924).sum := by decide
  have hdescent : baseEnd_3243924 < baseStart_3243924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243927 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 6]
def baseStart_3243927 : Nat := 118140960795 + 3243927 * 2 ^ 59
def prefixEnd_3243927 : Nat := 4983230072969 + 3 ^ 40 * 3243927 * 2
def baseEnd_3243927 : Nat := 1665693759097634854393957

theorem tailTrace_3243927 : CollatzResearch.WordTrace tailWord_3243927 prefixEnd_3243927 1665693759097634854393957 := by
  unfold tailWord_3243927
  simp only [CollatzResearch.WordTrace]
  refine ⟨118315737718813972469034035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78877158479209314979356023 118315737718813972469034035)
  ·
    refine ⟨177473606578220958703551053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118315737718813972469034035 177473606578220958703551053)
    ·
      refine ⟨66552602466832859513831645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177473606578220958703551053 66552602466832859513831645)
      ·
        refine ⟨24957225925062322317686867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66552602466832859513831645 24957225925062322317686867)
        ·
          refine ⟨37435838887593483476530301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24957225925062322317686867 37435838887593483476530301)
          ·
            refine ⟨14038439582847556303698863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37435838887593483476530301 14038439582847556303698863)
            ·
              refine ⟨21057659374271334455548295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14038439582847556303698863 21057659374271334455548295)
              ·
                refine ⟨31586489061407001683322443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21057659374271334455548295 31586489061407001683322443)
                ·
                  refine ⟨47379733592110502524983665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31586489061407001683322443 47379733592110502524983665)
                  ·
                    refine ⟨35534800194082876893737749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47379733592110502524983665 35534800194082876893737749)
                    ·
                      refine ⟨1665693759097634854393957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35534800194082876893737749 1665693759097634854393957)
                      ·
                        rfl

theorem cell23_3243927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_3243927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243927 prefixEnd_3243927 := by exact prefixLift 3243927
  have htrace : WordTrace (prefixWord ++ tailWord_3243927) baseStart_3243927 baseEnd_3243927 := by
    simpa [prefixWord, tailWord_3243927, baseEnd_3243927] using wordTrace_append hprefix tailTrace_3243927
  have hstable : (prefixWord ++ tailWord_3243927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243927).length < 2 ^ (prefixWord ++ tailWord_3243927).sum := by decide
  have hdescent : baseEnd_3243927 < baseStart_3243927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243928 : List Nat := [2, 1, 2, 6, 1, 1, 2, 1, 3, 4]
def baseStart_3243928 : Nat := 118140960795 + 3243928 * 2 ^ 59
def prefixEnd_3243928 : Nat := 4983230072969 + 3 ^ 40 * 3243928 * 2
def baseEnd_3243928 : Nat := 555231424192763116827151

theorem tailTrace_3243928 : CollatzResearch.WordTrace tailWord_3243928 prefixEnd_3243928 555231424192763116827151 := by
  unfold tailWord_3243928
  simp only [CollatzResearch.WordTrace]
  refine ⟨59157887095905174819910219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78877182794540233093213625 59157887095905174819910219)
  ·
    refine ⟨88736830643857762229865329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59157887095905174819910219 88736830643857762229865329)
    ·
      refine ⟨66552622982893321672398997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88736830643857762229865329 66552622982893321672398997)
      ·
        refine ⟨3119654202323124453393703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 66552622982893321672398997 3119654202323124453393703)
        ·
          refine ⟨4679481303484686680090555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3119654202323124453393703 4679481303484686680090555)
          ·
            refine ⟨7019221955227030020135833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4679481303484686680090555 7019221955227030020135833)
            ·
              refine ⟨5264416466420272515101875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7019221955227030020135833 5264416466420272515101875)
              ·
                refine ⟨7896624699630408772652813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5264416466420272515101875 7896624699630408772652813)
                ·
                  refine ⟨2961234262361403289744805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7896624699630408772652813 2961234262361403289744805)
                  ·
                    refine ⟨555231424192763116827151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2961234262361403289744805 555231424192763116827151)
                    ·
                      rfl

theorem cell23_3243928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 3, 4].length) (baseStart_3243928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243928 prefixEnd_3243928 := by exact prefixLift 3243928
  have htrace : WordTrace (prefixWord ++ tailWord_3243928) baseStart_3243928 baseEnd_3243928 := by
    simpa [prefixWord, tailWord_3243928, baseEnd_3243928] using wordTrace_append hprefix tailTrace_3243928
  have hstable : (prefixWord ++ tailWord_3243928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243928).length < 2 ^ (prefixWord ++ tailWord_3243928).sum := by decide
  have hdescent : baseEnd_3243928 < baseStart_3243928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243961 : List Nat := [1, 2, 1, 4, 2, 1, 2, 3, 2, 3, 2]
def baseStart_3243961 : Nat := 118140960795 + 3243961 * 2 ^ 59
def prefixEnd_3243961 : Nat := 4983230072969 + 3 ^ 40 * 3243961 * 2
def baseEnd_3243961 : Nat := 1665711217439887721368801

theorem tailTrace_3243961 : CollatzResearch.WordTrace tailWord_3243961 prefixEnd_3243961 1665711217439887721368801 := by
  unfold tailWord_3243961
  simp only [CollatzResearch.WordTrace]
  refine ⟨118316977800690796275771737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78877985200460530850514491 118316977800690796275771737)
  ·
    refine ⟨88737733350518097206828803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118316977800690796275771737 88737733350518097206828803)
    ·
      refine ⟨133106600025777145810243205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88737733350518097206828803 133106600025777145810243205)
      ·
        refine ⟨24957487504833214839420601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133106600025777145810243205 24957487504833214839420601)
        ·
          refine ⟨18718115628624911129565451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24957487504833214839420601 18718115628624911129565451)
          ·
            refine ⟨28077173442937366694348177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18718115628624911129565451 28077173442937366694348177)
            ·
              refine ⟨21057880082203025020761133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28077173442937366694348177 21057880082203025020761133)
              ·
                refine ⟨7896705030826134382785425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21057880082203025020761133 7896705030826134382785425)
                ·
                  refine ⟨5922528773119600787089069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7896705030826134382785425 5922528773119600787089069)
                  ·
                    refine ⟨2220948289919850295158401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5922528773119600787089069 2220948289919850295158401)
                    ·
                      refine ⟨1665711217439887721368801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2220948289919850295158401 1665711217439887721368801)
                      ·
                        rfl

theorem cell23_3243961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_3243961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243961 prefixEnd_3243961 := by exact prefixLift 3243961
  have htrace : WordTrace (prefixWord ++ tailWord_3243961) baseStart_3243961 baseEnd_3243961 := by
    simpa [prefixWord, tailWord_3243961, baseEnd_3243961] using wordTrace_append hprefix tailTrace_3243961
  have hstable : (prefixWord ++ tailWord_3243961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243961).length < 2 ^ (prefixWord ++ tailWord_3243961).sum := by decide
  have hdescent : baseEnd_3243961 < baseStart_3243961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243967 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 3, 6]
def baseStart_3243967 : Nat := 118140960795 + 3243967 * 2 ^ 59
def prefixEnd_3243967 : Nat := 4983230072969 + 3 ^ 40 * 3243967 * 2
def baseEnd_3243967 : Nat := 555238099441271565964591

theorem tailTrace_3243967 : CollatzResearch.WordTrace tailWord_3243967 prefixEnd_3243967 555238099441271565964591 := by
  unfold tailWord_3243967
  simp only [CollatzResearch.WordTrace]
  refine ⟨118317196638669059300490155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78878131092446039533660103 118317196638669059300490155)
  ·
    refine ⟨177475794958003588950735233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118317196638669059300490155 177475794958003588950735233)
    ·
      refine ⟨133106846218502691713051425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177475794958003588950735233 133106846218502691713051425)
      ·
        refine ⟨99830134663877018784788569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133106846218502691713051425 99830134663877018784788569)
        ·
          refine ⟨74872600997907764088591427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99830134663877018784788569 74872600997907764088591427)
          ·
            refine ⟨112308901496861646132887141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74872600997907764088591427 112308901496861646132887141)
            ·
              refine ⟨21057919030661558649916339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112308901496861646132887141 21057919030661558649916339)
              ·
                refine ⟨31586878545992337974874509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21057919030661558649916339 31586878545992337974874509)
                ·
                  refine ⟨11845079454747126740577941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31586878545992337974874509 11845079454747126740577941)
                  ·
                    refine ⟨555238099441271565964591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11845079454747126740577941 555238099441271565964591)
                    ·
                      rfl

theorem cell23_3243967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 6].length) (baseStart_3243967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243967 prefixEnd_3243967 := by exact prefixLift 3243967
  have htrace : WordTrace (prefixWord ++ tailWord_3243967) baseStart_3243967 baseEnd_3243967 := by
    simpa [prefixWord, tailWord_3243967, baseEnd_3243967] using wordTrace_append hprefix tailTrace_3243967
  have hstable : (prefixWord ++ tailWord_3243967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243967).length < 2 ^ (prefixWord ++ tailWord_3243967).sum := by decide
  have hdescent : baseEnd_3243967 < baseStart_3243967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243977 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 5, 1, 5]
def baseStart_3243977 : Nat := 118140960795 + 3243977 * 2 ^ 59
def prefixEnd_3243977 : Nat := 4983230072969 + 3 ^ 40 * 3243977 * 2
def baseEnd_3243977 : Nat := 1665719433130359658768727

theorem tailTrace_3243977 : CollatzResearch.WordTrace tailWord_3243977 prefixEnd_3243977 1665719433130359658768727 := by
  unfold tailWord_3243977
  simp only [CollatzResearch.WordTrace]
  refine ⟨118317561368632831008354185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78878374245755220672236123 118317561368632831008354185)
  ·
    refine ⟨88738171026474623256265639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118317561368632831008354185 88738171026474623256265639)
    ·
      refine ⟨133107256539711934884398459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88738171026474623256265639 133107256539711934884398459)
      ·
        refine ⟨199660884809567902326597689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133107256539711934884398459 199660884809567902326597689)
        ·
          refine ⟨149745663607175926744948267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199660884809567902326597689 149745663607175926744948267)
          ·
            refine ⟨224618495410763890117422401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149745663607175926744948267 224618495410763890117422401)
            ·
              refine ⟨168463871558072917588066801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224618495410763890117422401 168463871558072917588066801)
              ·
                refine ⟨126347903668554688191050101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168463871558072917588066801 126347903668554688191050101)
                ·
                  refine ⟨11845115968927002017910947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 126347903668554688191050101 11845115968927002017910947)
                  ·
                    refine ⟨17767673953390503026866421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11845115968927002017910947 17767673953390503026866421)
                    ·
                      refine ⟨1665719433130359658768727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17767673953390503026866421 1665719433130359658768727)
                      ·
                        rfl

theorem cell23_3243977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 1, 5].length) (baseStart_3243977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243977 prefixEnd_3243977 := by exact prefixLift 3243977
  have htrace : WordTrace (prefixWord ++ tailWord_3243977) baseStart_3243977 baseEnd_3243977 := by
    simpa [prefixWord, tailWord_3243977, baseEnd_3243977] using wordTrace_append hprefix tailTrace_3243977
  have hstable : (prefixWord ++ tailWord_3243977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243977).length < 2 ^ (prefixWord ++ tailWord_3243977).sum := by decide
  have hdescent : baseEnd_3243977 < baseStart_3243977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243984 : List Nat := [2, 1, 1, 1, 1, 2, 6, 1, 4, 4]
def baseStart_3243984 : Nat := 118140960795 + 3243984 * 2 ^ 59
def prefixEnd_3243984 : Nat := 4983230072969 + 3 ^ 40 * 3243984 * 2
def baseEnd_3243984 : Nat := 555241009164980377127065

theorem tailTrace_3243984 : CollatzResearch.WordTrace tailWord_3243984 prefixEnd_3243984 555241009164980377127065 := by
  unfold tailWord_3243984
  simp only [CollatzResearch.WordTrace]
  refine ⟨59158908339803735601929503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78878544453071647469239337 59158908339803735601929503)
  ·
    refine ⟨88738362509705603402894255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59158908339803735601929503 88738362509705603402894255)
    ·
      refine ⟨133107543764558405104341383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88738362509705603402894255 133107543764558405104341383)
      ·
        refine ⟨199661315646837607656512075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133107543764558405104341383 199661315646837607656512075)
        ·
          refine ⟨299491973470256411484768113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199661315646837607656512075 299491973470256411484768113)
          ·
            refine ⟨224618980102692308613576085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299491973470256411484768113 224618980102692308613576085)
            ·
              refine ⟨10529014692313701966261379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 224618980102692308613576085 10529014692313701966261379)
              ·
                refine ⟨15793522038470552949392069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10529014692313701966261379 15793522038470552949392069)
                ·
                  refine ⟨2961285382213228678011013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15793522038470552949392069 2961285382213228678011013)
                  ·
                    refine ⟨555241009164980377127065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2961285382213228678011013 555241009164980377127065)
                    ·
                      rfl

theorem cell23_3243984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 4, 4].length) (baseStart_3243984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3243984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3243984 prefixEnd_3243984 := by exact prefixLift 3243984
  have htrace : WordTrace (prefixWord ++ tailWord_3243984) baseStart_3243984 baseEnd_3243984 := by
    simpa [prefixWord, tailWord_3243984, baseEnd_3243984] using wordTrace_append hprefix tailTrace_3243984
  have hstable : (prefixWord ++ tailWord_3243984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243984).length < 2 ^ (prefixWord ++ tailWord_3243984).sum := by decide
  have hdescent : baseEnd_3243984 < baseStart_3243984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244004 : List Nat := [2, 3, 1, 1, 1, 1, 4, 3, 1, 2, 4]
def baseStart_3244004 : Nat := 118140960795 + 3244004 * 2 ^ 59
def prefixEnd_3244004 : Nat := 4983230072969 + 3 ^ 40 * 3244004 * 2
def baseEnd_3244004 : Nat := 1665733297108031053131103

theorem tailTrace_3244004 : CollatzResearch.WordTrace tailWord_3244004 prefixEnd_3244004 1665733297108031053131103 := by
  unfold tailWord_3244004
  simp only [CollatzResearch.WordTrace]
  refine ⟨59159273069767507309793533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78879030759690009746391377 59159273069767507309793533)
  ·
    refine ⟨22184727401162815241172575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59159273069767507309793533 22184727401162815241172575)
    ·
      refine ⟨33277091101744222861758863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22184727401162815241172575 33277091101744222861758863)
      ·
        refine ⟨49915636652616334292638295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33277091101744222861758863 49915636652616334292638295)
        ·
          refine ⟨74873454978924501438957443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49915636652616334292638295 74873454978924501438957443)
          ·
            refine ⟨112310182468386752158436165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74873454978924501438957443 112310182468386752158436165)
            ·
              refine ⟨21058159212822516029706781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112310182468386752158436165 21058159212822516029706781)
              ·
                refine ⟨7896809704808443511140043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21058159212822516029706781 7896809704808443511140043)
                ·
                  refine ⟨11845214557212665266710065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7896809704808443511140043 11845214557212665266710065)
                  ·
                    refine ⟨8883910917909498950032549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11845214557212665266710065 8883910917909498950032549)
                    ·
                      refine ⟨1665733297108031053131103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8883910917909498950032549 1665733297108031053131103)
                      ·
                        rfl

theorem cell23_3244004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_3244004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244004 prefixEnd_3244004 := by exact prefixLift 3244004
  have htrace : WordTrace (prefixWord ++ tailWord_3244004) baseStart_3244004 baseEnd_3244004 := by
    simpa [prefixWord, tailWord_3244004, baseEnd_3244004] using wordTrace_append hprefix tailTrace_3244004
  have hstable : (prefixWord ++ tailWord_3244004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244004).length < 2 ^ (prefixWord ++ tailWord_3244004).sum := by decide
  have hdescent : baseEnd_3244004 < baseStart_3244004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244014 : List Nat := [4, 1, 2, 1, 3, 1, 2, 9]
def baseStart_3244014 : Nat := 118140960795 + 3244014 * 2 ^ 59
def prefixEnd_3244014 : Nat := 4983230072969 + 3 ^ 40 * 3244014 * 2
def baseEnd_3244014 : Nat := 61694015996836148666891

theorem tailTrace_3244014 : CollatzResearch.WordTrace tailWord_3244014 prefixEnd_3244014 61694015996836148666891 := by
  unfold tailWord_3244014
  simp only [CollatzResearch.WordTrace]
  refine ⟨14789863858687348290931387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78879273912999190884967397 14789863858687348290931387)
  ·
    refine ⟨22184795788031022436397081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14789863858687348290931387 22184795788031022436397081)
    ·
      refine ⟨16638596841023266827297811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22184795788031022436397081 16638596841023266827297811)
      ·
        refine ⟨24957895261534900240946717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16638596841023266827297811 24957895261534900240946717)
        ·
          refine ⟨9359210723075587590355019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24957895261534900240946717 9359210723075587590355019)
          ·
            refine ⟨14038816084613381385532529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9359210723075587590355019 14038816084613381385532529)
            ·
              refine ⟨10529112063460036039149397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14038816084613381385532529 10529112063460036039149397)
              ·
                refine ⟨61694015996836148666891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10529112063460036039149397 61694015996836148666891)
                ·
                  rfl

theorem cell23_3244014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 9].length) (baseStart_3244014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244014 prefixEnd_3244014 := by exact prefixLift 3244014
  have htrace : WordTrace (prefixWord ++ tailWord_3244014) baseStart_3244014 baseEnd_3244014 := by
    simpa [prefixWord, tailWord_3244014, baseEnd_3244014] using wordTrace_append hprefix tailTrace_3244014
  have hstable : (prefixWord ++ tailWord_3244014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244014).length < 2 ^ (prefixWord ++ tailWord_3244014).sum := by decide
  have hdescent : baseEnd_3244014 < baseStart_3244014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244024 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 3, 3, 3]
def baseStart_3244024 : Nat := 118140960795 + 3244024 * 2 ^ 59
def prefixEnd_3244024 : Nat := 4983230072969 + 3 ^ 40 * 3244024 * 2
def baseEnd_3244024 : Nat := 1665743566721120974881011

theorem tailTrace_3244024 : CollatzResearch.WordTrace tailWord_3244024 prefixEnd_3244024 1665743566721120974881011 := by
  unfold tailWord_3244024
  simp only [CollatzResearch.WordTrace]
  refine ⟨59159637799731279017657563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78879517066308372023543417 59159637799731279017657563)
  ·
    refine ⟨88739456699596918526486345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59159637799731279017657563 88739456699596918526486345)
    ·
      refine ⟨66554592524697688894864759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88739456699596918526486345 66554592524697688894864759)
      ·
        refine ⟨99831888787046533342297139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66554592524697688894864759 99831888787046533342297139)
        ·
          refine ⟨149747833180569800013445709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99831888787046533342297139 149747833180569800013445709)
          ·
            refine ⟨56155437442713675005042141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149747833180569800013445709 56155437442713675005042141)
            ·
              refine ⟨21058289041017628126890803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56155437442713675005042141 21058289041017628126890803)
              ·
                refine ⟨31587433561526442190336205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21058289041017628126890803 31587433561526442190336205)
                ·
                  refine ⟨11845287585572415821376077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31587433561526442190336205 11845287585572415821376077)
                  ·
                    refine ⟨4441982844589655933016029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11845287585572415821376077 4441982844589655933016029)
                    ·
                      refine ⟨1665743566721120974881011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4441982844589655933016029 1665743566721120974881011)
                      ·
                        rfl

theorem cell23_3244024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 3, 3, 3].length) (baseStart_3244024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244024 prefixEnd_3244024 := by exact prefixLift 3244024
  have htrace : WordTrace (prefixWord ++ tailWord_3244024) baseStart_3244024 baseEnd_3244024 := by
    simpa [prefixWord, tailWord_3244024, baseEnd_3244024] using wordTrace_append hprefix tailTrace_3244024
  have hstable : (prefixWord ++ tailWord_3244024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244024).length < 2 ^ (prefixWord ++ tailWord_3244024).sum := by decide
  have hdescent : baseEnd_3244024 < baseStart_3244024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244028 : List Nat := [2, 2, 2, 1, 2, 2, 5, 1, 1, 2, 3]
def baseStart_3244028 : Nat := 118140960795 + 3244028 * 2 ^ 59
def prefixEnd_3244028 : Nat := 4983230072969 + 3 ^ 40 * 3244028 * 2
def baseEnd_3244028 : Nat := 1665745620643738959230993

theorem tailTrace_3244028 : CollatzResearch.WordTrace tailWord_3244028 prefixEnd_3244028 1665745620643738959230993 := by
  unfold tailWord_3244028
  simp only [CollatzResearch.WordTrace]
  refine ⟨59159710745724033359230369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78879614327632044478973825 59159710745724033359230369)
  ·
    refine ⟨44369783059293025019422777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59159710745724033359230369 44369783059293025019422777)
    ·
      refine ⟨33277337294469768764567083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44369783059293025019422777 33277337294469768764567083)
      ·
        refine ⟨49916005941704653146850625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33277337294469768764567083 49916005941704653146850625)
        ·
          refine ⟨37437004456278489860137969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49916005941704653146850625 37437004456278489860137969)
          ·
            refine ⟨28077753342208867395103477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37437004456278489860137969 28077753342208867395103477)
            ·
              refine ⟨2632289375832081318290951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28077753342208867395103477 2632289375832081318290951)
              ·
                refine ⟨3948434063748121977436427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2632289375832081318290951 3948434063748121977436427)
                ·
                  refine ⟨5922651095622182966154641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3948434063748121977436427 5922651095622182966154641)
                  ·
                    refine ⟨4441988321716637224615981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5922651095622182966154641 4441988321716637224615981)
                    ·
                      refine ⟨1665745620643738959230993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4441988321716637224615981 1665745620643738959230993)
                      ·
                        rfl

theorem cell23_3244028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 1, 2, 3].length) (baseStart_3244028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244028 prefixEnd_3244028 := by exact prefixLift 3244028
  have htrace : WordTrace (prefixWord ++ tailWord_3244028) baseStart_3244028 baseEnd_3244028 := by
    simpa [prefixWord, tailWord_3244028, baseEnd_3244028] using wordTrace_append hprefix tailTrace_3244028
  have hstable : (prefixWord ++ tailWord_3244028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244028).length < 2 ^ (prefixWord ++ tailWord_3244028).sum := by decide
  have hdescent : baseEnd_3244028 < baseStart_3244028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244036 : List Nat := [2, 3, 2, 4, 2, 1, 2, 2, 1, 1, 3]
def baseStart_3244036 : Nat := 118140960795 + 3244036 * 2 ^ 59
def prefixEnd_3244036 : Nat := 4983230072969 + 3 ^ 40 * 3244036 * 2
def baseEnd_3244036 : Nat := 1665749728488974927930957

theorem tailTrace_3244036 : CollatzResearch.WordTrace tailWord_3244036 prefixEnd_3244036 1665749728488974927930957 := by
  unfold tailWord_3244036
  simp only [CollatzResearch.WordTrace]
  refine ⟨59159856637709542042375981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78879808850279389389834641 59159856637709542042375981)
  ·
    refine ⟨22184946239141078265890993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59159856637709542042375981 22184946239141078265890993)
    ·
      refine ⟨16638709679355808699418245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22184946239141078265890993 16638709679355808699418245)
      ·
        refine ⟨3119758064879214131140921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16638709679355808699418245 3119758064879214131140921)
        ·
          refine ⟨2339818548659410598355691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3119758064879214131140921 2339818548659410598355691)
          ·
            refine ⟨3509727822989115897533537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2339818548659410598355691 3509727822989115897533537)
            ·
              refine ⟨2632295867241836923150153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3509727822989115897533537 2632295867241836923150153)
              ·
                refine ⟨1974221900431377692362615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2632295867241836923150153 1974221900431377692362615)
                ·
                  refine ⟨2961332850647066538543923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1974221900431377692362615 2961332850647066538543923)
                  ·
                    refine ⟨4441999275970599807815885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2961332850647066538543923 4441999275970599807815885)
                    ·
                      refine ⟨1665749728488974927930957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4441999275970599807815885 1665749728488974927930957)
                      ·
                        rfl

theorem cell23_3244036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_3244036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244036 prefixEnd_3244036 := by exact prefixLift 3244036
  have htrace : WordTrace (prefixWord ++ tailWord_3244036) baseStart_3244036 baseEnd_3244036 := by
    simpa [prefixWord, tailWord_3244036, baseEnd_3244036] using wordTrace_append hprefix tailTrace_3244036
  have hstable : (prefixWord ++ tailWord_3244036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244036).length < 2 ^ (prefixWord ++ tailWord_3244036).sum := by decide
  have hdescent : baseEnd_3244036 < baseStart_3244036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244042 : List Nat := [3, 1, 2, 2, 4, 1, 1, 4, 1, 2, 2]
def baseStart_3244042 : Nat := 118140960795 + 3244042 * 2 ^ 59
def prefixEnd_3244042 : Nat := 4983230072969 + 3 ^ 40 * 3244042 * 2
def baseEnd_3244042 : Nat := 1665752809372901904455929

theorem tailTrace_3244042 : CollatzResearch.WordTrace tailWord_3244042 prefixEnd_3244042 1665752809372901904455929 := by
  unfold tailWord_3244042
  simp only [CollatzResearch.WordTrace]
  refine ⟨29579983028349336777367595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78879954742264898072980253 29579983028349336777367595)
  ·
    refine ⟨44369974542524005166051393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29579983028349336777367595 44369974542524005166051393)
    ·
      refine ⟨33277480906893003874538545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44369974542524005166051393 33277480906893003874538545)
      ·
        refine ⟨24958110680169752905903909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33277480906893003874538545 24958110680169752905903909)
        ·
          refine ⟨4679645752531828669856983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24958110680169752905903909 4679645752531828669856983)
          ·
            refine ⟨7019468628797743004785475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4679645752531828669856983 7019468628797743004785475)
            ·
              refine ⟨10529202943196614507178213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7019468628797743004785475 10529202943196614507178213)
              ·
                refine ⟨1974225551849365220095915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10529202943196614507178213 1974225551849365220095915)
                ·
                  refine ⟨2961338327774047830143873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1974225551849365220095915 2961338327774047830143873)
                  ·
                    refine ⟨2221003745830535872607905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2961338327774047830143873 2221003745830535872607905)
                    ·
                      refine ⟨1665752809372901904455929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2221003745830535872607905 1665752809372901904455929)
                      ·
                        rfl

theorem cell23_3244042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_3244042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244042 prefixEnd_3244042 := by exact prefixLift 3244042
  have htrace : WordTrace (prefixWord ++ tailWord_3244042) baseStart_3244042 baseEnd_3244042 := by
    simpa [prefixWord, tailWord_3244042, baseEnd_3244042] using wordTrace_append hprefix tailTrace_3244042
  have hstable : (prefixWord ++ tailWord_3244042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244042).length < 2 ^ (prefixWord ++ tailWord_3244042).sum := by decide
  have hdescent : baseEnd_3244042 < baseStart_3244042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244051 : List Nat := [1, 1, 1, 2, 1, 4, 3, 2, 3, 3, 2]
def baseStart_3244051 : Nat := 118140960795 + 3244051 * 2 ^ 59
def prefixEnd_3244051 : Nat := 4983230072969 + 3 ^ 40 * 3244051 * 2
def baseEnd_3244051 : Nat := 1665757430698792369243387

theorem tailTrace_3244051 : CollatzResearch.WordTrace tailWord_3244051 prefixEnd_3244051 1665757430698792369243387 := by
  unfold tailWord_3244051
  simp only [CollatzResearch.WordTrace]
  refine ⟨118320260370364741646548007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78880173580243161097698671 118320260370364741646548007)
  ·
    refine ⟨177480390555547112469822011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118320260370364741646548007 177480390555547112469822011)
    ·
      refine ⟨266220585833320668704733017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177480390555547112469822011 266220585833320668704733017)
      ·
        refine ⟨199665439374990501528549763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266220585833320668704733017 199665439374990501528549763)
        ·
          refine ⟨299498159062485752292824645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199665439374990501528549763 299498159062485752292824645)
          ·
            refine ⟨56155904824216078554904621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 299498159062485752292824645 56155904824216078554904621)
            ·
              refine ⟨21058464309081029458089233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56155904824216078554904621 21058464309081029458089233)
              ·
                refine ⟨15793848231810772093566925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21058464309081029458089233 15793848231810772093566925)
                ·
                  refine ⟨5922693086929039535087597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15793848231810772093566925 5922693086929039535087597)
                  ·
                    refine ⟨2221009907598389825657849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5922693086929039535087597 2221009907598389825657849)
                    ·
                      refine ⟨1665757430698792369243387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2221009907598389825657849 1665757430698792369243387)
                      ·
                        rfl

theorem cell23_3244051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 3, 2].length) (baseStart_3244051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244051 prefixEnd_3244051 := by exact prefixLift 3244051
  have htrace : WordTrace (prefixWord ++ tailWord_3244051) baseStart_3244051 baseEnd_3244051 := by
    simpa [prefixWord, tailWord_3244051, baseEnd_3244051] using wordTrace_append hprefix tailTrace_3244051
  have hstable : (prefixWord ++ tailWord_3244051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244051).length < 2 ^ (prefixWord ++ tailWord_3244051).sum := by decide
  have hdescent : baseEnd_3244051 < baseStart_3244051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244058 : List Nat := [3, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3]
def baseStart_3244058 : Nat := 118140960795 + 3244058 * 2 ^ 59
def prefixEnd_3244058 : Nat := 4983230072969 + 3 ^ 40 * 3244058 * 2
def baseEnd_3244058 : Nat := 1665761025063373841855855

theorem tailTrace_3244058 : CollatzResearch.WordTrace tailWord_3244058 prefixEnd_3244058 1665761025063373841855855 := by
  unfold tailWord_3244058
  simp only [CollatzResearch.WordTrace]
  refine ⟨29580128920334845460513207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78880343787559587894701885 29580128920334845460513207)
  ·
    refine ⟨44370193380502268190769811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29580128920334845460513207 44370193380502268190769811)
    ·
      refine ⟨66555290070753402286154717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44370193380502268190769811 66555290070753402286154717)
      ·
        refine ⟨24958233776532525857308019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66555290070753402286154717 24958233776532525857308019)
        ·
          refine ⟨37437350664798788785962029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24958233776532525857308019 37437350664798788785962029)
          ·
            refine ⟨14039006499299545794735761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37437350664798788785962029 14039006499299545794735761)
            ·
              refine ⟨10529254874474659346051821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14039006499299545794735761 10529254874474659346051821)
              ·
                refine ⟨3948470577927997254769433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10529254874474659346051821 3948470577927997254769433)
                ·
                  refine ⟨2961352933445997941077075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3948470577927997254769433 2961352933445997941077075)
                  ·
                    refine ⟨4442029400168996911615613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2961352933445997941077075 4442029400168996911615613)
                    ·
                      refine ⟨1665761025063373841855855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4442029400168996911615613 1665761025063373841855855)
                      ·
                        rfl

theorem cell23_3244058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_3244058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244058 prefixEnd_3244058 := by exact prefixLift 3244058
  have htrace : WordTrace (prefixWord ++ tailWord_3244058) baseStart_3244058 baseEnd_3244058 := by
    simpa [prefixWord, tailWord_3244058, baseEnd_3244058] using wordTrace_append hprefix tailTrace_3244058
  have hstable : (prefixWord ++ tailWord_3244058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244058).length < 2 ^ (prefixWord ++ tailWord_3244058).sum := by decide
  have hdescent : baseEnd_3244058 < baseStart_3244058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244085 : List Nat := [1, 3, 3, 1, 1, 1, 6, 1, 1, 3, 2]
def baseStart_3244085 : Nat := 118140960795 + 3244085 * 2 ^ 59
def prefixEnd_3244085 : Nat := 4983230072969 + 3 ^ 40 * 3244085 * 2
def baseEnd_3244085 : Nat := 1665774889041045236218231

theorem tailTrace_3244085 : CollatzResearch.WordTrace tailWord_3244085 prefixEnd_3244085 1665774889041045236218231 := by
  unfold tailWord_3244085
  simp only [CollatzResearch.WordTrace]
  refine ⟨118321500452241565453285709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78881000301494376968857139 118321500452241565453285709)
  ·
    refine ⟨44370562669590587044982141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118321500452241565453285709 44370562669590587044982141)
    ·
      refine ⟨16638961001096470141868303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44370562669590587044982141 16638961001096470141868303)
      ·
        refine ⟨24958441501644705212802455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16638961001096470141868303 24958441501644705212802455)
        ·
          refine ⟨37437662252467057819203683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24958441501644705212802455 37437662252467057819203683)
          ·
            refine ⟨56156493378700586728805525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37437662252467057819203683 56156493378700586728805525)
            ·
              refine ⟨2632335627126590002912759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56156493378700586728805525 2632335627126590002912759)
              ·
                refine ⟨3948503440689885004369139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2632335627126590002912759 3948503440689885004369139)
                ·
                  refine ⟨5922755161034827506553709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3948503440689885004369139 5922755161034827506553709)
                  ·
                    refine ⟨2221033185388060314957641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5922755161034827506553709 2221033185388060314957641)
                    ·
                      refine ⟨1665774889041045236218231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2221033185388060314957641 1665774889041045236218231)
                      ·
                        rfl

theorem cell23_3244085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_3244085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244085 prefixEnd_3244085 := by exact prefixLift 3244085
  have htrace : WordTrace (prefixWord ++ tailWord_3244085) baseStart_3244085 baseEnd_3244085 := by
    simpa [prefixWord, tailWord_3244085, baseEnd_3244085] using wordTrace_append hprefix tailTrace_3244085
  have hstable : (prefixWord ++ tailWord_3244085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244085).length < 2 ^ (prefixWord ++ tailWord_3244085).sum := by decide
  have hdescent : baseEnd_3244085 < baseStart_3244085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244151 : List Nat := [1, 1, 3, 1, 1, 6, 1, 2, 2, 5]
def baseStart_3244151 : Nat := 118140960795 + 3244151 * 2 ^ 59
def prefixEnd_3244151 : Nat := 4983230072969 + 3 ^ 40 * 3244151 * 2
def baseEnd_3244151 : Nat := 555269592921413992664309

theorem tailTrace_3244151 : CollatzResearch.WordTrace tailWord_3244151 prefixEnd_3244151 555269592921413992664309 := by
  unfold tailWord_3244151
  simp only [CollatzResearch.WordTrace]
  refine ⟨118323907670002458725188307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78882605113334972483458871 118323907670002458725188307)
  ·
    refine ⟨177485861505003688087782461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118323907670002458725188307 177485861505003688087782461)
    ·
      refine ⟨66557198064376383032918423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177485861505003688087782461 66557198064376383032918423)
      ·
        refine ⟨99835797096564574549377635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66557198064376383032918423 99835797096564574549377635)
        ·
          refine ⟨149753695644846861824066453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99835797096564574549377635 149753695644846861824066453)
          ·
            refine ⟨7019704483352196648003115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 149753695644846861824066453 7019704483352196648003115)
            ·
              refine ⟨10529556725028294972004673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7019704483352196648003115 10529556725028294972004673)
              ·
                refine ⟨7897167543771221229003505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10529556725028294972004673 7897167543771221229003505)
                ·
                  refine ⟨5922875657828415921752629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7897167543771221229003505 5922875657828415921752629)
                  ·
                    refine ⟨555269592921413992664309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5922875657828415921752629 555269592921413992664309)
                    ·
                      rfl

theorem cell23_3244151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 5].length) (baseStart_3244151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244151 prefixEnd_3244151 := by exact prefixLift 3244151
  have htrace : WordTrace (prefixWord ++ tailWord_3244151) baseStart_3244151 baseEnd_3244151 := by
    simpa [prefixWord, tailWord_3244151, baseEnd_3244151] using wordTrace_append hprefix tailTrace_3244151
  have hstable : (prefixWord ++ tailWord_3244151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244151).length < 2 ^ (prefixWord ++ tailWord_3244151).sum := by decide
  have hdescent : baseEnd_3244151 < baseStart_3244151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244154 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 2, 7, 4]
def baseStart_3244154 : Nat := 118140960795 + 3244154 * 2 ^ 59
def prefixEnd_3244154 : Nat := 4983230072969 + 3 ^ 40 * 3244154 * 2
def baseEnd_3244154 : Nat := 1665810319206205466255413

theorem tailTrace_3244154 : CollatzResearch.WordTrace tailWord_3244154 prefixEnd_3244154 1665810319206205466255413 := by
  unfold tailWord_3244154
  simp only [CollatzResearch.WordTrace]
  refine ⟨29581004272247897559386879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78882678059327726825031677 29581004272247897559386879)
  ·
    refine ⟨44371506408371846339080319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29581004272247897559386879 44371506408371846339080319)
    ·
      refine ⟨66557259612557769508620479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44371506408371846339080319 66557259612557769508620479)
      ·
        refine ⟨99835889418836654262930719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66557259612557769508620479 99835889418836654262930719)
        ·
          refine ⟨149753834128254981394396079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99835889418836654262930719 149753834128254981394396079)
          ·
            refine ⟨224630751192382472091594119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149753834128254981394396079 224630751192382472091594119)
            ·
              refine ⟨336946126788573708137391179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224630751192382472091594119 336946126788573708137391179)
              ·
                refine ⟨505419190182860562206086769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 336946126788573708137391179 505419190182860562206086769)
                ·
                  refine ⟨379064392637145421654565077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 505419190182860562206086769 379064392637145421654565077)
                  ·
                    refine ⟨8884321702433095820028869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 379064392637145421654565077 8884321702433095820028869)
                    ·
                      refine ⟨1665810319206205466255413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8884321702433095820028869 1665810319206205466255413)
                      ·
                        rfl

theorem cell23_3244154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_3244154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244154 prefixEnd_3244154 := by exact prefixLift 3244154
  have htrace : WordTrace (prefixWord ++ tailWord_3244154) baseStart_3244154 baseEnd_3244154 := by
    simpa [prefixWord, tailWord_3244154, baseEnd_3244154] using wordTrace_append hprefix tailTrace_3244154
  have hstable : (prefixWord ++ tailWord_3244154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244154).length < 2 ^ (prefixWord ++ tailWord_3244154).sum := by decide
  have hdescent : baseEnd_3244154 < baseStart_3244154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244181 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 5, 4]
def baseStart_3244181 : Nat := 118140960795 + 3244181 * 2 ^ 59
def prefixEnd_3244181 : Nat := 4983230072969 + 3 ^ 40 * 3244181 * 2
def baseEnd_3244181 : Nat := 555274727727958953539263

theorem tailTrace_3244181 : CollatzResearch.WordTrace tailWord_3244181 prefixEnd_3244181 555274727727958953539263 := by
  unfold tailWord_3244181
  simp only [CollatzResearch.WordTrace]
  refine ⟨118325001859893773848780397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78883334573262515899186931 118325001859893773848780397)
  ·
    refine ⟨44371875697460165193292649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118325001859893773848780397 44371875697460165193292649)
    ·
      refine ⟨33278906773095123894969487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44371875697460165193292649 33278906773095123894969487)
      ·
        refine ⟨49918360159642685842454231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33278906773095123894969487 49918360159642685842454231)
        ·
          refine ⟨74877540239464028763681347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49918360159642685842454231 74877540239464028763681347)
          ·
            refine ⟨112316310359196043145522021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74877540239464028763681347 112316310359196043145522021)
            ·
              refine ⟨21059308192349258089785379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112316310359196043145522021 21059308192349258089785379)
              ·
                refine ⟨31588962288523887134678069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21059308192349258089785379 31588962288523887134678069)
                ·
                  refine ⟨2961465214549114418876069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31588962288523887134678069 2961465214549114418876069)
                  ·
                    refine ⟨555274727727958953539263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2961465214549114418876069 555274727727958953539263)
                    ·
                      rfl

theorem cell23_3244181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_3244181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244181 prefixEnd_3244181 := by exact prefixLift 3244181
  have htrace : WordTrace (prefixWord ++ tailWord_3244181) baseStart_3244181 baseEnd_3244181 := by
    simpa [prefixWord, tailWord_3244181, baseEnd_3244181] using wordTrace_append hprefix tailTrace_3244181
  have hstable : (prefixWord ++ tailWord_3244181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244181).length < 2 ^ (prefixWord ++ tailWord_3244181).sum := by decide
  have hdescent : baseEnd_3244181 < baseStart_3244181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244188 : List Nat := [2, 2, 3, 2, 1, 1, 4, 1, 2, 1, 4]
def baseStart_3244188 : Nat := 118140960795 + 3244188 * 2 ^ 59
def prefixEnd_3244188 : Nat := 4983230072969 + 3 ^ 40 * 3244188 * 2
def baseEnd_3244188 : Nat := 1665827777548458333230257

theorem tailTrace_3244188 : CollatzResearch.WordTrace tailWord_3244188 prefixEnd_3244188 1665827777548458333230257 := by
  unfold tailWord_3244188
  simp only [CollatzResearch.WordTrace]
  refine ⟨59162628585434207022142609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78883504780578942696190145 59162628585434207022142609)
  ·
    refine ⟨44371971439075655266606957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59162628585434207022142609 44371971439075655266606957)
    ·
      refine ⟨16639489289653370724977609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44371971439075655266606957 16639489289653370724977609)
      ·
        refine ⟨12479616967240028043733207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16639489289653370724977609 12479616967240028043733207)
        ·
          refine ⟨18719425450860042065599811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12479616967240028043733207 18719425450860042065599811)
          ·
            refine ⟨28079138176290063098399717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18719425450860042065599811 28079138176290063098399717)
            ·
              refine ⟨5264838408054386830949947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28079138176290063098399717 5264838408054386830949947)
              ·
                refine ⟨7897257612081580246424921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5264838408054386830949947 7897257612081580246424921)
                ·
                  refine ⟨5922943209061185184818691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7897257612081580246424921 5922943209061185184818691)
                  ·
                    refine ⟨8884414813591777777228037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5922943209061185184818691 8884414813591777777228037)
                    ·
                      refine ⟨1665827777548458333230257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8884414813591777777228037 1665827777548458333230257)
                      ·
                        rfl

theorem cell23_3244188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_3244188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244188 prefixEnd_3244188 := by exact prefixLift 3244188
  have htrace : WordTrace (prefixWord ++ tailWord_3244188) baseStart_3244188 baseEnd_3244188 := by
    simpa [prefixWord, tailWord_3244188, baseEnd_3244188] using wordTrace_append hprefix tailTrace_3244188
  have hstable : (prefixWord ++ tailWord_3244188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244188).length < 2 ^ (prefixWord ++ tailWord_3244188).sum := by decide
  have hdescent : baseEnd_3244188 < baseStart_3244188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244206 : List Nat := [4, 1, 4, 2, 2, 1, 2, 2, 5]
def baseStart_3244206 : Nat := 118140960795 + 3244206 * 2 ^ 59
def prefixEnd_3244206 : Nat := 4983230072969 + 3 ^ 40 * 3244206 * 2
def baseEnd_3244206 : Nat := 185093002244471029200575

theorem tailTrace_3244206 : CollatzResearch.WordTrace tailWord_3244206 prefixEnd_3244206 185093002244471029200575 := by
  unfold tailWord_3244206
  simp only [CollatzResearch.WordTrace]
  refine ⟨14790739210600400389805059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78883942456535468745626981 14790739210600400389805059)
  ·
    refine ⟨22186108815900600584707589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14790739210600400389805059 22186108815900600584707589)
    ·
      refine ⟨4159895402981362609632673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22186108815900600584707589 4159895402981362609632673)
      ·
        refine ⟨3119921552236021957224505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4159895402981362609632673 3119921552236021957224505)
        ·
          refine ⟨2339941164177016467918379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3119921552236021957224505 2339941164177016467918379)
          ·
            refine ⟨3509911746265524701877569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2339941164177016467918379 3509911746265524701877569)
            ·
              refine ⟨2632433809699143526408177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3509911746265524701877569 2632433809699143526408177)
              ·
                refine ⟨1974325357274357644806133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2632433809699143526408177 1974325357274357644806133)
                ·
                  refine ⟨185093002244471029200575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1974325357274357644806133 185093002244471029200575)
                  ·
                    rfl

theorem cell23_3244206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 2, 5].length) (baseStart_3244206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244206 prefixEnd_3244206 := by exact prefixLift 3244206
  have htrace : WordTrace (prefixWord ++ tailWord_3244206) baseStart_3244206 baseEnd_3244206 := by
    simpa [prefixWord, tailWord_3244206, baseEnd_3244206] using wordTrace_append hprefix tailTrace_3244206
  have hstable : (prefixWord ++ tailWord_3244206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244206).length < 2 ^ (prefixWord ++ tailWord_3244206).sum := by decide
  have hdescent : baseEnd_3244206 < baseStart_3244206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244215 : List Nat := [1, 1, 3, 1, 4, 3, 1, 4, 1, 4]
def baseStart_3244215 : Nat := 118140960795 + 3244215 * 2 ^ 59
def prefixEnd_3244215 : Nat := 4983230072969 + 3 ^ 40 * 3244215 * 2
def baseEnd_3244215 : Nat := 555280547175376575864211

theorem tailTrace_3244215 : CollatzResearch.WordTrace tailWord_3244215 prefixEnd_3244215 555280547175376575864211 := by
  unfold tailWord_3244215
  simp only [CollatzResearch.WordTrace]
  refine ⟨118326241941770597655518099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78884161294513731770345399 118326241941770597655518099)
  ·
    refine ⟨177489362912655896483277149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118326241941770597655518099 177489362912655896483277149)
    ·
      refine ⟨66558511092245961181228931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177489362912655896483277149 66558511092245961181228931)
      ·
        refine ⟨99837766638368941771843397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66558511092245961181228931 99837766638368941771843397)
        ·
          refine ⟨18719581244694176582220637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99837766638368941771843397 18719581244694176582220637)
          ·
            refine ⟨7019842966760316218332739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18719581244694176582220637 7019842966760316218332739)
            ·
              refine ⟨10529764450140474327499109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7019842966760316218332739 10529764450140474327499109)
              ·
                refine ⟨1974330834401338936406083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10529764450140474327499109 1974330834401338936406083)
                ·
                  refine ⟨2961496251602008404609125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1974330834401338936406083 2961496251602008404609125)
                  ·
                    refine ⟨555280547175376575864211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2961496251602008404609125 555280547175376575864211)
                    ·
                      rfl

theorem cell23_3244215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 4, 1, 4].length) (baseStart_3244215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244215 prefixEnd_3244215 := by exact prefixLift 3244215
  have htrace : WordTrace (prefixWord ++ tailWord_3244215) baseStart_3244215 baseEnd_3244215 := by
    simpa [prefixWord, tailWord_3244215, baseEnd_3244215] using wordTrace_append hprefix tailTrace_3244215
  have hstable : (prefixWord ++ tailWord_3244215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244215).length < 2 ^ (prefixWord ++ tailWord_3244215).sum := by decide
  have hdescent : baseEnd_3244215 < baseStart_3244215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244221 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 2, 5, 3]
def baseStart_3244221 : Nat := 118140960795 + 3244221 * 2 ^ 59
def prefixEnd_3244221 : Nat := 4983230072969 + 3 ^ 40 * 3244221 * 2
def baseEnd_3244221 : Nat := 1665844722410056704117605

theorem tailTrace_3244221 : CollatzResearch.WordTrace tailWord_3244221 prefixEnd_3244221 1665844722410056704117605 := by
  unfold tailWord_3244221
  simp only [CollatzResearch.WordTrace]
  refine ⟨118326460779748860680236517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78884307186499240453491011 118326460779748860680236517)
  ·
    refine ⟨22186211396202911377544347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118326460779748860680236517 22186211396202911377544347)
    ·
      refine ⟨33279317094304367066316521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22186211396202911377544347 33279317094304367066316521)
      ·
        refine ⟨24959487820728275299737391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33279317094304367066316521 24959487820728275299737391)
        ·
          refine ⟨37439231731092412949606087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24959487820728275299737391 37439231731092412949606087)
          ·
            refine ⟨56158847596638619424409131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37439231731092412949606087 56158847596638619424409131)
            ·
              refine ⟨84238271394957929136613697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56158847596638619424409131 84238271394957929136613697)
              ·
                refine ⟨63178703546218446852460273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84238271394957929136613697 63178703546218446852460273)
                ·
                  refine ⟨47384027659663835139345205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63178703546218446852460273 47384027659663835139345205)
                  ·
                    refine ⟨4442252593093484544313613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47384027659663835139345205 4442252593093484544313613)
                    ·
                      refine ⟨1665844722410056704117605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4442252593093484544313613 1665844722410056704117605)
                      ·
                        rfl

theorem cell23_3244221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_3244221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244221 prefixEnd_3244221 := by exact prefixLift 3244221
  have htrace : WordTrace (prefixWord ++ tailWord_3244221) baseStart_3244221 baseEnd_3244221 := by
    simpa [prefixWord, tailWord_3244221, baseEnd_3244221] using wordTrace_append hprefix tailTrace_3244221
  have hstable : (prefixWord ++ tailWord_3244221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244221).length < 2 ^ (prefixWord ++ tailWord_3244221).sum := by decide
  have hdescent : baseEnd_3244221 < baseStart_3244221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244228 : List Nat := [2, 3, 3, 1, 2, 1, 2, 3, 6]
def baseStart_3244228 : Nat := 118140960795 + 3244228 * 2 ^ 59
def prefixEnd_3244228 : Nat := 4983230072969 + 3 ^ 40 * 3244228 * 2
def baseEnd_3244228 : Nat := 185094257419404241858897

theorem tailTrace_3244228 : CollatzResearch.WordTrace tailWord_3244228 prefixEnd_3244228 185094257419404241858897 := by
  unfold tailWord_3244228
  simp only [CollatzResearch.WordTrace]
  refine ⟨59163358045361750437870669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78884477393815667250494225 59163358045361750437870669)
  ·
    refine ⟨22186259267010656414201501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59163358045361750437870669 22186259267010656414201501)
    ·
      refine ⟨8319847225128996155325563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22186259267010656414201501 8319847225128996155325563)
      ·
        refine ⟨12479770837693494232988345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8319847225128996155325563 12479770837693494232988345)
        ·
          refine ⟨9359828128270120674741259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12479770837693494232988345 9359828128270120674741259)
          ·
            refine ⟨14039742192405181012111889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9359828128270120674741259 14039742192405181012111889)
            ·
              refine ⟨10529806644303885759083917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14039742192405181012111889 10529806644303885759083917)
              ·
                refine ⟨3948677491613957159656469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10529806644303885759083917 3948677491613957159656469)
                ·
                  refine ⟨185094257419404241858897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3948677491613957159656469 185094257419404241858897)
                  ·
                    rfl

theorem cell23_3244228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 6].length) (baseStart_3244228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244228 prefixEnd_3244228 := by exact prefixLift 3244228
  have htrace : WordTrace (prefixWord ++ tailWord_3244228) baseStart_3244228 baseEnd_3244228 := by
    simpa [prefixWord, tailWord_3244228, baseEnd_3244228] using wordTrace_append hprefix tailTrace_3244228
  have hstable : (prefixWord ++ tailWord_3244228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244228).length < 2 ^ (prefixWord ++ tailWord_3244228).sum := by decide
  have hdescent : baseEnd_3244228 < baseStart_3244228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244241 : List Nat := [1, 2, 2, 1, 2, 2, 4, 1, 3, 5]
def baseStart_3244241 : Nat := 118140960795 + 3244241 * 2 ^ 59
def prefixEnd_3244241 : Nat := 4983230072969 + 3 ^ 40 * 3244241 * 2
def baseEnd_3244241 : Nat := 555284997341048875289171

theorem tailTrace_3244241 : CollatzResearch.WordTrace tailWord_3244241 prefixEnd_3244241 555284997341048875289171 := by
  unfold tailWord_3244241
  simp only [CollatzResearch.WordTrace]
  refine ⟨118327190239676404095964577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78884793493117602730643051 118327190239676404095964577)
  ·
    refine ⟨88745392679757303071973433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118327190239676404095964577 88745392679757303071973433)
    ·
      refine ⟨66559044509817977303980075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88745392679757303071973433 66559044509817977303980075)
      ·
        refine ⟨99838566764726965955970113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66559044509817977303980075 99838566764726965955970113)
        ·
          refine ⟨74878925073545224466977585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99838566764726965955970113 74878925073545224466977585)
          ·
            refine ⟨56159193805158918350233189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74878925073545224466977585 56159193805158918350233189)
            ·
              refine ⟨10529848838467297190668723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56159193805158918350233189 10529848838467297190668723)
              ·
                refine ⟨15794773257700945786003085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10529848838467297190668723 15794773257700945786003085)
                ·
                  refine ⟨5923039971637854669751157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15794773257700945786003085 5923039971637854669751157)
                  ·
                    refine ⟨555284997341048875289171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5923039971637854669751157 555284997341048875289171)
                    ·
                      rfl

theorem cell23_3244241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 5].length) (baseStart_3244241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244241 prefixEnd_3244241 := by exact prefixLift 3244241
  have htrace : WordTrace (prefixWord ++ tailWord_3244241) baseStart_3244241 baseEnd_3244241 := by
    simpa [prefixWord, tailWord_3244241, baseEnd_3244241] using wordTrace_append hprefix tailTrace_3244241
  have hstable : (prefixWord ++ tailWord_3244241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244241).length < 2 ^ (prefixWord ++ tailWord_3244241).sum := by decide
  have hdescent : baseEnd_3244241 < baseStart_3244241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244278 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4]
def baseStart_3244278 : Nat := 118140960795 + 3244278 * 2 ^ 59
def prefixEnd_3244278 : Nat := 4983230072969 + 3 ^ 40 * 3244278 * 2
def baseEnd_3244278 : Nat := 1665873990807362981104843

theorem tailTrace_3244278 : CollatzResearch.WordTrace tailWord_3244278 prefixEnd_3244278 1665873990807362981104843 := by
  unfold tailWord_3244278
  simp only [CollatzResearch.WordTrace]
  refine ⟨7395533733783897463441343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78885693160361572943374325 7395533733783897463441343)
  ·
    refine ⟨11093300600675846195162015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7395533733783897463441343 11093300600675846195162015)
    ·
      refine ⟨16639950901013769292743023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11093300600675846195162015 16639950901013769292743023)
      ·
        refine ⟨24959926351520653939114535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16639950901013769292743023 24959926351520653939114535)
        ·
          refine ⟨37439889527280980908671803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24959926351520653939114535 37439889527280980908671803)
          ·
            refine ⟨56159834290921471363007705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37439889527280980908671803 56159834290921471363007705)
            ·
              refine ⟨42119875718191103522255779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56159834290921471363007705 42119875718191103522255779)
              ·
                refine ⟨63179813577286655283383669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42119875718191103522255779 63179813577286655283383669)
                ·
                  refine ⟨5923107522870623932817219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63179813577286655283383669 5923107522870623932817219)
                  ·
                    refine ⟨8884661284305935899225829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5923107522870623932817219 8884661284305935899225829)
                    ·
                      refine ⟨1665873990807362981104843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8884661284305935899225829 1665873990807362981104843)
                      ·
                        rfl

theorem cell23_3244278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_3244278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244278 prefixEnd_3244278 := by exact prefixLift 3244278
  have htrace : WordTrace (prefixWord ++ tailWord_3244278) baseStart_3244278 baseEnd_3244278 := by
    simpa [prefixWord, tailWord_3244278, baseEnd_3244278] using wordTrace_append hprefix tailTrace_3244278
  have hstable : (prefixWord ++ tailWord_3244278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244278).length < 2 ^ (prefixWord ++ tailWord_3244278).sum := by decide
  have hdescent : baseEnd_3244278 < baseStart_3244278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244281 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 2, 6, 3]
def baseStart_3244281 : Nat := 118140960795 + 3244281 * 2 ^ 59
def prefixEnd_3244281 : Nat := 4983230072969 + 3 ^ 40 * 3244281 * 2
def baseEnd_3244281 : Nat := 1665875531249326469367329

theorem tailTrace_3244281 : CollatzResearch.WordTrace tailWord_3244281 prefixEnd_3244281 1665875531249326469367329 := by
  unfold tailWord_3244281
  simp only [CollatzResearch.WordTrace]
  refine ⟨118328649159531490927420697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78885766106354327284947131 118328649159531490927420697)
  ·
    refine ⟨88746486869648618195565523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118328649159531490927420697 88746486869648618195565523)
    ·
      refine ⟨133119730304472927293348285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88746486869648618195565523 133119730304472927293348285)
      ·
        refine ⟨49919898864177347735005607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133119730304472927293348285 49919898864177347735005607)
        ·
          refine ⟨74879848296266021602508411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49919898864177347735005607 74879848296266021602508411)
          ·
            refine ⟨112319772444399032403762617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74879848296266021602508411 112319772444399032403762617)
            ·
              refine ⟨84239829333299274302821963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112319772444399032403762617 84239829333299274302821963)
              ·
                refine ⟨126359743999948911454232945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84239829333299274302821963 126359743999948911454232945)
                ·
                  refine ⟨94769807999961683590674709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126359743999948911454232945 94769807999961683590674709)
                  ·
                    refine ⟨4442334749998203918312877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94769807999961683590674709 4442334749998203918312877)
                    ·
                      refine ⟨1665875531249326469367329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4442334749998203918312877 1665875531249326469367329)
                      ·
                        rfl

theorem cell23_3244281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_3244281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244281 prefixEnd_3244281 := by exact prefixLift 3244281
  have htrace : WordTrace (prefixWord ++ tailWord_3244281) baseStart_3244281 baseEnd_3244281 := by
    simpa [prefixWord, tailWord_3244281, baseEnd_3244281] using wordTrace_append hprefix tailTrace_3244281
  have hstable : (prefixWord ++ tailWord_3244281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244281).length < 2 ^ (prefixWord ++ tailWord_3244281).sum := by decide
  have hdescent : baseEnd_3244281 < baseStart_3244281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244288 : List Nat := [2, 1, 1, 2, 1, 1, 4, 5, 2, 4]
def baseStart_3244288 : Nat := 118140960795 + 3244288 * 2 ^ 59
def prefixEnd_3244288 : Nat := 4983230072969 + 3 ^ 40 * 3244288 * 2
def baseEnd_3244288 : Nat := 555293041871302647326599

theorem tailTrace_3244288 : CollatzResearch.WordTrace tailWord_3244288 prefixEnd_3244288 555293041871302647326599 := by
  unfold tailWord_3244288
  simp only [CollatzResearch.WordTrace]
  refine ⟨59164452235253065561462759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78885936313670754081950345 59164452235253065561462759)
  ·
    refine ⟨88746678352879598342194139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59164452235253065561462759 88746678352879598342194139)
    ·
      refine ⟨133120017529319397513291209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88746678352879598342194139 133120017529319397513291209)
      ·
        refine ⟨99840013146989548134968407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133120017529319397513291209 99840013146989548134968407)
        ·
          refine ⟨149760019720484322202452611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99840013146989548134968407 149760019720484322202452611)
          ·
            refine ⟨224640029580726483303678917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149760019720484322202452611 224640029580726483303678917)
            ·
              refine ⟨42120005546386215619439797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 224640029580726483303678917 42120005546386215619439797)
              ·
                refine ⟨3948750519973707714322481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42120005546386215619439797 3948750519973707714322481)
                ·
                  refine ⟨2961562889980280785741861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3948750519973707714322481 2961562889980280785741861)
                  ·
                    refine ⟨555293041871302647326599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2961562889980280785741861 555293041871302647326599)
                    ·
                      rfl

theorem cell23_3244288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 2, 4].length) (baseStart_3244288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244288 prefixEnd_3244288 := by exact prefixLift 3244288
  have htrace : WordTrace (prefixWord ++ tailWord_3244288) baseStart_3244288 baseEnd_3244288 := by
    simpa [prefixWord, tailWord_3244288, baseEnd_3244288] using wordTrace_append hprefix tailTrace_3244288
  have hstable : (prefixWord ++ tailWord_3244288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244288).length < 2 ^ (prefixWord ++ tailWord_3244288).sum := by decide
  have hdescent : baseEnd_3244288 < baseStart_3244288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244291 : List Nat := [1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 6]
def baseStart_3244291 : Nat := 118140960795 + 3244291 * 2 ^ 59
def prefixEnd_3244291 : Nat := 4983230072969 + 3 ^ 40 * 3244291 * 2
def baseEnd_3244291 : Nat := 1665880666055871430242283

theorem tailTrace_3244291 : CollatzResearch.WordTrace tailWord_3244291 prefixEnd_3244291 1665880666055871430242283 := by
  unfold tailWord_3244291
  simp only [CollatzResearch.WordTrace]
  refine ⟨118329013889495262635284727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78886009259663508423523151 118329013889495262635284727)
  ·
    refine ⟨177493520834242893952927091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118329013889495262635284727 177493520834242893952927091)
    ·
      refine ⟨266240281251364340929390637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177493520834242893952927091 266240281251364340929390637)
      ·
        refine ⟨99840105469261627848521489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266240281251364340929390637 99840105469261627848521489)
        ·
          refine ⟨74880079101946220886391117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99840105469261627848521489 74880079101946220886391117)
          ·
            refine ⟨28080029663229832832396669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74880079101946220886391117 28080029663229832832396669)
            ·
              refine ⟨10530011123711187312148751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28080029663229832832396669 10530011123711187312148751)
              ·
                refine ⟨15795016685566780968223127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10530011123711187312148751 15795016685566780968223127)
                ·
                  refine ⟨23692525028350171452334691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15795016685566780968223127 23692525028350171452334691)
                  ·
                    refine ⟨35538787542525257178502037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23692525028350171452334691 35538787542525257178502037)
                    ·
                      refine ⟨1665880666055871430242283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35538787542525257178502037 1665880666055871430242283)
                      ·
                        rfl

theorem cell23_3244291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_3244291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244291 prefixEnd_3244291 := by exact prefixLift 3244291
  have htrace : WordTrace (prefixWord ++ tailWord_3244291) baseStart_3244291 baseEnd_3244291 := by
    simpa [prefixWord, tailWord_3244291, baseEnd_3244291] using wordTrace_append hprefix tailTrace_3244291
  have hstable : (prefixWord ++ tailWord_3244291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244291).length < 2 ^ (prefixWord ++ tailWord_3244291).sum := by decide
  have hdescent : baseEnd_3244291 < baseStart_3244291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244298 : List Nat := [3, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3]
def baseStart_3244298 : Nat := 118140960795 + 3244298 * 2 ^ 59
def prefixEnd_3244298 : Nat := 4983230072969 + 3 ^ 40 * 3244298 * 2
def baseEnd_3244298 : Nat := 1665884260420452902854751

theorem tailTrace_3244298 : CollatzResearch.WordTrace tailWord_3244298 prefixEnd_3244298 1665884260420452902854751 := by
  unfold tailWord_3244298
  simp only [CollatzResearch.WordTrace]
  refine ⟨29582317300117475707697387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78886179466979935220526365 29582317300117475707697387)
  ·
    refine ⟨44373475950176213561546081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29582317300117475707697387 44373475950176213561546081)
    ·
      refine ⟨33280106962632160171159561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44373475950176213561546081 33280106962632160171159561)
      ·
        refine ⟨24960080221974120128369671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33280106962632160171159561 24960080221974120128369671)
        ·
          refine ⟨37440120332961180192554507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24960080221974120128369671 37440120332961180192554507)
          ·
            refine ⟨56160180499441770288831761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37440120332961180192554507 56160180499441770288831761)
            ·
              refine ⟨42120135374581327716623821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56160180499441770288831761 42120135374581327716623821)
              ·
                refine ⟨15795050765467997893733933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42120135374581327716623821 15795050765467997893733933)
                ·
                  refine ⟨5923144037050499210150225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15795050765467997893733933 5923144037050499210150225)
                  ·
                    refine ⟨4442358027787874407612669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5923144037050499210150225 4442358027787874407612669)
                    ·
                      refine ⟨1665884260420452902854751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4442358027787874407612669 1665884260420452902854751)
                      ·
                        rfl

theorem cell23_3244298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_3244298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244298 prefixEnd_3244298 := by exact prefixLift 3244298
  have htrace : WordTrace (prefixWord ++ tailWord_3244298) baseStart_3244298 baseEnd_3244298 := by
    simpa [prefixWord, tailWord_3244298, baseEnd_3244298] using wordTrace_append hprefix tailTrace_3244298
  have hstable : (prefixWord ++ tailWord_3244298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244298).length < 2 ^ (prefixWord ++ tailWord_3244298).sum := by decide
  have hdescent : baseEnd_3244298 < baseStart_3244298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244361 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 4, 6]
def baseStart_3244361 : Nat := 118140960795 + 3244361 * 2 ^ 59
def prefixEnd_3244361 : Nat := 4983230072969 + 3 ^ 40 * 3244361 * 2
def baseEnd_3244361 : Nat := 555305536567228718788987

theorem tailTrace_3244361 : CollatzResearch.WordTrace tailWord_3244361 prefixEnd_3244361 555305536567228718788987 := by
  unfold tailWord_3244361
  simp only [CollatzResearch.WordTrace]
  refine ⟨118331566999241664590332937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78887711332827776393555291 118331566999241664590332937)
  ·
    refine ⟨88748675249431248442749703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118331566999241664590332937 88748675249431248442749703)
    ·
      refine ⟨133123012874146872664124555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88748675249431248442749703 133123012874146872664124555)
      ·
        refine ⟨199684519311220308996186833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133123012874146872664124555 199684519311220308996186833)
        ·
          refine ⟨149763389483415231747140125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199684519311220308996186833 149763389483415231747140125)
          ·
            refine ⟨56161271056280711905177547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149763389483415231747140125 56161271056280711905177547)
            ·
              refine ⟨84241906584421067857766321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56161271056280711905177547 84241906584421067857766321)
              ·
                refine ⟨63181429938315800893324741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84241906584421067857766321 63181429938315800893324741)
                ·
                  refine ⟨11846518113434212667498389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63181429938315800893324741 11846518113434212667498389)
                  ·
                    refine ⟨555305536567228718788987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11846518113434212667498389 555305536567228718788987)
                    ·
                      rfl

theorem cell23_3244361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 6].length) (baseStart_3244361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244361 prefixEnd_3244361 := by exact prefixLift 3244361
  have htrace : WordTrace (prefixWord ++ tailWord_3244361) baseStart_3244361 baseEnd_3244361 := by
    simpa [prefixWord, tailWord_3244361, baseEnd_3244361] using wordTrace_append hprefix tailTrace_3244361
  have hstable : (prefixWord ++ tailWord_3244361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244361).length < 2 ^ (prefixWord ++ tailWord_3244361).sum := by decide
  have hdescent : baseEnd_3244361 < baseStart_3244361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244371 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 5]
def baseStart_3244371 : Nat := 118140960795 + 3244371 * 2 ^ 59
def prefixEnd_3244371 : Nat := 4983230072969 + 3 ^ 40 * 3244371 * 2
def baseEnd_3244371 : Nat := 1665921744508231117241915

theorem tailTrace_3244371 : CollatzResearch.WordTrace tailWord_3244371 prefixEnd_3244371 1665921744508231117241915 := by
  unfold tailWord_3244371
  simp only [CollatzResearch.WordTrace]
  refine ⟨118331931729205436298196967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78887954486136957532131311 118331931729205436298196967)
  ·
    refine ⟨177497897593808154447295451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118331931729205436298196967 177497897593808154447295451)
    ·
      refine ⟨266246846390712231670943177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177497897593808154447295451 266246846390712231670943177)
      ·
        refine ⟨199685134793034173753207383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266246846390712231670943177 199685134793034173753207383)
        ·
          refine ⟨299527702189551260629811075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199685134793034173753207383 299527702189551260629811075)
          ·
            refine ⟨449291553284326890944716613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299527702189551260629811075 449291553284326890944716613)
            ·
              refine ⟨84242166240811292052134365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 449291553284326890944716613 84242166240811292052134365)
              ·
                refine ⟨31590812340304234519550387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84242166240811292052134365 31590812340304234519550387)
                ·
                  refine ⟨47386218510456351779325581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31590812340304234519550387 47386218510456351779325581)
                  ·
                    refine ⟨17769831941421131917247093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47386218510456351779325581 17769831941421131917247093)
                    ·
                      refine ⟨1665921744508231117241915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17769831941421131917247093 1665921744508231117241915)
                      ·
                        rfl

theorem cell23_3244371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 5].length) (baseStart_3244371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244371 prefixEnd_3244371 := by exact prefixLift 3244371
  have htrace : WordTrace (prefixWord ++ tailWord_3244371) baseStart_3244371 baseEnd_3244371 := by
    simpa [prefixWord, tailWord_3244371, baseEnd_3244371] using wordTrace_append hprefix tailTrace_3244371
  have hstable : (prefixWord ++ tailWord_3244371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244371).length < 2 ^ (prefixWord ++ tailWord_3244371).sum := by decide
  have hdescent : baseEnd_3244371 < baseStart_3244371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244380 : List Nat := [2, 2, 4, 3, 1, 2, 2, 2, 1, 2, 2]
def baseStart_3244380 : Nat := 118140960795 + 3244380 * 2 ^ 59
def prefixEnd_3244380 : Nat := 4983230072969 + 3 ^ 40 * 3244380 * 2
def baseEnd_3244380 : Nat := 1665926365834121582029375

theorem tailTrace_3244380 : CollatzResearch.WordTrace tailWord_3244380 prefixEnd_3244380 1665926365834121582029375 := by
  unfold tailWord_3244380
  simp only [CollatzResearch.WordTrace]
  refine ⟨59166129993086415417637297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78888173324115220556849729 59166129993086415417637297)
  ·
    refine ⟨44374597494814811563227973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59166129993086415417637297 44374597494814811563227973)
    ·
      refine ⟨8320237030277777168105245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44374597494814811563227973 8320237030277777168105245)
      ·
        refine ⟨3120088886354166438039467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8320237030277777168105245 3120088886354166438039467)
        ·
          refine ⟨4680133329531249657059201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3120088886354166438039467 4680133329531249657059201)
          ·
            refine ⟨3510099997148437242794401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4680133329531249657059201 3510099997148437242794401)
            ·
              refine ⟨2632574997861327932095801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3510099997148437242794401 2632574997861327932095801)
              ·
                refine ⟨1974431248395995949071851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2632574997861327932095801 1974431248395995949071851)
                ·
                  refine ⟨2961646872593993923607777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1974431248395995949071851 2961646872593993923607777)
                  ·
                    refine ⟨2221235154445495442705833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2961646872593993923607777 2221235154445495442705833)
                    ·
                      refine ⟨1665926365834121582029375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2221235154445495442705833 1665926365834121582029375)
                      ·
                        rfl

theorem cell23_3244380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_3244380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244380 prefixEnd_3244380 := by exact prefixLift 3244380
  have htrace : WordTrace (prefixWord ++ tailWord_3244380) baseStart_3244380 baseEnd_3244380 := by
    simpa [prefixWord, tailWord_3244380, baseEnd_3244380] using wordTrace_append hprefix tailTrace_3244380
  have hstable : (prefixWord ++ tailWord_3244380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244380).length < 2 ^ (prefixWord ++ tailWord_3244380).sum := by decide
  have hdescent : baseEnd_3244380 < baseStart_3244380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244388 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 1, 6, 3]
def baseStart_3244388 : Nat := 118140960795 + 3244388 * 2 ^ 59
def prefixEnd_3244388 : Nat := 4983230072969 + 3 ^ 40 * 3244388 * 2
def baseEnd_3244388 : Nat := 1665930473679357550729337

theorem tailTrace_3244388 : CollatzResearch.WordTrace tailWord_3244388 prefixEnd_3244388 1665930473679357550729337 := by
  unfold tailWord_3244388
  simp only [CollatzResearch.WordTrace]
  refine ⟨59166275885071924100782909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78888367846762565467710545 59166275885071924100782909)
  ·
    refine ⟨22187353456901971537793591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59166275885071924100782909 22187353456901971537793591)
    ·
      refine ⟨33281030185352957306690387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22187353456901971537793591 33281030185352957306690387)
      ·
        refine ⟨49921545278029435960035581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33281030185352957306690387 49921545278029435960035581)
        ·
          refine ⟨18720579479261038485013343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49921545278029435960035581 18720579479261038485013343)
          ·
            refine ⟨28080869218891557727520015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18720579479261038485013343 28080869218891557727520015)
            ·
              refine ⟨42121303828337336591280023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28080869218891557727520015 42121303828337336591280023)
              ·
                refine ⟨63181955742506004886920035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42121303828337336591280023 63181955742506004886920035)
                ·
                  refine ⟨94772933613759007330380053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63181955742506004886920035 94772933613759007330380053)
                  ·
                    refine ⟨4442481263144953468611565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94772933613759007330380053 4442481263144953468611565)
                    ·
                      refine ⟨1665930473679357550729337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4442481263144953468611565 1665930473679357550729337)
                      ·
                        rfl

theorem cell23_3244388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_3244388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244388 prefixEnd_3244388 := by exact prefixLift 3244388
  have htrace : WordTrace (prefixWord ++ tailWord_3244388) baseStart_3244388 baseEnd_3244388 := by
    simpa [prefixWord, tailWord_3244388, baseEnd_3244388] using wordTrace_append hprefix tailTrace_3244388
  have hstable : (prefixWord ++ tailWord_3244388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244388).length < 2 ^ (prefixWord ++ tailWord_3244388).sum := by decide
  have hdescent : baseEnd_3244388 < baseStart_3244388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244402 : List Nat := [3, 2, 1, 2, 1, 4, 2, 1, 1, 4, 2]
def baseStart_3244402 : Nat := 118140960795 + 3244402 * 2 ^ 59
def prefixEnd_3244402 : Nat := 4983230072969 + 3 ^ 40 * 3244402 * 2
def baseEnd_3244402 : Nat := 1665937662408520495954273

theorem tailTrace_3244402 : CollatzResearch.WordTrace tailWord_3244402 prefixEnd_3244402 1665937662408520495954273 := by
  unfold tailWord_3244402
  simp only [CollatzResearch.WordTrace]
  refine ⟨29583265598023282148143865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78888708261395419061716973 29583265598023282148143865)
  ·
    refine ⟨22187449198517461611107899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29583265598023282148143865 22187449198517461611107899)
    ·
      refine ⟨33281173797776192416661849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22187449198517461611107899 33281173797776192416661849)
      ·
        refine ⟨24960880348332144312496387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33281173797776192416661849 24960880348332144312496387)
        ·
          refine ⟨37441320522498216468744581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24960880348332144312496387 37441320522498216468744581)
          ·
            refine ⟨7020247597968415587889609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37441320522498216468744581 7020247597968415587889609)
            ·
              refine ⟨5265185698476311690917207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7020247597968415587889609 5265185698476311690917207)
              ·
                refine ⟨7897778547714467536375811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5265185698476311690917207 7897778547714467536375811)
                ·
                  refine ⟨11846667821571701304563717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7897778547714467536375811 11846667821571701304563717)
                  ·
                    refine ⟨2221250216544693994605697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11846667821571701304563717 2221250216544693994605697)
                    ·
                      refine ⟨1665937662408520495954273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2221250216544693994605697 1665937662408520495954273)
                      ·
                        rfl

theorem cell23_3244402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_3244402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244402 prefixEnd_3244402 := by exact prefixLift 3244402
  have htrace : WordTrace (prefixWord ++ tailWord_3244402) baseStart_3244402 baseEnd_3244402 := by
    simpa [prefixWord, tailWord_3244402, baseEnd_3244402] using wordTrace_append hprefix tailTrace_3244402
  have hstable : (prefixWord ++ tailWord_3244402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244402).length < 2 ^ (prefixWord ++ tailWord_3244402).sum := by decide
  have hdescent : baseEnd_3244402 < baseStart_3244402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244425 : List Nat := [1, 2, 1, 1, 6, 1, 1, 5, 5]
def baseStart_3244425 : Nat := 118140960795 + 3244425 * 2 ^ 59
def prefixEnd_3244425 : Nat := 4983230072969 + 3 ^ 40 * 3244425 * 2
def baseEnd_3244425 : Nat := 185105496940397100662963

theorem tailTrace_3244425 : CollatzResearch.WordTrace tailWord_3244425 prefixEnd_3244425 185105496940397100662963 := by
  unfold tailWord_3244425
  simp only [CollatzResearch.WordTrace]
  refine ⟨118333901271009803520662729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78889267514006535680441819 118333901271009803520662729)
  ·
    refine ⟨88750425953257352640497047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118333901271009803520662729 88750425953257352640497047)
    ·
      refine ⟨133125638929886028960745571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88750425953257352640497047 133125638929886028960745571)
      ·
        refine ⟨199688458394829043441118357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133125638929886028960745571 199688458394829043441118357)
        ·
          refine ⟨9360396487257611411302423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 199688458394829043441118357 9360396487257611411302423)
          ·
            refine ⟨14040594730886417116953635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9360396487257611411302423 14040594730886417116953635)
            ·
              refine ⟨21060892096329625675430453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14040594730886417116953635 21060892096329625675430453)
              ·
                refine ⟨1974458634030902407071605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21060892096329625675430453 1974458634030902407071605)
                ·
                  refine ⟨185105496940397100662963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1974458634030902407071605 185105496940397100662963)
                  ·
                    rfl

theorem cell23_3244425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 5, 5].length) (baseStart_3244425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244425 prefixEnd_3244425 := by exact prefixLift 3244425
  have htrace : WordTrace (prefixWord ++ tailWord_3244425) baseStart_3244425 baseEnd_3244425 := by
    simpa [prefixWord, tailWord_3244425, baseEnd_3244425] using wordTrace_append hprefix tailTrace_3244425
  have hstable : (prefixWord ++ tailWord_3244425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244425).length < 2 ^ (prefixWord ++ tailWord_3244425).sum := by decide
  have hdescent : baseEnd_3244425 < baseStart_3244425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244492 : List Nat := [2, 2, 1, 4, 3, 1, 1, 2, 2, 1, 4]
def baseStart_3244492 : Nat := 118140960795 + 3244492 * 2 ^ 59
def prefixEnd_3244492 : Nat := 4983230072969 + 3 ^ 40 * 3244492 * 2
def baseEnd_3244492 : Nat := 1665983875667425143828859

theorem tailTrace_3244492 : CollatzResearch.WordTrace tailWord_3244492 prefixEnd_3244492 1665983875667425143828859 := by
  unfold tailWord_3244492
  simp only [CollatzResearch.WordTrace]
  refine ⟨59168172480883536981675865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78890896641178049308901153 59168172480883536981675865)
  ·
    refine ⟨44376129360662652736256899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59168172480883536981675865 44376129360662652736256899)
    ·
      refine ⟨66564194040993979104385349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44376129360662652736256899 66564194040993979104385349)
      ·
        refine ⟨12480786382686371082072253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66564194040993979104385349 12480786382686371082072253)
        ·
          refine ⟨4680294893507389155777095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12480786382686371082072253 4680294893507389155777095)
          ·
            refine ⟨7020442340261083733665643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4680294893507389155777095 7020442340261083733665643)
            ·
              refine ⟨10530663510391625600498465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7020442340261083733665643 10530663510391625600498465)
              ·
                refine ⟨7897997632793719200373849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10530663510391625600498465 7897997632793719200373849)
                ·
                  refine ⟨5923498224595289400280387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7897997632793719200373849 5923498224595289400280387)
                  ·
                    refine ⟨8885247336892934100420581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5923498224595289400280387 8885247336892934100420581)
                    ·
                      refine ⟨1665983875667425143828859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8885247336892934100420581 1665983875667425143828859)
                      ·
                        rfl

theorem cell23_3244492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_3244492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244492 prefixEnd_3244492 := by exact prefixLift 3244492
  have htrace : WordTrace (prefixWord ++ tailWord_3244492) baseStart_3244492 baseEnd_3244492 := by
    simpa [prefixWord, tailWord_3244492, baseEnd_3244492] using wordTrace_append hprefix tailTrace_3244492
  have hstable : (prefixWord ++ tailWord_3244492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244492).length < 2 ^ (prefixWord ++ tailWord_3244492).sum := by decide
  have hdescent : baseEnd_3244492 < baseStart_3244492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244535 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 5, 5, 2]
def baseStart_3244535 : Nat := 118140960795 + 3244535 * 2 ^ 59
def prefixEnd_3244535 : Nat := 4983230072969 + 3 ^ 40 * 3244535 * 2
def baseEnd_3244535 : Nat := 1666005955335568475591161

theorem tailTrace_3244535 : CollatzResearch.WordTrace tailWord_3244535 prefixEnd_3244535 1666005955335568475591161 := by
  unfold tailWord_3244535
  simp only [CollatzResearch.WordTrace]
  refine ⟨118337913300611292307167059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78891942200407528204778039 118337913300611292307167059)
  ·
    refine ⟨177506869950916938460750589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118337913300611292307167059 177506869950916938460750589)
    ·
      refine ⟨66565076231593851922781471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177506869950916938460750589 66565076231593851922781471)
      ·
        refine ⟨99847614347390777884172207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66565076231593851922781471 99847614347390777884172207)
        ·
          refine ⟨149771421521086166826258311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99847614347390777884172207 149771421521086166826258311)
          ·
            refine ⟨224657132281629250239387467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149771421521086166826258311 224657132281629250239387467)
            ·
              refine ⟨336985698422443875359081201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224657132281629250239387467 336985698422443875359081201)
              ·
                refine ⟨252739273816832906519310901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 336985698422443875359081201 252739273816832906519310901)
                ·
                  refine ⟨23694306920328084986185397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 252739273816832906519310901 23694306920328084986185397)
                  ·
                    refine ⟨2221341273780757967454881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23694306920328084986185397 2221341273780757967454881)
                    ·
                      refine ⟨1666005955335568475591161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2221341273780757967454881 1666005955335568475591161)
                      ·
                        rfl

theorem cell23_3244535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 5, 2].length) (baseStart_3244535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244535 prefixEnd_3244535 := by exact prefixLift 3244535
  have htrace : WordTrace (prefixWord ++ tailWord_3244535) baseStart_3244535 baseEnd_3244535 := by
    simpa [prefixWord, tailWord_3244535, baseEnd_3244535] using wordTrace_append hprefix tailTrace_3244535
  have hstable : (prefixWord ++ tailWord_3244535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244535).length < 2 ^ (prefixWord ++ tailWord_3244535).sum := by decide
  have hdescent : baseEnd_3244535 < baseStart_3244535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244538 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 2, 4, 5]
def baseStart_3244538 : Nat := 118140960795 + 3244538 * 2 ^ 59
def prefixEnd_3244538 : Nat := 4983230072969 + 3 ^ 40 * 3244538 * 2
def baseEnd_3244538 : Nat := 1666007495777531963853647

theorem tailTrace_3244538 : CollatzResearch.WordTrace tailWord_3244538 prefixEnd_3244538 1666007495777531963853647 := by
  unfold tailWord_3244538
  simp only [CollatzResearch.WordTrace]
  refine ⟨29584505679900105954881567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78892015146400282546350845 29584505679900105954881567)
  ·
    refine ⟨44376758519850158932322351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29584505679900105954881567 44376758519850158932322351)
    ·
      refine ⟨66565137779775238398483527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44376758519850158932322351 66565137779775238398483527)
      ·
        refine ⟨99847706669662857597725291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66565137779775238398483527 99847706669662857597725291)
        ·
          refine ⟨149771560004494286396587937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99847706669662857597725291 149771560004494286396587937)
          ·
            refine ⟨112328670003370714797440953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149771560004494286396587937 112328670003370714797440953)
            ·
              refine ⟨84246502502528036098080715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112328670003370714797440953 84246502502528036098080715)
              ·
                refine ⟨126369753753792054147121073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84246502502528036098080715 126369753753792054147121073)
                ·
                  refine ⟨94777315315344040610340805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126369753753792054147121073 94777315315344040610340805)
                  ·
                    refine ⟨17770746621627007614438901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94777315315344040610340805 17770746621627007614438901)
                    ·
                      refine ⟨1666007495777531963853647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17770746621627007614438901 1666007495777531963853647)
                      ·
                        rfl

theorem cell23_3244538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_3244538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244538 prefixEnd_3244538 := by exact prefixLift 3244538
  have htrace : WordTrace (prefixWord ++ tailWord_3244538) baseStart_3244538 baseEnd_3244538 := by
    simpa [prefixWord, tailWord_3244538, baseEnd_3244538] using wordTrace_append hprefix tailTrace_3244538
  have hstable : (prefixWord ++ tailWord_3244538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244538).length < 2 ^ (prefixWord ++ tailWord_3244538).sum := by decide
  have hdescent : baseEnd_3244538 < baseStart_3244538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244565 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 5, 1, 4]
def baseStart_3244565 : Nat := 118140960795 + 3244565 * 2 ^ 59
def prefixEnd_3244565 : Nat := 4983230072969 + 3 ^ 40 * 3244565 * 2
def baseEnd_3244565 : Nat := 1666021359755203358216023

theorem tailTrace_3244565 : CollatzResearch.WordTrace tailWord_3244565 prefixEnd_3244565 1666021359755203358216023 := by
  unfold tailWord_3244565
  simp only [CollatzResearch.WordTrace]
  refine ⟨118339007490502607430759149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78892671660335071620506099 118339007490502607430759149)
  ·
    refine ⟨44377127808938477786534681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118339007490502607430759149 44377127808938477786534681)
    ·
      refine ⟨33282845856703858339901011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44377127808938477786534681 33282845856703858339901011)
      ·
        refine ⟨49924268785055787509851517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33282845856703858339901011 49924268785055787509851517)
        ·
          refine ⟨18721600794395920316194319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49924268785055787509851517 18721600794395920316194319)
          ·
            refine ⟨28082401191593880474291479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18721600794395920316194319 28082401191593880474291479)
            ·
              refine ⟨42123601787390820711437219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28082401191593880474291479 42123601787390820711437219)
              ·
                refine ⟨63185402681086231067155829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42123601787390820711437219 63185402681086231067155829)
                ·
                  refine ⟨5923631501351834162545859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63185402681086231067155829 5923631501351834162545859)
                  ·
                    refine ⟨8885447252027751243818789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5923631501351834162545859 8885447252027751243818789)
                    ·
                      refine ⟨1666021359755203358216023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8885447252027751243818789 1666021359755203358216023)
                      ·
                        rfl

theorem cell23_3244565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_3244565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244565 prefixEnd_3244565 := by exact prefixLift 3244565
  have htrace : WordTrace (prefixWord ++ tailWord_3244565) baseStart_3244565 baseEnd_3244565 := by
    simpa [prefixWord, tailWord_3244565, baseEnd_3244565] using wordTrace_append hprefix tailTrace_3244565
  have hstable : (prefixWord ++ tailWord_3244565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244565).length < 2 ^ (prefixWord ++ tailWord_3244565).sum := by decide
  have hdescent : baseEnd_3244565 < baseStart_3244565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244575 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 6, 4]
def baseStart_3244575 : Nat := 118140960795 + 3244575 * 2 ^ 59
def prefixEnd_3244575 : Nat := 4983230072969 + 3 ^ 40 * 3244575 * 2
def baseEnd_3244575 : Nat := 555342164853916106363659

theorem tailTrace_3244575 : CollatzResearch.WordTrace tailWord_3244575 prefixEnd_3244575 555342164853916106363659 := by
  unfold tailWord_3244575
  simp only [CollatzResearch.WordTrace]
  refine ⟨118339372220466379138623179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78892914813644252759082119 118339372220466379138623179)
  ·
    refine ⟨177509058330699568707934769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118339372220466379138623179 177509058330699568707934769)
    ·
      refine ⟨133131793748024676530951077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177509058330699568707934769 133131793748024676530951077)
      ·
        refine ⟨24962211327754626849553327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133131793748024676530951077 24962211327754626849553327)
        ·
          refine ⟨37443316991631940274329991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24962211327754626849553327 37443316991631940274329991)
          ·
            refine ⟨56164975487447910411494987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37443316991631940274329991 56164975487447910411494987)
            ·
              refine ⟨84247463231171865617242481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56164975487447910411494987 84247463231171865617242481)
              ·
                refine ⟨63185597423378899212931861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84247463231171865617242481 63185597423378899212931861)
                ·
                  refine ⟨2961824879220885900606181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63185597423378899212931861 2961824879220885900606181)
                  ·
                    refine ⟨555342164853916106363659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2961824879220885900606181 555342164853916106363659)
                    ·
                      rfl

theorem cell23_3244575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 6, 4].length) (baseStart_3244575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244575 prefixEnd_3244575 := by exact prefixLift 3244575
  have htrace : WordTrace (prefixWord ++ tailWord_3244575) baseStart_3244575 baseEnd_3244575 := by
    simpa [prefixWord, tailWord_3244575, baseEnd_3244575] using wordTrace_append hprefix tailTrace_3244575
  have hstable : (prefixWord ++ tailWord_3244575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244575).length < 2 ^ (prefixWord ++ tailWord_3244575).sum := by decide
  have hdescent : baseEnd_3244575 < baseStart_3244575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244586 : List Nat := [3, 1, 4, 1, 1, 4, 1, 1, 2, 3, 2]
def baseStart_3244586 : Nat := 118140960795 + 3244586 * 2 ^ 59
def prefixEnd_3244586 : Nat := 4983230072969 + 3 ^ 40 * 3244586 * 2
def baseEnd_3244586 : Nat := 1666032142848947776053427

theorem tailTrace_3244586 : CollatzResearch.WordTrace tailWord_3244586 prefixEnd_3244586 1666032142848947776053427 := by
  unfold tailWord_3244586
  simp only [CollatzResearch.WordTrace]
  refine ⟨29584943355856632004318403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78893182282284352011515741 29584943355856632004318403)
  ·
    refine ⟨44377415033784948006477605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29584943355856632004318403 44377415033784948006477605)
    ·
      refine ⟨8320765318834677751214551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44377415033784948006477605 8320765318834677751214551)
      ·
        refine ⟨12481147978252016626821827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8320765318834677751214551 12481147978252016626821827)
        ·
          refine ⟨18721721967378024940232741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12481147978252016626821827 18721721967378024940232741)
          ·
            refine ⟨3510322868883379676293639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18721721967378024940232741 3510322868883379676293639)
            ·
              refine ⟨5265484303325069514440459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3510322868883379676293639 5265484303325069514440459)
              ·
                refine ⟨7898226454987604271660689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5265484303325069514440459 7898226454987604271660689)
                ·
                  refine ⟨5923669841240703203745517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7898226454987604271660689 5923669841240703203745517)
                  ·
                    refine ⟨2221376190465263701404569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5923669841240703203745517 2221376190465263701404569)
                    ·
                      refine ⟨1666032142848947776053427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2221376190465263701404569 1666032142848947776053427)
                      ·
                        rfl

theorem cell23_3244586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_3244586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244586 prefixEnd_3244586 := by exact prefixLift 3244586
  have htrace : WordTrace (prefixWord ++ tailWord_3244586) baseStart_3244586 baseEnd_3244586 := by
    simpa [prefixWord, tailWord_3244586, baseEnd_3244586] using wordTrace_append hprefix tailTrace_3244586
  have hstable : (prefixWord ++ tailWord_3244586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244586).length < 2 ^ (prefixWord ++ tailWord_3244586).sum := by decide
  have hdescent : baseEnd_3244586 < baseStart_3244586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244588 : List Nat := [2, 2, 1, 1, 1, 2, 1, 13]
def baseStart_3244588 : Nat := 118140960795 + 3244588 * 2 ^ 59
def prefixEnd_3244588 : Nat := 4983230072969 + 3 ^ 40 * 3244588 * 2
def baseEnd_3244588 : Nat := 61704932215194695119571

theorem tailTrace_3244588 : CollatzResearch.WordTrace tailWord_3244588 prefixEnd_3244588 61704932215194695119571 := by
  unfold tailWord_3244588
  simp only [CollatzResearch.WordTrace]
  refine ⟨59169923184709641179423209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78893230912946188239230945 59169923184709641179423209)
  ·
    refine ⟨44377442388532230884567407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59169923184709641179423209 44377442388532230884567407)
    ·
      refine ⟨66566163582798346326851111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44377442388532230884567407 66566163582798346326851111)
      ·
        refine ⟨99849245374197519490276667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66566163582798346326851111 99849245374197519490276667)
        ·
          refine ⟨149773868061296279235415001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99849245374197519490276667 149773868061296279235415001)
          ·
            refine ⟨112330401045972209426561251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149773868061296279235415001 112330401045972209426561251)
            ·
              refine ⟨168495601568958314139841877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112330401045972209426561251 168495601568958314139841877)
              ·
                refine ⟨61704932215194695119571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 168495601568958314139841877 61704932215194695119571)
                ·
                  rfl

theorem cell23_3244588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 13].length) (baseStart_3244588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244588 prefixEnd_3244588 := by exact prefixLift 3244588
  have htrace : WordTrace (prefixWord ++ tailWord_3244588) baseStart_3244588 baseEnd_3244588 := by
    simpa [prefixWord, tailWord_3244588, baseEnd_3244588] using wordTrace_append hprefix tailTrace_3244588
  have hstable : (prefixWord ++ tailWord_3244588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244588).length < 2 ^ (prefixWord ++ tailWord_3244588).sum := by decide
  have hdescent : baseEnd_3244588 < baseStart_3244588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244595 : List Nat := [1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 4]
def baseStart_3244595 : Nat := 118140960795 + 3244595 * 2 ^ 59
def prefixEnd_3244595 : Nat := 4983230072969 + 3 ^ 40 * 3244595 * 2
def baseEnd_3244595 : Nat := 1666036764174838240840885

theorem tailTrace_3244595 : CollatzResearch.WordTrace tailWord_3244595 prefixEnd_3244595 1666036764174838240840885 := by
  unfold tailWord_3244595
  simp only [CollatzResearch.WordTrace]
  refine ⟨118340101680393922554351239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78893401120262615036234159 118340101680393922554351239)
  ·
    refine ⟨177510152520590883831526859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118340101680393922554351239 177510152520590883831526859)
    ·
      refine ⟨266265228780886325747290289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177510152520590883831526859 266265228780886325747290289)
      ·
        refine ⟨199698921585664744310467717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266265228780886325747290289 199698921585664744310467717)
        ·
          refine ⟨37443547797312139558212697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 199698921585664744310467717 37443547797312139558212697)
          ·
            refine ⟨28082660847984104668659523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37443547797312139558212697 28082660847984104668659523)
            ·
              refine ⟨42123991271976157002989285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28082660847984104668659523 42123991271976157002989285)
              ·
                refine ⟨7898248363495529438060491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42123991271976157002989285 7898248363495529438060491)
                ·
                  refine ⟨11847372545243294157090737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7898248363495529438060491 11847372545243294157090737)
                  ·
                    refine ⟨8885529408932470617818053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11847372545243294157090737 8885529408932470617818053)
                    ·
                      refine ⟨1666036764174838240840885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8885529408932470617818053 1666036764174838240840885)
                      ·
                        rfl

theorem cell23_3244595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 2, 4].length) (baseStart_3244595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244595 prefixEnd_3244595 := by exact prefixLift 3244595
  have htrace : WordTrace (prefixWord ++ tailWord_3244595) baseStart_3244595 baseEnd_3244595 := by
    simpa [prefixWord, tailWord_3244595, baseEnd_3244595] using wordTrace_append hprefix tailTrace_3244595
  have hstable : (prefixWord ++ tailWord_3244595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244595).length < 2 ^ (prefixWord ++ tailWord_3244595).sum := by decide
  have hdescent : baseEnd_3244595 < baseStart_3244595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244596 : List Nat := [2, 5, 1, 3, 1, 1, 1, 3, 1, 5]
def baseStart_3244596 : Nat := 118140960795 + 3244596 * 2 ^ 59
def prefixEnd_3244596 : Nat := 4983230072969 + 3 ^ 40 * 3244596 * 2
def baseEnd_3244596 : Nat := 555345759218497578976127

theorem tailTrace_3244596 : CollatzResearch.WordTrace tailWord_3244596 prefixEnd_3244596 555345759218497578976127 := by
  unfold tailWord_3244596
  simp only [CollatzResearch.WordTrace]
  refine ⟨59170069076695149862568821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78893425435593533150091761 59170069076695149862568821)
  ·
    refine ⟨5547193975940170299615827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59170069076695149862568821 5547193975940170299615827)
    ·
      refine ⟨8320790963910255449423741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5547193975940170299615827 8320790963910255449423741)
      ·
        refine ⟨3120296611466345793533903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8320790963910255449423741 3120296611466345793533903)
        ·
          refine ⟨4680444917199518690300855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3120296611466345793533903 4680444917199518690300855)
          ·
            refine ⟨7020667375799278035451283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4680444917199518690300855 7020667375799278035451283)
            ·
              refine ⟨10531001063698917053176925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7020667375799278035451283 10531001063698917053176925)
              ·
                refine ⟨3949125398887093894941347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10531001063698917053176925 3949125398887093894941347)
                ·
                  refine ⟨5923688098330640842412021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3949125398887093894941347 5923688098330640842412021)
                  ·
                    refine ⟨555345759218497578976127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5923688098330640842412021 555345759218497578976127)
                    ·
                      rfl

theorem cell23_3244596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_3244596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244596 prefixEnd_3244596 := by exact prefixLift 3244596
  have htrace : WordTrace (prefixWord ++ tailWord_3244596) baseStart_3244596 baseEnd_3244596 := by
    simpa [prefixWord, tailWord_3244596, baseEnd_3244596] using wordTrace_append hprefix tailTrace_3244596
  have hstable : (prefixWord ++ tailWord_3244596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244596).length < 2 ^ (prefixWord ++ tailWord_3244596).sum := by decide
  have hdescent : baseEnd_3244596 < baseStart_3244596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244605 : List Nat := [1, 4, 1, 3, 2, 2, 10]
def baseStart_3244605 : Nat := 118140960795 + 3244605 * 2 ^ 59
def prefixEnd_3244605 : Nat := 4983230072969 + 3 ^ 40 * 3244605 * 2
def baseEnd_3244605 : Nat := 20568418505943002490319

theorem tailTrace_3244605 : CollatzResearch.WordTrace tailWord_3244605 prefixEnd_3244605 20568418505943002490319 := by
  unfold tailWord_3244605
  simp only [CollatzResearch.WordTrace]
  refine ⟨118340466410357694262215269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78893644273571796174810179 118340466410357694262215269)
  ·
    refine ⟨22188837451942067674165363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118340466410357694262215269 22188837451942067674165363)
    ·
      refine ⟨33283256177913101511248045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22188837451942067674165363 33283256177913101511248045)
      ·
        refine ⟨12481221066717413066718017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33283256177913101511248045 12481221066717413066718017)
        ·
          refine ⟨9360915800038059800038513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12481221066717413066718017 9360915800038059800038513)
          ·
            refine ⟨7020686850028544850028885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9360915800038059800038513 7020686850028544850028885)
            ·
              refine ⟨20568418505943002490319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7020686850028544850028885 20568418505943002490319)
              ·
                rfl

theorem cell23_3244605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 10].length) (baseStart_3244605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244605 prefixEnd_3244605 := by exact prefixLift 3244605
  have htrace : WordTrace (prefixWord ++ tailWord_3244605) baseStart_3244605 baseEnd_3244605 := by
    simpa [prefixWord, tailWord_3244605, baseEnd_3244605] using wordTrace_append hprefix tailTrace_3244605
  have hstable : (prefixWord ++ tailWord_3244605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244605).length < 2 ^ (prefixWord ++ tailWord_3244605).sum := by decide
  have hdescent : baseEnd_3244605 < baseStart_3244605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244609 : List Nat := [1, 2, 5, 1, 1, 2, 3, 2, 2, 4]
def baseStart_3244609 : Nat := 118140960795 + 3244609 * 2 ^ 59
def prefixEnd_3244609 : Nat := 4983230072969 + 3 ^ 40 * 3244609 * 2
def baseEnd_3244609 : Nat := 555347984301333728688607

theorem tailTrace_3244609 : CollatzResearch.WordTrace tailWord_3244609 prefixEnd_3244609 555347984301333728688607 := by
  unfold tailWord_3244609
  simp only [CollatzResearch.WordTrace]
  refine ⟨118340612302343202945360881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78893741534895468630240587 118340612302343202945360881)
  ·
    refine ⟨88755459226757402209020661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118340612302343202945360881 88755459226757402209020661)
    ·
      refine ⟨8320824302508506457095687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88755459226757402209020661 8320824302508506457095687)
      ·
        refine ⟨12481236453762759685643531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8320824302508506457095687 12481236453762759685643531)
        ·
          refine ⟨18721854680644139528465297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12481236453762759685643531 18721854680644139528465297)
          ·
            refine ⟨14041391010483104646348973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18721854680644139528465297 14041391010483104646348973)
            ·
              refine ⟨5265521628931164242380865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14041391010483104646348973 5265521628931164242380865)
              ·
                refine ⟨3949141221698373181785649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5265521628931164242380865 3949141221698373181785649)
                ·
                  refine ⟨2961855916273779886339237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3949141221698373181785649 2961855916273779886339237)
                  ·
                    refine ⟨555347984301333728688607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2961855916273779886339237 555347984301333728688607)
                    ·
                      rfl

theorem cell23_3244609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_3244609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244609 prefixEnd_3244609 := by exact prefixLift 3244609
  have htrace : WordTrace (prefixWord ++ tailWord_3244609) baseStart_3244609 baseEnd_3244609 := by
    simpa [prefixWord, tailWord_3244609, baseEnd_3244609] using wordTrace_append hprefix tailTrace_3244609
  have hstable : (prefixWord ++ tailWord_3244609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244609).length < 2 ^ (prefixWord ++ tailWord_3244609).sum := by decide
  have hdescent : baseEnd_3244609 < baseStart_3244609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244632 : List Nat := [2, 1, 2, 2, 1, 2, 5, 1, 1, 3, 3]
def baseStart_3244632 : Nat := 118140960795 + 3244632 * 2 ^ 59
def prefixEnd_3244632 : Nat := 4983230072969 + 3 ^ 40 * 3244632 * 2
def baseEnd_3244632 : Nat := 1666055762959054596078215

theorem tailTrace_3244632 : CollatzResearch.WordTrace tailWord_3244632 prefixEnd_3244632 1666055762959054596078215 := by
  unfold tailWord_3244632
  simp only [CollatzResearch.WordTrace]
  refine ⟨59170725590629938936724075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78894300787506585248965433 59170725590629938936724075)
  ·
    refine ⟨88756088385944908405086113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59170725590629938936724075 88756088385944908405086113)
    ·
      refine ⟨66567066289458681303814585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88756088385944908405086113 66567066289458681303814585)
      ·
        refine ⟨49925299717094010977860939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66567066289458681303814585 49925299717094010977860939)
        ·
          refine ⟨74887949575641016466791409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49925299717094010977860939 74887949575641016466791409)
          ·
            refine ⟨56165962181730762350093557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74887949575641016466791409 56165962181730762350093557)
            ·
              refine ⟨5265558954537258970321271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56165962181730762350093557 5265558954537258970321271)
              ·
                refine ⟨7898338431805888455481907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5265558954537258970321271 7898338431805888455481907)
                ·
                  refine ⟨11847507647708832683222861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7898338431805888455481907 11847507647708832683222861)
                  ·
                    refine ⟨4442815367890812256208573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11847507647708832683222861 4442815367890812256208573)
                    ·
                      refine ⟨1666055762959054596078215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4442815367890812256208573 1666055762959054596078215)
                      ·
                        rfl

theorem cell23_3244632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_3244632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244632 prefixEnd_3244632 := by exact prefixLift 3244632
  have htrace : WordTrace (prefixWord ++ tailWord_3244632) baseStart_3244632 baseEnd_3244632 := by
    simpa [prefixWord, tailWord_3244632, baseEnd_3244632] using wordTrace_append hprefix tailTrace_3244632
  have hstable : (prefixWord ++ tailWord_3244632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244632).length < 2 ^ (prefixWord ++ tailWord_3244632).sum := by decide
  have hdescent : baseEnd_3244632 < baseStart_3244632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244636 : List Nat := [2, 2, 4, 1, 3, 1, 2, 2, 1, 2, 3]
def baseStart_3244636 : Nat := 118140960795 + 3244636 * 2 ^ 59
def prefixEnd_3244636 : Nat := 4983230072969 + 3 ^ 40 * 3244636 * 2
def baseEnd_3244636 : Nat := 1666057816881672580428197

theorem tailTrace_3244636 : CollatzResearch.WordTrace tailWord_3244636 prefixEnd_3244636 1666057816881672580428197 := by
  unfold tailWord_3244636
  simp only [CollatzResearch.WordTrace]
  refine ⟨59170798536622693278296881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78894398048830257704395841 59170798536622693278296881)
  ·
    refine ⟨44378098902467019958722661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59170798536622693278296881 44378098902467019958722661)
    ·
      refine ⟨8320893544212566242260499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44378098902467019958722661 8320893544212566242260499)
      ·
        refine ⟨12481340316318849363390749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8320893544212566242260499 12481340316318849363390749)
        ·
          refine ⟨4680502618619568511271531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12481340316318849363390749 4680502618619568511271531)
          ·
            refine ⟨7020753927929352766907297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4680502618619568511271531 7020753927929352766907297)
            ·
              refine ⟨5265565445947014575180473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7020753927929352766907297 5265565445947014575180473)
              ·
                refine ⟨3949174084460260931385355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5265565445947014575180473 3949174084460260931385355)
                ·
                  refine ⟨5923761126690391397078033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3949174084460260931385355 5923761126690391397078033)
                  ·
                    refine ⟨4442820845017793547808525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5923761126690391397078033 4442820845017793547808525)
                    ·
                      refine ⟨1666057816881672580428197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4442820845017793547808525 1666057816881672580428197)
                      ·
                        rfl

theorem cell23_3244636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_3244636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244636 prefixEnd_3244636 := by exact prefixLift 3244636
  have htrace : WordTrace (prefixWord ++ tailWord_3244636) baseStart_3244636 baseEnd_3244636 := by
    simpa [prefixWord, tailWord_3244636, baseEnd_3244636] using wordTrace_append hprefix tailTrace_3244636
  have hstable : (prefixWord ++ tailWord_3244636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244636).length < 2 ^ (prefixWord ++ tailWord_3244636).sum := by decide
  have hdescent : baseEnd_3244636 < baseStart_3244636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244695 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 9]
def baseStart_3244695 : Nat := 118140960795 + 3244695 * 2 ^ 59
def prefixEnd_3244695 : Nat := 4983230072969 + 3 ^ 40 * 3244695 * 2
def baseEnd_3244695 : Nat := 185120901360031983287825

theorem tailTrace_3244695 : CollatzResearch.WordTrace tailWord_3244695 prefixEnd_3244695 185120901360031983287825 := by
  unfold tailWord_3244695
  simp only [CollatzResearch.WordTrace]
  refine ⟨118343748980031639632991539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78895832653354426421994359 118343748980031639632991539)
  ·
    refine ⟨177515623470047459449487309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118343748980031639632991539 177515623470047459449487309)
    ·
      refine ⟨66568358801267797293557741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177515623470047459449487309 66568358801267797293557741)
      ·
        refine ⟨24963134550475423985084153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66568358801267797293557741 24963134550475423985084153)
        ·
          refine ⟨18722350912856567988813115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24963134550475423985084153 18722350912856567988813115)
          ·
            refine ⟨28083526369284851983219673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18722350912856567988813115 28083526369284851983219673)
            ·
              refine ⟨21062644776963638987414755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28083526369284851983219673 21062644776963638987414755)
              ·
                refine ⟨31593967165445458481122133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21062644776963638987414755 31593967165445458481122133)
                ·
                  refine ⟨185120901360031983287825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31593967165445458481122133 185120901360031983287825)
                  ·
                    rfl

theorem cell23_3244695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 9].length) (baseStart_3244695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244695 prefixEnd_3244695 := by exact prefixLift 3244695
  have htrace : WordTrace (prefixWord ++ tailWord_3244695) baseStart_3244695 baseEnd_3244695 := by
    simpa [prefixWord, tailWord_3244695, baseEnd_3244695] using wordTrace_append hprefix tailTrace_3244695
  have hstable : (prefixWord ++ tailWord_3244695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244695).length < 2 ^ (prefixWord ++ tailWord_3244695).sum := by decide
  have hdescent : baseEnd_3244695 < baseStart_3244695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244722 : List Nat := [3, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3]
def baseStart_3244722 : Nat := 118140960795 + 3244722 * 2 ^ 59
def prefixEnd_3244722 : Nat := 4983230072969 + 3 ^ 40 * 3244722 * 2
def baseEnd_3244722 : Nat := 1666101976217959243952801

theorem tailTrace_3244722 : CollatzResearch.WordTrace tailWord_3244722 prefixEnd_3244722 1666101976217959243952801 := by
  unfold tailWord_3244722
  simp only [CollatzResearch.WordTrace]
  refine ⟨29586183437733455811056105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78896489167289215496149613 29586183437733455811056105)
  ·
    refine ⟨22189637578300091858292079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29586183437733455811056105 22189637578300091858292079)
    ·
      refine ⟨33284456367450137787438119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22189637578300091858292079 33284456367450137787438119)
      ·
        refine ⟨49926684551175206681157179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33284456367450137787438119 49926684551175206681157179)
        ·
          refine ⟨74890026826762810021735769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49926684551175206681157179 74890026826762810021735769)
          ·
            refine ⟨56167520120072107516301827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74890026826762810021735769 56167520120072107516301827)
            ·
              refine ⟨84251280180108161274452741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56167520120072107516301827 84251280180108161274452741)
              ·
                refine ⟨15797115033770280238959889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84251280180108161274452741 15797115033770280238959889)
                ·
                  refine ⟨11847836275327710179219917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15797115033770280238959889 11847836275327710179219917)
                  ·
                    refine ⟨4442938603247891317207469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11847836275327710179219917 4442938603247891317207469)
                    ·
                      refine ⟨1666101976217959243952801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4442938603247891317207469 1666101976217959243952801)
                      ·
                        rfl

theorem cell23_3244722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_3244722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244722 prefixEnd_3244722 := by exact prefixLift 3244722
  have htrace : WordTrace (prefixWord ++ tailWord_3244722) baseStart_3244722 baseEnd_3244722 := by
    simpa [prefixWord, tailWord_3244722, baseEnd_3244722] using wordTrace_append hprefix tailTrace_3244722
  have hstable : (prefixWord ++ tailWord_3244722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244722).length < 2 ^ (prefixWord ++ tailWord_3244722).sum := by decide
  have hdescent : baseEnd_3244722 < baseStart_3244722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244759 : List Nat := [1, 1, 3, 2, 1, 6, 1, 1, 2, 5]
def baseStart_3244759 : Nat := 118140960795 + 3244759 * 2 ^ 59
def prefixEnd_3244759 : Nat := 4983230072969 + 3 ^ 40 * 3244759 * 2
def baseEnd_3244759 : Nat := 555373658334058533063377

theorem tailTrace_3244759 : CollatzResearch.WordTrace tailWord_3244759 prefixEnd_3244759 555373658334058533063377 := by
  unfold tailWord_3244759
  simp only [CollatzResearch.WordTrace]
  refine ⟨118346083251799778563321331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78897388834533185708880887 118346083251799778563321331)
  ·
    refine ⟨177519124877699667844981997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118346083251799778563321331 177519124877699667844981997)
    ·
      refine ⟨66569671829137375441868249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177519124877699667844981997 66569671829137375441868249)
      ·
        refine ⟨49927253871853031581401187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66569671829137375441868249 49927253871853031581401187)
        ·
          refine ⟨74890880807779547372101781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49927253871853031581401187 74890880807779547372101781)
          ·
            refine ⟨3510510037864666283067271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 74890880807779547372101781 3510510037864666283067271)
            ·
              refine ⟨5265765056796999424600907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3510510037864666283067271 5265765056796999424600907)
              ·
                refine ⟨7898647585195499136901361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5265765056796999424600907 7898647585195499136901361)
                ·
                  refine ⟨5923985688896624352676021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7898647585195499136901361 5923985688896624352676021)
                  ·
                    refine ⟨555373658334058533063377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5923985688896624352676021 555373658334058533063377)
                    ·
                      rfl

theorem cell23_3244759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 5].length) (baseStart_3244759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244759 prefixEnd_3244759 := by exact prefixLift 3244759
  have htrace : WordTrace (prefixWord ++ tailWord_3244759) baseStart_3244759 baseEnd_3244759 := by
    simpa [prefixWord, tailWord_3244759, baseEnd_3244759] using wordTrace_append hprefix tailTrace_3244759
  have hstable : (prefixWord ++ tailWord_3244759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244759).length < 2 ^ (prefixWord ++ tailWord_3244759).sum := by decide
  have hdescent : baseEnd_3244759 < baseStart_3244759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244762 : List Nat := [3, 1, 1, 2, 2, 2, 3, 1, 1, 3, 4]
def baseStart_3244762 : Nat := 118140960795 + 3244762 * 2 ^ 59
def prefixEnd_3244762 : Nat := 4983230072969 + 3 ^ 40 * 3244762 * 2
def baseEnd_3244762 : Nat := 1666122515444139087452617

theorem tailTrace_3244762 : CollatzResearch.WordTrace tailWord_3244762 prefixEnd_3244762 1666122515444139087452617 := by
  unfold tailWord_3244762
  simp only [CollatzResearch.WordTrace]
  refine ⟨29586548167697227518920135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78897461780525940050453693 29586548167697227518920135)
  ·
    refine ⟨44379822251545841278380203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29586548167697227518920135 44379822251545841278380203)
    ·
      refine ⟨66569733377318761917570305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44379822251545841278380203 66569733377318761917570305)
      ·
        refine ⟨49927300032989071438177729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66569733377318761917570305 49927300032989071438177729)
        ·
          refine ⟨37445475024741803578633297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49927300032989071438177729 37445475024741803578633297)
          ·
            refine ⟨28084106268556352683974973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37445475024741803578633297 28084106268556352683974973)
            ·
              refine ⟨10531539850708632256490615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28084106268556352683974973 10531539850708632256490615)
              ·
                refine ⟨15797309776062948384735923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10531539850708632256490615 15797309776062948384735923)
                ·
                  refine ⟨23695964664094422577103885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15797309776062948384735923 23695964664094422577103885)
                  ·
                    refine ⟨8885986749035408466413957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23695964664094422577103885 8885986749035408466413957)
                    ·
                      refine ⟨1666122515444139087452617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8885986749035408466413957 1666122515444139087452617)
                      ·
                        rfl

theorem cell23_3244762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_3244762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244762 prefixEnd_3244762 := by exact prefixLift 3244762
  have htrace : WordTrace (prefixWord ++ tailWord_3244762) baseStart_3244762 baseEnd_3244762 := by
    simpa [prefixWord, tailWord_3244762, baseEnd_3244762] using wordTrace_append hprefix tailTrace_3244762
  have hstable : (prefixWord ++ tailWord_3244762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244762).length < 2 ^ (prefixWord ++ tailWord_3244762).sum := by decide
  have hdescent : baseEnd_3244762 < baseStart_3244762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244795 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 9]
def baseStart_3244795 : Nat := 118140960795 + 3244795 * 2 ^ 59
def prefixEnd_3244795 : Nat := 4983230072969 + 3 ^ 40 * 3244795 * 2
def baseEnd_3244795 : Nat := 1666139460305737458339965

theorem tailTrace_3244795 : CollatzResearch.WordTrace tailWord_3244795 prefixEnd_3244795 1666139460305737458339965 := by
  unfold tailWord_3244795
  simp only [CollatzResearch.WordTrace]
  refine ⟨118347396279669356711631839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78898264186446237807754559 118347396279669356711631839)
  ·
    refine ⟨177521094419504035067447759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118347396279669356711631839 177521094419504035067447759)
    ·
      refine ⟨266281641629256052601171639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177521094419504035067447759 266281641629256052601171639)
      ·
        refine ⟨399422462443884078901757459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266281641629256052601171639 399422462443884078901757459)
        ·
          refine ⟨599133693665826118352636189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399422462443884078901757459 599133693665826118352636189)
          ·
            refine ⟨224675135124684794382238571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 599133693665826118352636189 224675135124684794382238571)
            ·
              refine ⟨337012702687027191573357857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224675135124684794382238571 337012702687027191573357857)
              ·
                refine ⟨252759527015270393680018393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337012702687027191573357857 252759527015270393680018393)
                ·
                  refine ⟨189569645261452795260013795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252759527015270393680018393 189569645261452795260013795)
                  ·
                    refine ⟨284354467892179192890020693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 189569645261452795260013795 284354467892179192890020693)
                    ·
                      refine ⟨1666139460305737458339965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 284354467892179192890020693 1666139460305737458339965)
                      ·
                        rfl

theorem cell23_3244795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 9].length) (baseStart_3244795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244795 prefixEnd_3244795 := by exact prefixLift 3244795
  have htrace : WordTrace (prefixWord ++ tailWord_3244795) baseStart_3244795 baseEnd_3244795 := by
    simpa [prefixWord, tailWord_3244795, baseEnd_3244795] using wordTrace_append hprefix tailTrace_3244795
  have hstable : (prefixWord ++ tailWord_3244795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244795).length < 2 ^ (prefixWord ++ tailWord_3244795).sum := by decide
  have hdescent : baseEnd_3244795 < baseStart_3244795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244812 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 1, 7, 3]
def baseStart_3244812 : Nat := 118140960795 + 3244812 * 2 ^ 59
def prefixEnd_3244812 : Nat := 4983230072969 + 3 ^ 40 * 3244812 * 2
def baseEnd_3244812 : Nat := 1666148189476863891827387

theorem tailTrace_3244812 : CollatzResearch.WordTrace tailWord_3244812 prefixEnd_3244812 1666148189476863891827387 := by
  unfold tailWord_3244812
  simp only [CollatzResearch.WordTrace]
  refine ⟨59174008160303884307500345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78898677547071845743333793 59174008160303884307500345)
  ·
    refine ⟨44380506120227913230625259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59174008160303884307500345 44380506120227913230625259)
    ·
      refine ⟨66570759180341869845937889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44380506120227913230625259 66570759180341869845937889)
      ·
        refine ⟨49928069385256402384453417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66570759180341869845937889 49928069385256402384453417)
        ·
          refine ⟨37446052038942301788340063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49928069385256402384453417 37446052038942301788340063)
          ·
            refine ⟨56169078058413452682510095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37446052038942301788340063 56169078058413452682510095)
            ·
              refine ⟨84253617087620179023765143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56169078058413452682510095 84253617087620179023765143)
              ·
                refine ⟨126380425631430268535647715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84253617087620179023765143 126380425631430268535647715)
                ·
                  refine ⟨189570638447145402803471573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126380425631430268535647715 189570638447145402803471573)
                  ·
                    refine ⟨4443061838604970378206365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 189570638447145402803471573 4443061838604970378206365)
                    ·
                      refine ⟨1666148189476863891827387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4443061838604970378206365 1666148189476863891827387)
                      ·
                        rfl

theorem cell23_3244812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_3244812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244812 prefixEnd_3244812 := by exact prefixLift 3244812
  have htrace : WordTrace (prefixWord ++ tailWord_3244812) baseStart_3244812 baseEnd_3244812 := by
    simpa [prefixWord, tailWord_3244812, baseEnd_3244812] using wordTrace_append hprefix tailTrace_3244812
  have hstable : (prefixWord ++ tailWord_3244812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244812).length < 2 ^ (prefixWord ++ tailWord_3244812).sum := by decide
  have hdescent : baseEnd_3244812 < baseStart_3244812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244869 : List Nat := [1, 3, 1, 1, 1, 2, 2, 6, 1, 1, 4]
def baseStart_3244869 : Nat := 118140960795 + 3244869 * 2 ^ 59
def prefixEnd_3244869 : Nat := 4983230072969 + 3 ^ 40 * 3244869 * 2
def baseEnd_3244869 : Nat := 1666177457874170168814625

theorem tailTrace_3244869 : CollatzResearch.WordTrace tailWord_3244869 prefixEnd_3244869 1666177457874170168814625 := by
  unfold tailWord_3244869
  simp only [CollatzResearch.WordTrace]
  refine ⟨118350095281401267349825661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78900063520934178233217107 118350095281401267349825661)
  ·
    refine ⟨44381285730525475256184623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118350095281401267349825661 44381285730525475256184623)
    ·
      refine ⟨66571928595788212884276935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44381285730525475256184623 66571928595788212884276935)
      ·
        refine ⟨99857892893682319326415403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66571928595788212884276935 99857892893682319326415403)
        ·
          refine ⟨149786839340523478989623105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99857892893682319326415403 149786839340523478989623105)
          ·
            refine ⟨112340129505392609242217329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149786839340523478989623105 112340129505392609242217329)
            ·
              refine ⟨84255097129044456931662997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112340129505392609242217329 84255097129044456931662997)
              ·
                refine ⟨3949457677923958918671703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84255097129044456931662997 3949457677923958918671703)
                ·
                  refine ⟨5924186516885938378007555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3949457677923958918671703 5924186516885938378007555)
                  ·
                    refine ⟨8886279775328907567011333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5924186516885938378007555 8886279775328907567011333)
                    ·
                      refine ⟨1666177457874170168814625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8886279775328907567011333 1666177457874170168814625)
                      ·
                        rfl

theorem cell23_3244869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 1, 4].length) (baseStart_3244869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244869 prefixEnd_3244869 := by exact prefixLift 3244869
  have htrace : WordTrace (prefixWord ++ tailWord_3244869) baseStart_3244869 baseEnd_3244869 := by
    simpa [prefixWord, tailWord_3244869, baseEnd_3244869] using wordTrace_append hprefix tailTrace_3244869
  have hstable : (prefixWord ++ tailWord_3244869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244869).length < 2 ^ (prefixWord ++ tailWord_3244869).sum := by decide
  have hdescent : baseEnd_3244869 < baseStart_3244869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244889 : List Nat := [1, 2, 1, 2, 2, 4, 3, 1, 1, 1, 5]
def baseStart_3244889 : Nat := 118140960795 + 3244889 * 2 ^ 59
def prefixEnd_3244889 : Nat := 4983230072969 + 3 ^ 40 * 3244889 * 2
def baseEnd_3244889 : Nat := 1666187727487260090564533

theorem tailTrace_3244889 : CollatzResearch.WordTrace tailWord_3244889 prefixEnd_3244889 1666187727487260090564533 := by
  unfold tailWord_3244889
  simp only [CollatzResearch.WordTrace]
  refine ⟨118350824741328810765553721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78900549827552540510369147 118350824741328810765553721)
  ·
    refine ⟨88763118555996608074165291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118350824741328810765553721 88763118555996608074165291)
    ·
      refine ⟨133144677833994912111247937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88763118555996608074165291 133144677833994912111247937)
      ·
        refine ⟨99858508375496184083435953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133144677833994912111247937 99858508375496184083435953)
        ·
          refine ⟨74893881281622138062576965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99858508375496184083435953 74893881281622138062576965)
          ·
            refine ⟨14042602740304150886733181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74893881281622138062576965 14042602740304150886733181)
            ·
              refine ⟨5265976027614056582524943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14042602740304150886733181 5265976027614056582524943)
              ·
                refine ⟨7898964041421084873787415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5265976027614056582524943 7898964041421084873787415)
                ·
                  refine ⟨11848446062131627310681123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7898964041421084873787415 11848446062131627310681123)
                  ·
                    refine ⟨17772669093197440966021685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11848446062131627310681123 17772669093197440966021685)
                    ·
                      refine ⟨1666187727487260090564533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17772669093197440966021685 1666187727487260090564533)
                      ·
                        rfl

theorem cell23_3244889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 1, 5].length) (baseStart_3244889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244889 prefixEnd_3244889 := by exact prefixLift 3244889
  have htrace : WordTrace (prefixWord ++ tailWord_3244889) baseStart_3244889 baseEnd_3244889 := by
    simpa [prefixWord, tailWord_3244889, baseEnd_3244889] using wordTrace_append hprefix tailTrace_3244889
  have hstable : (prefixWord ++ tailWord_3244889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244889).length < 2 ^ (prefixWord ++ tailWord_3244889).sum := by decide
  have hdescent : baseEnd_3244889 < baseStart_3244889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244896 : List Nat := [2, 1, 1, 3, 3, 1, 4, 2, 2, 4]
def baseStart_3244896 : Nat := 118140960795 + 3244896 * 2 ^ 59
def prefixEnd_3244896 : Nat := 4983230072969 + 3 ^ 40 * 3244896 * 2
def baseEnd_3244896 : Nat := 555397107283947187725667

theorem tailTrace_3244896 : CollatzResearch.WordTrace tailWord_3244896 prefixEnd_3244896 555397107283947187725667 := by
  unfold tailWord_3244896
  simp only [CollatzResearch.WordTrace]
  refine ⟨59175540026151725480529271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78900720034868967307372361 59175540026151725480529271)
  ·
    refine ⟨88763310039227588220793907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59175540026151725480529271 88763310039227588220793907)
    ·
      refine ⟨133144965058841382331190861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88763310039227588220793907 133144965058841382331190861)
      ·
        refine ⟨49929361897065518374196573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133144965058841382331190861 49929361897065518374196573)
        ·
          refine ⟨18723510711399569390323715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49929361897065518374196573 18723510711399569390323715)
          ·
            refine ⟨28085266067099354085485573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18723510711399569390323715 28085266067099354085485573)
            ·
              refine ⟨5265987387581128891028545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28085266067099354085485573 5265987387581128891028545)
              ·
                refine ⟨3949490540685846668271409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5265987387581128891028545 3949490540685846668271409)
                ·
                  refine ⟨2962117905514385001203557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3949490540685846668271409 2962117905514385001203557)
                  ·
                    refine ⟨555397107283947187725667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2962117905514385001203557 555397107283947187725667)
                    ·
                      rfl

theorem cell23_3244896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 2, 4].length) (baseStart_3244896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244896 prefixEnd_3244896 := by exact prefixLift 3244896
  have htrace : WordTrace (prefixWord ++ tailWord_3244896) baseStart_3244896 baseEnd_3244896 := by
    simpa [prefixWord, tailWord_3244896, baseEnd_3244896] using wordTrace_append hprefix tailTrace_3244896
  have hstable : (prefixWord ++ tailWord_3244896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244896).length < 2 ^ (prefixWord ++ tailWord_3244896).sum := by decide
  have hdescent : baseEnd_3244896 < baseStart_3244896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244912 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 6]
def baseStart_3244912 : Nat := 118140960795 + 3244912 * 2 ^ 59
def prefixEnd_3244912 : Nat := 4983230072969 + 3 ^ 40 * 3244912 * 2
def baseEnd_3244912 : Nat := 1666199537542313500576927

theorem tailTrace_3244912 : CollatzResearch.WordTrace tailWord_3244912 prefixEnd_3244912 1666199537542313500576927 := by
  unfold tailWord_3244912
  simp only [CollatzResearch.WordTrace]
  refine ⟨59175831810122742846820495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78901109080163657129093993 59175831810122742846820495)
  ·
    refine ⟨88763747715184114270230743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59175831810122742846820495 88763747715184114270230743)
    ·
      refine ⟨133145621572776171405346115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88763747715184114270230743 133145621572776171405346115)
      ·
        refine ⟨199718432359164257108019173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133145621572776171405346115 199718432359164257108019173)
        ·
          refine ⟨37447206067343298207753595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 199718432359164257108019173 37447206067343298207753595)
          ·
            refine ⟨56170809101014947311630393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37447206067343298207753595 56170809101014947311630393)
            ·
              refine ⟨42128106825761210483722795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56170809101014947311630393 42128106825761210483722795)
              ·
                refine ⟨63192160238641815725584193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42128106825761210483722795 63192160238641815725584193)
                ·
                  refine ⟨47394120178981361794188145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63192160238641815725584193 47394120178981361794188145)
                  ·
                    refine ⟨35545590134236021345641109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47394120178981361794188145 35545590134236021345641109)
                    ·
                      refine ⟨1666199537542313500576927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35545590134236021345641109 1666199537542313500576927)
                      ·
                        rfl

theorem cell23_3244912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 6].length) (baseStart_3244912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244912 prefixEnd_3244912 := by exact prefixLift 3244912
  have htrace : WordTrace (prefixWord ++ tailWord_3244912) baseStart_3244912 baseEnd_3244912 := by
    simpa [prefixWord, tailWord_3244912, baseEnd_3244912] using wordTrace_append hprefix tailTrace_3244912
  have hstable : (prefixWord ++ tailWord_3244912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244912).length < 2 ^ (prefixWord ++ tailWord_3244912).sum := by decide
  have hdescent : baseEnd_3244912 < baseStart_3244912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244922 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 4, 7]
def baseStart_3244922 : Nat := 118140960795 + 3244922 * 2 ^ 59
def prefixEnd_3244922 : Nat := 4983230072969 + 3 ^ 40 * 3244922 * 2
def baseEnd_3244922 : Nat := 555401557449619487150627

theorem tailTrace_3244922 : CollatzResearch.WordTrace tailWord_3244922 prefixEnd_3244922 555401557449619487150627 := by
  unfold tailWord_3244922
  simp only [CollatzResearch.WordTrace]
  refine ⟨29588007087552314350376255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78901352233472838267670013 29588007087552314350376255)
  ·
    refine ⟨44382010631328471525564383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29588007087552314350376255 44382010631328471525564383)
    ·
      refine ⟨66573015946992707288346575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44382010631328471525564383 66573015946992707288346575)
      ·
        refine ⟨99859523920489060932519863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66573015946992707288346575 99859523920489060932519863)
        ·
          refine ⟨149789285880733591398779795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99859523920489060932519863 149789285880733591398779795)
          ·
            refine ⟨224683928821100387098169693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149789285880733591398779795 224683928821100387098169693)
            ·
              refine ⟨84256473307912645161813635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224683928821100387098169693 84256473307912645161813635)
              ·
                refine ⟨126384709961868967742720453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84256473307912645161813635 126384709961868967742720453)
                ·
                  refine ⟨23697133117850431451760085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126384709961868967742720453 23697133117850431451760085)
                  ·
                    refine ⟨555401557449619487150627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23697133117850431451760085 555401557449619487150627)
                    ·
                      rfl

theorem cell23_3244922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 4, 7].length) (baseStart_3244922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244922 prefixEnd_3244922 := by exact prefixLift 3244922
  have htrace : WordTrace (prefixWord ++ tailWord_3244922) baseStart_3244922 baseEnd_3244922 := by
    simpa [prefixWord, tailWord_3244922, baseEnd_3244922] using wordTrace_append hprefix tailTrace_3244922
  have hstable : (prefixWord ++ tailWord_3244922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244922).length < 2 ^ (prefixWord ++ tailWord_3244922).sum := by decide
  have hdescent : baseEnd_3244922 < baseStart_3244922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244936 : List Nat := [2, 1, 3, 3, 2, 1, 2, 2, 1, 3, 3]
def baseStart_3244936 : Nat := 118140960795 + 3244936 * 2 ^ 59
def prefixEnd_3244936 : Nat := 4983230072969 + 3 ^ 40 * 3244936 * 2
def baseEnd_3244936 : Nat := 1666211861078021406676817

theorem tailTrace_3244936 : CollatzResearch.WordTrace tailWord_3244936 prefixEnd_3244936 1666211861078021406676817 := by
  unfold tailWord_3244936
  simp only [CollatzResearch.WordTrace]
  refine ⟨59176269486079268896257331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78901692648105691861676441 59176269486079268896257331)
  ·
    refine ⟨88764404229118903344385997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59176269486079268896257331 88764404229118903344385997)
    ·
      refine ⟨33286651585919588754144749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88764404229118903344385997 33286651585919588754144749)
      ·
        refine ⟨12482494344719845782804281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33286651585919588754144749 12482494344719845782804281)
        ·
          refine ⟨9361870758539884337103211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12482494344719845782804281 9361870758539884337103211)
          ·
            refine ⟨14042806137809826505654817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9361870758539884337103211 14042806137809826505654817)
            ·
              refine ⟨10532104603357369879241113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14042806137809826505654817 10532104603357369879241113)
              ·
                refine ⟨7899078452518027409430835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10532104603357369879241113 7899078452518027409430835)
                ·
                  refine ⟨11848617678777041114146253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7899078452518027409430835 11848617678777041114146253)
                  ·
                    refine ⟨4443231629541390417804845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11848617678777041114146253 4443231629541390417804845)
                    ·
                      refine ⟨1666211861078021406676817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4443231629541390417804845 1666211861078021406676817)
                      ·
                        rfl

theorem cell23_3244936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_3244936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3244936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3244936 prefixEnd_3244936 := by exact prefixLift 3244936
  have htrace : WordTrace (prefixWord ++ tailWord_3244936) baseStart_3244936 baseEnd_3244936 := by
    simpa [prefixWord, tailWord_3244936, baseEnd_3244936] using wordTrace_append hprefix tailTrace_3244936
  have hstable : (prefixWord ++ tailWord_3244936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244936).length < 2 ^ (prefixWord ++ tailWord_3244936).sum := by decide
  have hdescent : baseEnd_3244936 < baseStart_3244936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245010 : List Nat := [3, 2, 2, 3, 1, 1, 2, 1, 4, 2, 2]
def baseStart_3245010 : Nat := 118140960795 + 3245010 * 2 ^ 59
def prefixEnd_3245010 : Nat := 4983230072969 + 3 ^ 40 * 3245010 * 2
def baseEnd_3245010 : Nat := 1666249858646454117151477

theorem tailTrace_3245010 : CollatzResearch.WordTrace tailWord_3245010 prefixEnd_3245010 1666249858646454117151477 := by
  unfold tailWord_3245010
  simp only [CollatzResearch.WordTrace]
  refine ⟨29588809493472612107677121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78903491982593632287138989 29588809493472612107677121)
  ·
    refine ⟨22191607120104459080757841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29588809493472612107677121 22191607120104459080757841)
    ·
      refine ⟨16643705340078344310568381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22191607120104459080757841 16643705340078344310568381)
      ·
        refine ⟨6241389502529379116463143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16643705340078344310568381 6241389502529379116463143)
        ·
          refine ⟨9362084253794068674694715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6241389502529379116463143 9362084253794068674694715)
          ·
            refine ⟨14043126380691103012042073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9362084253794068674694715 14043126380691103012042073)
            ·
              refine ⟨10532344785518327259031555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14043126380691103012042073 10532344785518327259031555)
              ·
                refine ⟨15798517178277490888547333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10532344785518327259031555 15798517178277490888547333)
                ·
                  refine ⟨2962221970927029541602625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15798517178277490888547333 2962221970927029541602625)
                  ·
                    refine ⟨2221666478195272156201969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2962221970927029541602625 2221666478195272156201969)
                    ·
                      refine ⟨1666249858646454117151477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2221666478195272156201969 1666249858646454117151477)
                      ·
                        rfl

theorem cell23_3245010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_3245010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245010 prefixEnd_3245010 := by exact prefixLift 3245010
  have htrace : WordTrace (prefixWord ++ tailWord_3245010) baseStart_3245010 baseEnd_3245010 := by
    simpa [prefixWord, tailWord_3245010, baseEnd_3245010] using wordTrace_append hprefix tailTrace_3245010
  have hstable : (prefixWord ++ tailWord_3245010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245010).length < 2 ^ (prefixWord ++ tailWord_3245010).sum := by decide
  have hdescent : baseEnd_3245010 < baseStart_3245010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245016 : List Nat := [2, 1, 2, 2, 2, 5, 1, 1, 7]
def baseStart_3245016 : Nat := 118140960795 + 3245016 * 2 ^ 59
def prefixEnd_3245016 : Nat := 4983230072969 + 3 ^ 40 * 3245016 * 2
def baseEnd_3245016 : Nat := 185139215503375677075161

theorem tailTrace_3245016 : CollatzResearch.WordTrace tailWord_3245016 prefixEnd_3245016 185139215503375677075161 := by
  unfold tailWord_3245016
  simp only [CollatzResearch.WordTrace]
  refine ⟨59177728405934355727713451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78903637874579140970284601 59177728405934355727713451)
  ·
    refine ⟨88766592608901533591570177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59177728405934355727713451 88766592608901533591570177)
    ·
      refine ⟨66574944456676150193677633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88766592608901533591570177 66574944456676150193677633)
      ·
        refine ⟨49931208342507112645258225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66574944456676150193677633 49931208342507112645258225)
        ·
          refine ⟨37448406256880334483943669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49931208342507112645258225 37448406256880334483943669)
          ·
            refine ⟨3510788086582531357869719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37448406256880334483943669 3510788086582531357869719)
            ·
              refine ⟨5266182129873797036804579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3510788086582531357869719 5266182129873797036804579)
              ·
                refine ⟨7899273194810695555206869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5266182129873797036804579 7899273194810695555206869)
                ·
                  refine ⟨185139215503375677075161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7899273194810695555206869 185139215503375677075161)
                  ·
                    rfl

theorem cell23_3245016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 7].length) (baseStart_3245016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245016 prefixEnd_3245016 := by exact prefixLift 3245016
  have htrace : WordTrace (prefixWord ++ tailWord_3245016) baseStart_3245016 baseEnd_3245016 := by
    simpa [prefixWord, tailWord_3245016, baseEnd_3245016] using wordTrace_append hprefix tailTrace_3245016
  have hstable : (prefixWord ++ tailWord_3245016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245016).length < 2 ^ (prefixWord ++ tailWord_3245016).sum := by decide
  have hdescent : baseEnd_3245016 < baseStart_3245016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245129 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 2, 1, 7]
def baseStart_3245129 : Nat := 118140960795 + 3245129 * 2 ^ 59
def prefixEnd_3245129 : Nat := 4983230072969 + 3 ^ 40 * 3245129 * 2
def baseEnd_3245129 : Nat := 1666310962844339151563429

theorem tailTrace_3245129 : CollatzResearch.WordTrace tailWord_3245129 prefixEnd_3245129 1666310962844339151563429 := by
  unfold tailWord_3245129
  simp only [CollatzResearch.WordTrace]
  refine ⟨118359578260459331754290441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78906385506972887836193627 118359578260459331754290441)
  ·
    refine ⟨88769683695344498815717831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118359578260459331754290441 88769683695344498815717831)
    ·
      refine ⟨133154525543016748223576747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88769683695344498815717831 133154525543016748223576747)
      ·
        refine ⟨199731788314525122335365121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133154525543016748223576747 199731788314525122335365121)
        ·
          refine ⟨149798841235893841751523841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199731788314525122335365121 149798841235893841751523841)
          ·
            refine ⟨112349130926920381313642881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149798841235893841751523841 112349130926920381313642881)
            ·
              refine ⟨84261848195190285985232161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112349130926920381313642881 84261848195190285985232161)
              ·
                refine ⟨63196386146392714488924121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84261848195190285985232161 63196386146392714488924121)
                ·
                  refine ⟨47397289609794535866693091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63196386146392714488924121 47397289609794535866693091)
                  ·
                    refine ⟨71095934414691803800039637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47397289609794535866693091 71095934414691803800039637)
                    ·
                      refine ⟨1666310962844339151563429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 71095934414691803800039637 1666310962844339151563429)
                      ·
                        rfl

theorem cell23_3245129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 1, 7].length) (baseStart_3245129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245129 prefixEnd_3245129 := by exact prefixLift 3245129
  have htrace : WordTrace (prefixWord ++ tailWord_3245129) baseStart_3245129 baseEnd_3245129 := by
    simpa [prefixWord, tailWord_3245129, baseEnd_3245129] using wordTrace_append hprefix tailTrace_3245129
  have hstable : (prefixWord ++ tailWord_3245129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245129).length < 2 ^ (prefixWord ++ tailWord_3245129).sum := by decide
  have hdescent : baseEnd_3245129 < baseStart_3245129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245176 : List Nat := [2, 1, 2, 1, 1, 1, 5, 3, 1, 1, 5]
def baseStart_3245176 : Nat := 118140960795 + 3245176 * 2 ^ 59
def prefixEnd_3245176 : Nat := 4983230072969 + 3 ^ 40 * 3245176 * 2
def baseEnd_3245176 : Nat := 1666335096435100467675713

theorem tailTrace_3245176 : CollatzResearch.WordTrace tailWord_3245176 prefixEnd_3245176 1666335096435100467675713 := by
  unfold tailWord_3245176
  simp only [CollatzResearch.WordTrace]
  refine ⟨59180646245644529390625691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78907528327526039187500921 59180646245644529390625691)
  ·
    refine ⟨88770969368466794085938537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59180646245644529390625691 88770969368466794085938537)
    ·
      refine ⟨66578227026350095564453903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88770969368466794085938537 66578227026350095564453903)
      ·
        refine ⟨99867340539525143346680855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66578227026350095564453903 99867340539525143346680855)
        ·
          refine ⟨149801010809287715020021283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99867340539525143346680855 149801010809287715020021283)
          ·
            refine ⟨224701516213931572530031925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149801010809287715020021283 224701516213931572530031925)
            ·
              refine ⟨21065767145056084924690493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 224701516213931572530031925 21065767145056084924690493)
              ·
                refine ⟨7899662679396031846758935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21065767145056084924690493 7899662679396031846758935)
                ·
                  refine ⟨11849494019094047770138403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7899662679396031846758935 11849494019094047770138403)
                  ·
                    refine ⟨17774241028641071655207605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11849494019094047770138403 17774241028641071655207605)
                    ·
                      refine ⟨1666335096435100467675713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17774241028641071655207605 1666335096435100467675713)
                      ·
                        rfl

theorem cell23_3245176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_3245176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245176 prefixEnd_3245176 := by exact prefixLift 3245176
  have htrace : WordTrace (prefixWord ++ tailWord_3245176) baseStart_3245176 baseEnd_3245176 := by
    simpa [prefixWord, tailWord_3245176, baseEnd_3245176] using wordTrace_append hprefix tailTrace_3245176
  have hstable : (prefixWord ++ tailWord_3245176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245176).length < 2 ^ (prefixWord ++ tailWord_3245176).sum := by decide
  have hdescent : baseEnd_3245176 < baseStart_3245176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245210 : List Nat := [3, 1, 1, 5, 1, 2, 1, 1, 3, 2, 3]
def baseStart_3245210 : Nat := 118140960795 + 3245210 * 2 ^ 59
def prefixEnd_3245210 : Nat := 4983230072969 + 3 ^ 40 * 3245210 * 2
def baseEnd_3245210 : Nat := 1666352554777353334650557

theorem tailTrace_3245210 : CollatzResearch.WordTrace tailWord_3245210 prefixEnd_3245210 1666352554777353334650557 := by
  unfold tailWord_3245210
  simp only [CollatzResearch.WordTrace]
  refine ⟨29590633143291470646997271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78908355048777255058659389 29590633143291470646997271)
  ·
    refine ⟨44385949714937205970495907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29590633143291470646997271 44385949714937205970495907)
    ·
      refine ⟨66578924572405808955743861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44385949714937205970495907 66578924572405808955743861)
      ·
        refine ⟨6241774178663044589600987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66578924572405808955743861 6241774178663044589600987)
        ·
          refine ⟨9362661267994566884401481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6241774178663044589600987 9362661267994566884401481)
          ·
            refine ⟨7021995950995925163301111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9362661267994566884401481 7021995950995925163301111)
            ·
              refine ⟨10532993926493887744951667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7021995950995925163301111 10532993926493887744951667)
              ·
                refine ⟨15799490889740831617427501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10532993926493887744951667 15799490889740831617427501)
                ·
                  refine ⟨5924809083652811856535313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15799490889740831617427501 5924809083652811856535313)
                  ·
                    refine ⟨4443606812739608892401485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5924809083652811856535313 4443606812739608892401485)
                    ·
                      refine ⟨1666352554777353334650557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4443606812739608892401485 1666352554777353334650557)
                      ·
                        rfl

theorem cell23_3245210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_3245210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245210 prefixEnd_3245210 := by exact prefixLift 3245210
  have htrace : WordTrace (prefixWord ++ tailWord_3245210) baseStart_3245210 baseEnd_3245210 := by
    simpa [prefixWord, tailWord_3245210, baseEnd_3245210] using wordTrace_append hprefix tailTrace_3245210
  have hstable : (prefixWord ++ tailWord_3245210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245210).length < 2 ^ (prefixWord ++ tailWord_3245210).sum := by decide
  have hdescent : baseEnd_3245210 < baseStart_3245210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245241 : List Nat := [1, 2, 1, 4, 1, 5, 2, 2, 1, 2, 2]
def baseStart_3245241 : Nat := 118140960795 + 3245241 * 2 ^ 59
def prefixEnd_3245241 : Nat := 4983230072969 + 3 ^ 40 * 3245241 * 2
def baseEnd_3245241 : Nat := 1666368472677642713362915

theorem tailTrace_3245241 : CollatzResearch.WordTrace tailWord_3245241 prefixEnd_3245241 1666368472677642713362915 := by
  unfold tailWord_3245241
  simp only [CollatzResearch.WordTrace]
  refine ⟨118363663236053574882367577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78909108824035716588245051 118363663236053574882367577)
  ·
    refine ⟨88772747427040181161775683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118363663236053574882367577 88772747427040181161775683)
    ·
      refine ⟨133159121140560271742663525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88772747427040181161775683 133159121140560271742663525)
      ·
        refine ⟨24967335213855050951749411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133159121140560271742663525 24967335213855050951749411)
        ·
          refine ⟨37451002820782576427624117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24967335213855050951749411 37451002820782576427624117)
          ·
            refine ⟨3511031514448366540089761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37451002820782576427624117 3511031514448366540089761)
            ·
              refine ⟨2633273635836274905067321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3511031514448366540089761 2633273635836274905067321)
              ·
                refine ⟨1974955226877206178800491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2633273635836274905067321 1974955226877206178800491)
                ·
                  refine ⟨2962432840315809268200737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1974955226877206178800491 2962432840315809268200737)
                  ·
                    refine ⟨2221824630236856951150553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2962432840315809268200737 2221824630236856951150553)
                    ·
                      refine ⟨1666368472677642713362915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2221824630236856951150553 1666368472677642713362915)
                      ·
                        rfl

theorem cell23_3245241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_3245241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245241 prefixEnd_3245241 := by exact prefixLift 3245241
  have htrace : WordTrace (prefixWord ++ tailWord_3245241) baseStart_3245241 baseEnd_3245241 := by
    simpa [prefixWord, tailWord_3245241, baseEnd_3245241] using wordTrace_append hprefix tailTrace_3245241
  have hstable : (prefixWord ++ tailWord_3245241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245241).length < 2 ^ (prefixWord ++ tailWord_3245241).sum := by decide
  have hdescent : baseEnd_3245241 < baseStart_3245241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245256 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 1, 8]
def baseStart_3245256 : Nat := 118140960795 + 3245256 * 2 ^ 59
def prefixEnd_3245256 : Nat := 4983230072969 + 3 ^ 40 * 3245256 * 2
def baseEnd_3245256 : Nat := 555458724962486718225115

theorem tailTrace_3245256 : CollatzResearch.WordTrace tailWord_3245256 prefixEnd_3245256 555458724962486718225115 := by
  unfold tailWord_3245256
  simp only [CollatzResearch.WordTrace]
  refine ⟨59182105165499616222081811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78909473553999488296109081 59182105165499616222081811)
  ·
    refine ⟨88773157748249424333122717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59182105165499616222081811 88773157748249424333122717)
    ·
      refine ⟨33289934155593534124921019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88773157748249424333122717 33289934155593534124921019)
      ·
        refine ⟨49934901233390301187381529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33289934155593534124921019 49934901233390301187381529)
        ·
          refine ⟨37451175925042725890536147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49934901233390301187381529 37451175925042725890536147)
          ·
            refine ⟨56176763887564088835804221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37451175925042725890536147 56176763887564088835804221)
            ·
              refine ⟨21066286457836533313426583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56176763887564088835804221 21066286457836533313426583)
              ·
                refine ⟨31599429686754799970139875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21066286457836533313426583 31599429686754799970139875)
                ·
                  refine ⟨47399144530132199955209813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31599429686754799970139875 47399144530132199955209813)
                  ·
                    refine ⟨555458724962486718225115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47399144530132199955209813 555458724962486718225115)
                    ·
                      rfl

theorem cell23_3245256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_3245256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245256 prefixEnd_3245256 := by exact prefixLift 3245256
  have htrace : WordTrace (prefixWord ++ tailWord_3245256) baseStart_3245256 baseEnd_3245256 := by
    simpa [prefixWord, tailWord_3245256, baseEnd_3245256] using wordTrace_append hprefix tailTrace_3245256
  have hstable : (prefixWord ++ tailWord_3245256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245256).length < 2 ^ (prefixWord ++ tailWord_3245256).sum := by decide
  have hdescent : baseEnd_3245256 < baseStart_3245256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245280 : List Nat := [2, 1, 1, 3, 1, 4, 2, 2, 1, 4, 2]
def baseStart_3245280 : Nat := 118140960795 + 3245280 * 2 ^ 59
def prefixEnd_3245280 : Nat := 4983230072969 + 3 ^ 40 * 3245280 * 2
def baseEnd_3245280 : Nat := 1666388498423168060775235

theorem tailTrace_3245280 : CollatzResearch.WordTrace tailWord_3245280 prefixEnd_3245280 1666388498423168060775235 := by
  unfold tailWord_3245280
  simp only [CollatzResearch.WordTrace]
  refine ⟨59182542841456142271518647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78910057121941523028691529 59182542841456142271518647)
  ·
    refine ⟨88773814262184213407277971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59182542841456142271518647 88773814262184213407277971)
    ·
      refine ⟨133160721393276320110916957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88773814262184213407277971 133160721393276320110916957)
      ·
        refine ⟨49935270522478620041593859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133160721393276320110916957 49935270522478620041593859)
        ·
          refine ⟨74902905783717930062390789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49935270522478620041593859 74902905783717930062390789)
          ·
            refine ⟨14044294834447111886698273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74902905783717930062390789 14044294834447111886698273)
            ·
              refine ⟨10533221125835333915023705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14044294834447111886698273 10533221125835333915023705)
              ·
                refine ⟨7899915844376500436267779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10533221125835333915023705 7899915844376500436267779)
                ·
                  refine ⟨11849873766564750654401669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7899915844376500436267779 11849873766564750654401669)
                  ·
                    refine ⟨2221851331230890747700313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11849873766564750654401669 2221851331230890747700313)
                    ·
                      refine ⟨1666388498423168060775235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2221851331230890747700313 1666388498423168060775235)
                      ·
                        rfl

theorem cell23_3245280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 1, 4, 2].length) (baseStart_3245280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245280 prefixEnd_3245280 := by exact prefixLift 3245280
  have htrace : WordTrace (prefixWord ++ tailWord_3245280) baseStart_3245280 baseEnd_3245280 := by
    simpa [prefixWord, tailWord_3245280, baseEnd_3245280] using wordTrace_append hprefix tailTrace_3245280
  have hstable : (prefixWord ++ tailWord_3245280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245280).length < 2 ^ (prefixWord ++ tailWord_3245280).sum := by decide
  have hdescent : baseEnd_3245280 < baseStart_3245280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245310 : List Nat := [4, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_3245310 : Nat := 118140960795 + 3245310 * 2 ^ 59
def prefixEnd_3245310 : Nat := 4983230072969 + 3 ^ 40 * 3245310 * 2
def baseEnd_3245310 : Nat := 1666403902842802943400097

theorem tailTrace_3245310 : CollatzResearch.WordTrace tailWord_3245310 prefixEnd_3245310 1666403902842802943400097 := by
  unfold tailWord_3245310
  simp only [CollatzResearch.WordTrace]
  refine ⟨14795772484100449958328673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78910786581869066444419589 14795772484100449958328673)
  ·
    refine ⟨11096829363075337468746505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14795772484100449958328673 11096829363075337468746505)
    ·
      refine ⟨8322622022306503101559879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11096829363075337468746505 8322622022306503101559879)
      ·
        refine ⟨12483933033459754652339819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8322622022306503101559879 12483933033459754652339819)
        ·
          refine ⟨18725899550189631978509729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12483933033459754652339819 18725899550189631978509729)
          ·
            refine ⟨14044424662642223983882297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18725899550189631978509729 14044424662642223983882297)
            ·
              refine ⟨10533318496981667987911723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14044424662642223983882297 10533318496981667987911723)
              ·
                refine ⟨15799977745472501981867585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10533318496981667987911723 15799977745472501981867585)
                ·
                  refine ⟨11849983309104376486400689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15799977745472501981867585 11849983309104376486400689)
                  ·
                    refine ⟨8887487481828282364800517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11849983309104376486400689 8887487481828282364800517)
                    ·
                      refine ⟨1666403902842802943400097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8887487481828282364800517 1666403902842802943400097)
                      ·
                        rfl

theorem cell23_3245310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_3245310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245310 prefixEnd_3245310 := by exact prefixLift 3245310
  have htrace : WordTrace (prefixWord ++ tailWord_3245310) baseStart_3245310 baseEnd_3245310 := by
    simpa [prefixWord, tailWord_3245310, baseEnd_3245310] using wordTrace_append hprefix tailTrace_3245310
  have hstable : (prefixWord ++ tailWord_3245310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245310).length < 2 ^ (prefixWord ++ tailWord_3245310).sum := by decide
  have hdescent : baseEnd_3245310 < baseStart_3245310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245333 : List Nat := [1, 3, 2, 1, 2, 1, 1, 5, 2, 5]
def baseStart_3245333 : Nat := 118140960795 + 3245333 * 2 ^ 59
def prefixEnd_3245333 : Nat := 4983230072969 + 3 ^ 40 * 3245333 * 2
def baseEnd_3245333 : Nat := 555471904299285451137497

theorem tailTrace_3245333 : CollatzResearch.WordTrace tailWord_3245333 prefixEnd_3245333 555471904299285451137497 := by
  unfold tailWord_3245333
  simp only [CollatzResearch.WordTrace]
  refine ⟨118367018751720274594716653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78911345834480183063144435 118367018751720274594716653)
  ·
    refine ⟨44387632031895102973018745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118367018751720274594716653 44387632031895102973018745)
    ·
      refine ⟨33290724023921327229764059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44387632031895102973018745 33290724023921327229764059)
      ·
        refine ⟨49936086035881990844646089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33290724023921327229764059 49936086035881990844646089)
        ·
          refine ⟨37452064526911493133484567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49936086035881990844646089 37452064526911493133484567)
          ·
            refine ⟨56178096790367239700226851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37452064526911493133484567 56178096790367239700226851)
            ·
              refine ⟨84267145185550859550340277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56178096790367239700226851 84267145185550859550340277)
              ·
                refine ⟨7900044861145393082844401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84267145185550859550340277 7900044861145393082844401)
                ·
                  refine ⟨5925033645859044812133301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7900044861145393082844401 5925033645859044812133301)
                  ·
                    refine ⟨555471904299285451137497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5925033645859044812133301 555471904299285451137497)
                    ·
                      rfl

theorem cell23_3245333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_3245333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245333 prefixEnd_3245333 := by exact prefixLift 3245333
  have htrace : WordTrace (prefixWord ++ tailWord_3245333) baseStart_3245333 baseEnd_3245333 := by
    simpa [prefixWord, tailWord_3245333, baseEnd_3245333] using wordTrace_append hprefix tailTrace_3245333
  have hstable : (prefixWord ++ tailWord_3245333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245333).length < 2 ^ (prefixWord ++ tailWord_3245333).sum := by decide
  have hdescent : baseEnd_3245333 < baseStart_3245333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245354 : List Nat := [3, 1, 4, 2, 1, 2, 3, 2, 5]
def baseStart_3245354 : Nat := 118140960795 + 3245354 * 2 ^ 59
def prefixEnd_3245354 : Nat := 4983230072969 + 3 ^ 40 * 3245354 * 2
def baseEnd_3245354 : Nat := 185158499554622307916655

theorem tailTrace_3245354 : CollatzResearch.WordTrace tailWord_3245354 prefixEnd_3245354 185158499554622307916655 := by
  unfold tailWord_3245354
  simp only [CollatzResearch.WordTrace]
  refine ⟨29591946171161048795307779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78911856456429463454154077 29591946171161048795307779)
  ·
    refine ⟨44387919256741573192961669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29591946171161048795307779 44387919256741573192961669)
    ·
      refine ⟨8322734860639044973680313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44387919256741573192961669 8322734860639044973680313)
      ·
        refine ⟨6242051145479283730260235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8322734860639044973680313 6242051145479283730260235)
        ·
          refine ⟨9363076718218925595390353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6242051145479283730260235 9363076718218925595390353)
          ·
            refine ⟨7022307538664194196542765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9363076718218925595390353 7022307538664194196542765)
            ·
              refine ⟨2633365326999072823703537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7022307538664194196542765 2633365326999072823703537)
              ·
                refine ⟨1975023995249304617777653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2633365326999072823703537 1975023995249304617777653)
                ·
                  refine ⟨185158499554622307916655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1975023995249304617777653 185158499554622307916655)
                  ·
                    rfl

theorem cell23_3245354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 2, 5].length) (baseStart_3245354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245354 prefixEnd_3245354 := by exact prefixLift 3245354
  have htrace : WordTrace (prefixWord ++ tailWord_3245354) baseStart_3245354 baseEnd_3245354 := by
    simpa [prefixWord, tailWord_3245354, baseEnd_3245354] using wordTrace_append hprefix tailTrace_3245354
  have hstable : (prefixWord ++ tailWord_3245354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245354).length < 2 ^ (prefixWord ++ tailWord_3245354).sum := by decide
  have hdescent : baseEnd_3245354 < baseStart_3245354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245370 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 1, 6, 2]
def baseStart_3245370 : Nat := 118140960795 + 3245370 * 2 ^ 59
def prefixEnd_3245370 : Nat := 4983230072969 + 3 ^ 40 * 3245370 * 2
def baseEnd_3245370 : Nat := 1666434711682072708649821

theorem tailTrace_3245370 : CollatzResearch.WordTrace tailWord_3245370 prefixEnd_3245370 1666434711682072708649821 := by
  unfold tailWord_3245370
  simp only [CollatzResearch.WordTrace]
  refine ⟨29592092063146557478453391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78912245501724153275875709 29592092063146557478453391)
  ·
    refine ⟨44388138094719836217680087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29592092063146557478453391 44388138094719836217680087)
    ·
      refine ⟨66582207142079754326520131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44388138094719836217680087 66582207142079754326520131)
      ·
        refine ⟨99873310713119631489780197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66582207142079754326520131 99873310713119631489780197)
        ·
          refine ⟨18726245758709930904333787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99873310713119631489780197 18726245758709930904333787)
          ·
            refine ⟨28089368638064896356500681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18726245758709930904333787 28089368638064896356500681)
            ·
              refine ⟨21067026478548672267375511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28089368638064896356500681 21067026478548672267375511)
              ·
                refine ⟨31600539717823008401063267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21067026478548672267375511 31600539717823008401063267)
                ·
                  refine ⟨47400809576734512601594901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31600539717823008401063267 47400809576734512601594901)
                  ·
                    refine ⟨2221912948909430278199761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 47400809576734512601594901 2221912948909430278199761)
                    ·
                      refine ⟨1666434711682072708649821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2221912948909430278199761 1666434711682072708649821)
                      ·
                        rfl

theorem cell23_3245370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 1, 6, 2].length) (baseStart_3245370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245370 prefixEnd_3245370 := by exact prefixLift 3245370
  have htrace : WordTrace (prefixWord ++ tailWord_3245370) baseStart_3245370 baseEnd_3245370 := by
    simpa [prefixWord, tailWord_3245370, baseEnd_3245370] using wordTrace_append hprefix tailTrace_3245370
  have hstable : (prefixWord ++ tailWord_3245370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245370).length < 2 ^ (prefixWord ++ tailWord_3245370).sum := by decide
  have hdescent : baseEnd_3245370 < baseStart_3245370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245405 : List Nat := [1, 4, 5, 1, 2, 1, 2, 2, 5]
def baseStart_3245405 : Nat := 118140960795 + 3245405 * 2 ^ 59
def prefixEnd_3245405 : Nat := 4983230072969 + 3 ^ 40 * 3245405 * 2
def baseEnd_3245405 : Nat := 185161409278331119079129

theorem tailTrace_3245405 : CollatzResearch.WordTrace tailWord_3245405 prefixEnd_3245405 185161409278331119079129 := by
  unfold tailWord_3245405
  simp only [CollatzResearch.WordTrace]
  refine ⟨118369644807459430891337669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78913096538306287260891779 118369644807459430891337669)
  ·
    refine ⟨22194308401398643292125813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118369644807459430891337669 22194308401398643292125813)
    ·
      refine ⟨2080716412631122808636795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22194308401398643292125813 2080716412631122808636795)
      ·
        refine ⟨3121074618946684212955193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2080716412631122808636795 3121074618946684212955193)
        ·
          refine ⟨2340805964210013159716395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3121074618946684212955193 2340805964210013159716395)
          ·
            refine ⟨3511208946315019739574593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2340805964210013159716395 3511208946315019739574593)
            ·
              refine ⟨2633406709736264804680945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3511208946315019739574593 2633406709736264804680945)
              ·
                refine ⟨1975055032302198603510709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2633406709736264804680945 1975055032302198603510709)
                ·
                  refine ⟨185161409278331119079129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1975055032302198603510709 185161409278331119079129)
                  ·
                    rfl

theorem cell23_3245405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 2, 5].length) (baseStart_3245405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245405 prefixEnd_3245405 := by exact prefixLift 3245405
  have htrace : WordTrace (prefixWord ++ tailWord_3245405) baseStart_3245405 baseEnd_3245405 := by
    simpa [prefixWord, tailWord_3245405, baseEnd_3245405] using wordTrace_append hprefix tailTrace_3245405
  have hstable : (prefixWord ++ tailWord_3245405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245405).length < 2 ^ (prefixWord ++ tailWord_3245405).sum := by decide
  have hdescent : baseEnd_3245405 < baseStart_3245405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245413 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 1, 2, 6]
def baseStart_3245413 : Nat := 118140960795 + 3245413 * 2 ^ 59
def prefixEnd_3245413 : Nat := 4983230072969 + 3 ^ 40 * 3245413 * 2
def baseEnd_3245413 : Nat := 1666456791350216040412123

theorem tailTrace_3245413 : CollatzResearch.WordTrace tailWord_3245413 prefixEnd_3245413 1666456791350216040412123 := by
  unfold tailWord_3245413
  simp only [CollatzResearch.WordTrace]
  refine ⟨118369936591430448257628893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78913291060953632171752595 118369936591430448257628893)
  ·
    refine ⟨44388726221786418096610835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118369936591430448257628893 44388726221786418096610835)
    ·
      refine ⟨66583089332679627144916253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44388726221786418096610835 66583089332679627144916253)
      ·
        refine ⟨24968658499754860179343595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66583089332679627144916253 24968658499754860179343595)
        ·
          refine ⟨37452987749632290269015393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24968658499754860179343595 37452987749632290269015393)
          ·
            refine ⟨28089740812224217701761545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37452987749632290269015393 28089740812224217701761545)
            ·
              refine ⟨21067305609168163276321159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28089740812224217701761545 21067305609168163276321159)
              ·
                refine ⟨31600958413752244914481739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21067305609168163276321159 31600958413752244914481739)
                ·
                  refine ⟨47401437620628367371722609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31600958413752244914481739 47401437620628367371722609)
                  ·
                    refine ⟨35551078215471275528791957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47401437620628367371722609 35551078215471275528791957)
                    ·
                      refine ⟨1666456791350216040412123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35551078215471275528791957 1666456791350216040412123)
                      ·
                        rfl

theorem cell23_3245413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_3245413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245413 prefixEnd_3245413 := by exact prefixLift 3245413
  have htrace : WordTrace (prefixWord ++ tailWord_3245413) baseStart_3245413 baseEnd_3245413 := by
    simpa [prefixWord, tailWord_3245413, baseEnd_3245413] using wordTrace_append hprefix tailTrace_3245413
  have hstable : (prefixWord ++ tailWord_3245413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245413).length < 2 ^ (prefixWord ++ tailWord_3245413).sum := by decide
  have hdescent : baseEnd_3245413 < baseStart_3245413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245423 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 5, 5]
def baseStart_3245423 : Nat := 118140960795 + 3245423 * 2 ^ 59
def prefixEnd_3245423 : Nat := 4983230072969 + 3 ^ 40 * 3245423 * 2
def baseEnd_3245423 : Nat := 555487308718920333762359

theorem tailTrace_3245423 : CollatzResearch.WordTrace tailWord_3245423 prefixEnd_3245423 555487308718920333762359 := by
  unfold tailWord_3245423
  simp only [CollatzResearch.WordTrace]
  refine ⟨118370301321394219965492923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78913534214262813310328615 118370301321394219965492923)
  ·
    refine ⟨177555451982091329948239385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118370301321394219965492923 177555451982091329948239385)
    ·
      refine ⟨133166588986568497461179539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177555451982091329948239385 133166588986568497461179539)
      ·
        refine ⟨199749883479852746191769309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133166588986568497461179539 199749883479852746191769309)
        ·
          refine ⟨74906206304944779821913491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199749883479852746191769309 74906206304944779821913491)
          ·
            refine ⟨112359309457417169732870237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74906206304944779821913491 112359309457417169732870237)
            ·
              refine ⟨42134741046531438649826339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112359309457417169732870237 42134741046531438649826339)
              ·
                refine ⟨63202111569797157974739509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42134741046531438649826339 63202111569797157974739509)
                ·
                  refine ⟨5925197959668483560131829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63202111569797157974739509 5925197959668483560131829)
                  ·
                    refine ⟨555487308718920333762359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5925197959668483560131829 555487308718920333762359)
                    ·
                      rfl

theorem cell23_3245423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 5].length) (baseStart_3245423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245423 prefixEnd_3245423 := by exact prefixLift 3245423
  have htrace : WordTrace (prefixWord ++ tailWord_3245423) baseStart_3245423 baseEnd_3245423 := by
    simpa [prefixWord, tailWord_3245423, baseEnd_3245423] using wordTrace_append hprefix tailTrace_3245423
  have hstable : (prefixWord ++ tailWord_3245423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245423).length < 2 ^ (prefixWord ++ tailWord_3245423).sum := by decide
  have hdescent : baseEnd_3245423 < baseStart_3245423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245437 : List Nat := [1, 4, 1, 1, 2, 2, 3, 2, 3, 1, 3]
def baseStart_3245437 : Nat := 118140960795 + 3245437 * 2 ^ 59
def prefixEnd_3245437 : Nat := 4983230072969 + 3 ^ 40 * 3245437 * 2
def baseEnd_3245437 : Nat := 1666469114885923946512013

theorem tailTrace_3245437 : CollatzResearch.WordTrace tailWord_3245437 prefixEnd_3245437 1666469114885923946512013 := by
  unfold tailWord_3245437
  simp only [CollatzResearch.WordTrace]
  refine ⟨118370811943343500356502565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78913874628895666904335043 118370811943343500356502565)
  ·
    refine ⟨22194527239376906316844231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118370811943343500356502565 22194527239376906316844231)
    ·
      refine ⟨33291790859065359475266347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22194527239376906316844231 33291790859065359475266347)
      ·
        refine ⟨49937686288598039212899521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33291790859065359475266347 49937686288598039212899521)
        ·
          refine ⟨37453264716448529409674641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49937686288598039212899521 37453264716448529409674641)
          ·
            refine ⟨28089948537336397057255981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37453264716448529409674641 28089948537336397057255981)
            ·
              refine ⟨10533730701501148896470993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28089948537336397057255981 10533730701501148896470993)
              ·
                refine ⟨7900298026125861672353245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10533730701501148896470993 7900298026125861672353245)
                ·
                  refine ⟨2962611759797198127132467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7900298026125861672353245 2962611759797198127132467)
                  ·
                    refine ⟨4443917639695797190698701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2962611759797198127132467 4443917639695797190698701)
                    ·
                      refine ⟨1666469114885923946512013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4443917639695797190698701 1666469114885923946512013)
                      ·
                        rfl

theorem cell23_3245437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_3245437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245437 prefixEnd_3245437 := by exact prefixLift 3245437
  have htrace : WordTrace (prefixWord ++ tailWord_3245437) baseStart_3245437 baseEnd_3245437 := by
    simpa [prefixWord, tailWord_3245437, baseEnd_3245437] using wordTrace_append hprefix tailTrace_3245437
  have hstable : (prefixWord ++ tailWord_3245437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245437).length < 2 ^ (prefixWord ++ tailWord_3245437).sum := by decide
  have hdescent : baseEnd_3245437 < baseStart_3245437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245438 : List Nat := [4, 2, 3, 2, 2, 1, 1, 1, 2, 1, 4]
def baseStart_3245438 : Nat := 118140960795 + 3245438 * 2 ^ 59
def prefixEnd_3245438 : Nat := 4983230072969 + 3 ^ 40 * 3245438 * 2
def baseEnd_3245438 : Nat := 1666469628366578442599509

theorem tailTrace_3245438 : CollatzResearch.WordTrace tailWord_3245438 prefixEnd_3245438 1666469628366578442599509 := by
  unfold tailWord_3245438
  simp only [CollatzResearch.WordTrace]
  refine ⟨14796356052042484690911121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78913898944226585018192645 14796356052042484690911121)
  ·
    refine ⟨11097267039031863518183341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14796356052042484690911121 11097267039031863518183341)
    ·
      refine ⟨4161475139636948819318753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11097267039031863518183341 4161475139636948819318753)
      ·
        refine ⟨3121106354727711614489065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4161475139636948819318753 3121106354727711614489065)
        ·
          refine ⟨2340829766045783710866799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3121106354727711614489065 2340829766045783710866799)
          ·
            refine ⟨3511244649068675566300199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2340829766045783710866799 3511244649068675566300199)
            ·
              refine ⟨5266866973603013349450299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3511244649068675566300199 5266866973603013349450299)
              ·
                refine ⟨7900300460404520024175449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5266866973603013349450299 7900300460404520024175449)
                ·
                  refine ⟨5925225345303390018131587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7900300460404520024175449 5925225345303390018131587)
                  ·
                    refine ⟨8887838017955085027197381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5925225345303390018131587 8887838017955085027197381)
                    ·
                      refine ⟨1666469628366578442599509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8887838017955085027197381 1666469628366578442599509)
                      ·
                        rfl

theorem cell23_3245438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_3245438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245438 prefixEnd_3245438 := by exact prefixLift 3245438
  have htrace : WordTrace (prefixWord ++ tailWord_3245438) baseStart_3245438 baseEnd_3245438 := by
    simpa [prefixWord, tailWord_3245438, baseEnd_3245438] using wordTrace_append hprefix tailTrace_3245438
  have hstable : (prefixWord ++ tailWord_3245438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245438).length < 2 ^ (prefixWord ++ tailWord_3245438).sum := by decide
  have hdescent : baseEnd_3245438 < baseStart_3245438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245441 : List Nat := [1, 2, 4, 3, 3, 1, 1, 1, 2, 2, 3]
def baseStart_3245441 : Nat := 118140960795 + 3245441 * 2 ^ 59
def prefixEnd_3245441 : Nat := 4983230072969 + 3 ^ 40 * 3245441 * 2
def baseEnd_3245441 : Nat := 1666471168808541930861995

theorem tailTrace_3245441 : CollatzResearch.WordTrace tailWord_3245441 prefixEnd_3245441 1666471168808541930861995 := by
  unfold tailWord_3245441
  simp only [CollatzResearch.WordTrace]
  refine ⟨118370957835329009039648177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78913971890219339359765451 118370957835329009039648177)
  ·
    refine ⟨88778218376496756779736133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118370957835329009039648177 88778218376496756779736133)
    ·
      refine ⟨16645915945593141896200525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88778218376496756779736133 16645915945593141896200525)
      ·
        refine ⟨6242218479597428211075197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16645915945593141896200525 6242218479597428211075197)
        ·
          refine ⟨2340831929849035579153199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6242218479597428211075197 2340831929849035579153199)
          ·
            refine ⟨3511247894773553368729799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2340831929849035579153199 3511247894773553368729799)
            ·
              refine ⟨5266871842160330053094699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3511247894773553368729799 5266871842160330053094699)
              ·
                refine ⟨7900307763240495079642049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5266871842160330053094699 7900307763240495079642049)
                ·
                  refine ⟨5925230822430371309731537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7900307763240495079642049 5925230822430371309731537)
                  ·
                    refine ⟨4443923116822778482298653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5925230822430371309731537 4443923116822778482298653)
                    ·
                      refine ⟨1666471168808541930861995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4443923116822778482298653 1666471168808541930861995)
                      ·
                        rfl

theorem cell23_3245441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_3245441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245441 prefixEnd_3245441 := by exact prefixLift 3245441
  have htrace : WordTrace (prefixWord ++ tailWord_3245441) baseStart_3245441 baseEnd_3245441 := by
    simpa [prefixWord, tailWord_3245441, baseEnd_3245441] using wordTrace_append hprefix tailTrace_3245441
  have hstable : (prefixWord ++ tailWord_3245441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245441).length < 2 ^ (prefixWord ++ tailWord_3245441).sum := by decide
  have hdescent : baseEnd_3245441 < baseStart_3245441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
