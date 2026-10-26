import V185TrunkScan22Chunk060

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_548324 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 3, 6]
def baseStart_548324 : Nat := 118140960795 + 548324 * 2 ^ 59
def prefixEnd_548324 : Nat := 4983230072969 + 3 ^ 40 * 548324 * 2
def baseEnd_548324 : Nat := 187702510930678609018873

theorem tailTrace_548324 : CollatzResearch.WordTrace tailWord_548324 prefixEnd_548324 187702510930678609018873 := by
  unfold tailWord_548324
  simp only [CollatzResearch.WordTrace]
  refine ⟨9999509632761634564374013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13332679510348846085832017 9999509632761634564374013)
  ·
    refine ⟨3749816112285612961640255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9999509632761634564374013 3749816112285612961640255)
    ·
      refine ⟨5624724168428419442460383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3749816112285612961640255 5624724168428419442460383)
      ·
        refine ⟨8437086252642629163690575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5624724168428419442460383 8437086252642629163690575)
        ·
          refine ⟨12655629378963943745535863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8437086252642629163690575 12655629378963943745535863)
          ·
            refine ⟨18983444068445915618303795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12655629378963943745535863 18983444068445915618303795)
            ·
              refine ⟨28475166102668873427455693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18983444068445915618303795 28475166102668873427455693)
              ·
                refine ⟨10678187288500827535295885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28475166102668873427455693 10678187288500827535295885)
                ·
                  refine ⟨4004320233187810325735957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10678187288500827535295885 4004320233187810325735957)
                  ·
                    refine ⟨187702510930678609018873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4004320233187810325735957 187702510930678609018873)
                    ·
                      rfl

theorem cell22_548324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_548324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548324 prefixEnd_548324 := by exact prefixLift 548324
  have htrace : WordTrace (prefixWord ++ tailWord_548324) baseStart_548324 baseEnd_548324 := by
    simpa [prefixWord, tailWord_548324, baseEnd_548324] using wordTrace_append hprefix tailTrace_548324
  have hstable : (prefixWord ++ tailWord_548324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548324).length < 2 ^ (prefixWord ++ tailWord_548324).sum := by decide
  have hdescent : baseEnd_548324 < baseStart_548324 := by decide
  rcases family_descends (prefixWord ++ tailWord_548324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548330 : List Nat := [3, 1, 3, 1, 4, 2, 1, 2, 1, 4]
def baseStart_548330 : Nat := 118140960795 + 548330 * 2 ^ 59
def prefixEnd_548330 : Nat := 4983230072969 + 3 ^ 40 * 548330 * 2
def baseEnd_548330 : Nat := 187704564853296593368855

theorem tailTrace_548330 : CollatzResearch.WordTrace tailWord_548330 prefixEnd_548330 187704564853296593368855 := by
  unfold tailWord_548330
  simp only [CollatzResearch.WordTrace]
  refine ⟨4999809525875383038366611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13332825402334354768977629 4999809525875383038366611)
  ·
    refine ⟨7499714288813074557549917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4999809525875383038366611 7499714288813074557549917)
    ·
      refine ⟨2812392858304902959081219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7499714288813074557549917 2812392858304902959081219)
      ·
        refine ⟨4218589287457354438621829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2812392858304902959081219 4218589287457354438621829)
        ·
          refine ⟨790985491398253957241593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4218589287457354438621829 790985491398253957241593)
          ·
            refine ⟨593239118548690467931195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 790985491398253957241593 593239118548690467931195)
            ·
              refine ⟨889858677823035701896793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 593239118548690467931195 889858677823035701896793)
              ·
                refine ⟨667394008367276776422595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 889858677823035701896793 667394008367276776422595)
                ·
                  refine ⟨1001091012550915164633893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 667394008367276776422595 1001091012550915164633893)
                  ·
                    refine ⟨187704564853296593368855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1001091012550915164633893 187704564853296593368855)
                    ·
                      rfl

theorem cell22_548330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_548330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548330 prefixEnd_548330 := by exact prefixLift 548330
  have htrace : WordTrace (prefixWord ++ tailWord_548330) baseStart_548330 baseEnd_548330 := by
    simpa [prefixWord, tailWord_548330, baseEnd_548330] using wordTrace_append hprefix tailTrace_548330
  have hstable : (prefixWord ++ tailWord_548330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548330).length < 2 ^ (prefixWord ++ tailWord_548330).sum := by decide
  have hdescent : baseEnd_548330 < baseStart_548330 := by decide
  rcases family_descends (prefixWord ++ tailWord_548330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548356 : List Nat := [2, 3, 2, 3, 2, 10]
def baseStart_548356 : Nat := 118140960795 + 548356 * 2 ^ 59
def prefixEnd_548356 : Nat := 4983230072969 + 3 ^ 40 * 548356 * 2
def baseEnd_548356 : Nat := 2317450187464706076775

theorem tailTrace_548356 : CollatzResearch.WordTrace tailWord_548356 prefixEnd_548356 2317450187464706076775 := by
  unfold tailWord_548356
  simp only [CollatzResearch.WordTrace]
  refine ⟨10000093200703669296956461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13333457600938225729275281 10000093200703669296956461)
  ·
    refine ⟨3750034950263875986358673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10000093200703669296956461 3750034950263875986358673)
    ·
      refine ⟨2812526212697906989769005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3750034950263875986358673 2812526212697906989769005)
      ·
        refine ⟨1054697329761715121163377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2812526212697906989769005 1054697329761715121163377)
        ·
          refine ⟨791022997321286340872533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1054697329761715121163377 791022997321286340872533)
          ·
            refine ⟨2317450187464706076775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 791022997321286340872533 2317450187464706076775)
            ·
              rfl

theorem cell22_548356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 10].length) (baseStart_548356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548356 prefixEnd_548356 := by exact prefixLift 548356
  have htrace : WordTrace (prefixWord ++ tailWord_548356) baseStart_548356 baseEnd_548356 := by
    simpa [prefixWord, tailWord_548356, baseEnd_548356] using wordTrace_append hprefix tailTrace_548356
  have hstable : (prefixWord ++ tailWord_548356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548356).length < 2 ^ (prefixWord ++ tailWord_548356).sum := by decide
  have hdescent : baseEnd_548356 < baseStart_548356 := by decide
  rcases family_descends (prefixWord ++ tailWord_548356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548369 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 1, 8]
def baseStart_548369 : Nat := 118140960795 + 548369 * 2 ^ 59
def prefixEnd_548369 : Nat := 4983230072969 + 3 ^ 40 * 548369 * 2
def baseEnd_548369 : Nat := 187717915350313491643735

theorem tailTrace_548369 : CollatzResearch.WordTrace tailWord_548369 prefixEnd_548369 187717915350313491643735 := by
  unfold tailWord_548369
  simp only [CollatzResearch.WordTrace]
  refine ⟨20000660550360241814136161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13333773700240161209424107 20000660550360241814136161)
  ·
    refine ⟨15000495412770181360602121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20000660550360241814136161 15000495412770181360602121)
    ·
      refine ⟨11250371559577636020451591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15000495412770181360602121 11250371559577636020451591)
      ·
        refine ⟨16875557339366454030677387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11250371559577636020451591 16875557339366454030677387)
        ·
          refine ⟨25313336009049681046016081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16875557339366454030677387 25313336009049681046016081)
          ·
            refine ⟨18985002006787260784512061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25313336009049681046016081 18985002006787260784512061)
            ·
              refine ⟨7119375752545222794192023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18985002006787260784512061 7119375752545222794192023)
              ·
                refine ⟨10679063628817834191288035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7119375752545222794192023 10679063628817834191288035)
                ·
                  refine ⟨16018595443226751286932053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10679063628817834191288035 16018595443226751286932053)
                  ·
                    refine ⟨187717915350313491643735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 16018595443226751286932053 187717915350313491643735)
                    ·
                      rfl

theorem cell22_548369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_548369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548369 prefixEnd_548369 := by exact prefixLift 548369
  have htrace : WordTrace (prefixWord ++ tailWord_548369) baseStart_548369 baseEnd_548369 := by
    simpa [prefixWord, tailWord_548369, baseEnd_548369] using wordTrace_append hprefix tailTrace_548369
  have hstable : (prefixWord ++ tailWord_548369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548369).length < 2 ^ (prefixWord ++ tailWord_548369).sum := by decide
  have hdescent : baseEnd_548369 < baseStart_548369 := by decide
  rcases family_descends (prefixWord ++ tailWord_548369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548392 : List Nat := [2, 1, 5, 2, 3, 1, 1, 1, 2, 4]
def baseStart_548392 : Nat := 118140960795 + 548392 * 2 ^ 59
def prefixEnd_548392 : Nat := 4983230072969 + 3 ^ 40 * 548392 * 2
def baseEnd_548392 : Nat := 187725788720349098318665

theorem tailTrace_548392 : CollatzResearch.WordTrace tailWord_548392 prefixEnd_548392 187725788720349098318665 := by
  unfold tailWord_548392
  simp only [CollatzResearch.WordTrace]
  refine ⟨10000749714638458371111715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13334332952851277828148953 10000749714638458371111715)
  ·
    refine ⟨15001124571957687556667573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10000749714638458371111715 15001124571957687556667573)
    ·
      refine ⟨1406355428621033208437585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15001124571957687556667573 1406355428621033208437585)
      ·
        refine ⟨1054766571465774906328189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1406355428621033208437585 1054766571465774906328189)
        ·
          refine ⟨395537464299665589873071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1054766571465774906328189 395537464299665589873071)
          ·
            refine ⟨593306196449498384809607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395537464299665589873071 593306196449498384809607)
            ·
              refine ⟨889959294674247577214411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 593306196449498384809607 889959294674247577214411)
              ·
                refine ⟨1334938942011371365821617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 889959294674247577214411 1334938942011371365821617)
                ·
                  refine ⟨1001204206508528524366213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1334938942011371365821617 1001204206508528524366213)
                  ·
                    refine ⟨187725788720349098318665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1001204206508528524366213 187725788720349098318665)
                    ·
                      rfl

theorem cell22_548392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_548392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548392 prefixEnd_548392 := by exact prefixLift 548392
  have htrace : WordTrace (prefixWord ++ tailWord_548392) baseStart_548392 baseEnd_548392 := by
    simpa [prefixWord, tailWord_548392, baseEnd_548392] using wordTrace_append hprefix tailTrace_548392
  have hstable : (prefixWord ++ tailWord_548392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548392).length < 2 ^ (prefixWord ++ tailWord_548392).sum := by decide
  have hdescent : baseEnd_548392 < baseStart_548392 := by decide
  rcases family_descends (prefixWord ++ tailWord_548392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548405 : List Nat := [1, 3, 3, 1, 1, 3, 1, 5, 1, 3]
def baseStart_548405 : Nat := 118140960795 + 548405 * 2 ^ 59
def prefixEnd_548405 : Nat := 4983230072969 + 3 ^ 40 * 548405 * 2
def baseEnd_548405 : Nat := 187730238886021397743625

theorem tailTrace_548405 : CollatzResearch.WordTrace tailWord_548405 prefixEnd_548405 187730238886021397743625 := by
  unfold tailWord_548405
  simp only [CollatzResearch.WordTrace]
  refine ⟨20001973578229819962446669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13334649052153213308297779 20001973578229819962446669)
  ·
    refine ⟨7500740091836182485917501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20001973578229819962446669 7500740091836182485917501)
    ·
      refine ⟨2812777534438568432219063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7500740091836182485917501 2812777534438568432219063)
      ·
        refine ⟨4219166301657852648328595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2812777534438568432219063 4219166301657852648328595)
        ·
          refine ⟨6328749452486778972492893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4219166301657852648328595 6328749452486778972492893)
          ·
            refine ⟨2373281044682542114684835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6328749452486778972492893 2373281044682542114684835)
            ·
              refine ⟨3559921567023813172027253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2373281044682542114684835 3559921567023813172027253)
              ·
                refine ⟨333742646908482484877555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3559921567023813172027253 333742646908482484877555)
                ·
                  refine ⟨500613970362723727316333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 333742646908482484877555 500613970362723727316333)
                  ·
                    refine ⟨187730238886021397743625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 500613970362723727316333 187730238886021397743625)
                    ·
                      rfl

theorem cell22_548405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_548405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548405 prefixEnd_548405 := by exact prefixLift 548405
  have htrace : WordTrace (prefixWord ++ tailWord_548405) baseStart_548405 baseEnd_548405 := by
    simpa [prefixWord, tailWord_548405, baseEnd_548405] using wordTrace_append hprefix tailTrace_548405
  have hstable : (prefixWord ++ tailWord_548405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548405).length < 2 ^ (prefixWord ++ tailWord_548405).sum := by decide
  have hdescent : baseEnd_548405 < baseStart_548405 := by decide
  rcases family_descends (prefixWord ++ tailWord_548405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548480 : List Nat := [2, 1, 1, 2, 1, 4, 5, 2, 4]
def baseStart_548480 : Nat := 118140960795 + 548480 * 2 ^ 59
def prefixEnd_548480 : Nat := 4983230072969 + 3 ^ 40 * 548480 * 2
def baseEnd_548480 : Nat := 62585304306248734039465

theorem tailTrace_548480 : CollatzResearch.WordTrace tailWord_548480 prefixEnd_548480 62585304306248734039465 := by
  unfold tailWord_548480
  simp only [CollatzResearch.WordTrace]
  refine ⟨10002354526479053885713447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13336472701972071847617929 10002354526479053885713447)
  ·
    refine ⟨15003531789718580828570171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10002354526479053885713447 15003531789718580828570171)
    ·
      refine ⟨22505297684577871242855257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15003531789718580828570171 22505297684577871242855257)
      ·
        refine ⟨16878973263433403432141443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22505297684577871242855257 16878973263433403432141443)
        ·
          refine ⟨25318459895150105148212165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16878973263433403432141443 25318459895150105148212165)
          ·
            refine ⟨4747211230340644715289781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25318459895150105148212165 4747211230340644715289781)
            ·
              refine ⟨445051052844435442058417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4747211230340644715289781 445051052844435442058417)
              ·
                refine ⟨333788289633326581543813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 445051052844435442058417 333788289633326581543813)
                ·
                  refine ⟨62585304306248734039465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 333788289633326581543813 62585304306248734039465)
                  ·
                    rfl

theorem cell22_548480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 2, 4].length) (baseStart_548480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548480 prefixEnd_548480 := by exact prefixLift 548480
  have htrace : WordTrace (prefixWord ++ tailWord_548480) baseStart_548480 baseEnd_548480 := by
    simpa [prefixWord, tailWord_548480, baseEnd_548480] using wordTrace_append hprefix tailTrace_548480
  have hstable : (prefixWord ++ tailWord_548480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548480).length < 2 ^ (prefixWord ++ tailWord_548480).sum := by decide
  have hdescent : baseEnd_548480 < baseStart_548480 := by decide
  rcases family_descends (prefixWord ++ tailWord_548480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548491 : List Nat := [1, 1, 1, 1, 4, 1, 6, 7]
def baseStart_548491 : Nat := 118140960795 + 548491 * 2 ^ 59
def prefixEnd_548491 : Nat := 4983230072969 + 3 ^ 40 * 548491 * 2
def baseEnd_548491 : Nat := 20862186493727315565929

theorem tailTrace_548491 : CollatzResearch.WordTrace tailWord_548491 prefixEnd_548491 20862186493727315565929 := by
  unfold tailWord_548491
  simp only [CollatzResearch.WordTrace]
  refine ⟨20005110255918256650077327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13336740170612171100051551 20005110255918256650077327)
  ·
    refine ⟨30007665383877384975115991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20005110255918256650077327 30007665383877384975115991)
    ·
      refine ⟨45011498075816077462673987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30007665383877384975115991 45011498075816077462673987)
      ·
        refine ⟨67517247113724116194010981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45011498075816077462673987 67517247113724116194010981)
        ·
          refine ⟨12659483833823271786377059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67517247113724116194010981 12659483833823271786377059)
          ·
            refine ⟨18989225750734907679565589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12659483833823271786377059 18989225750734907679565589)
            ·
              refine ⟨890119957065698797479637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18989225750734907679565589 890119957065698797479637)
              ·
                refine ⟨20862186493727315565929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 890119957065698797479637 20862186493727315565929)
                ·
                  rfl

theorem cell22_548491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 7].length) (baseStart_548491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548491 prefixEnd_548491 := by exact prefixLift 548491
  have htrace : WordTrace (prefixWord ++ tailWord_548491) baseStart_548491 baseEnd_548491 := by
    simpa [prefixWord, tailWord_548491, baseEnd_548491] using wordTrace_append hprefix tailTrace_548491
  have hstable : (prefixWord ++ tailWord_548491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548491).length < 2 ^ (prefixWord ++ tailWord_548491).sum := by decide
  have hdescent : baseEnd_548491 < baseStart_548491 := by decide
  rcases family_descends (prefixWord ++ tailWord_548491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548510 : List Nat := [4, 3, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_548510 : Nat := 118140960795 + 548510 * 2 ^ 59
def prefixEnd_548510 : Nat := 4983230072969 + 3 ^ 40 * 548510 * 2
def baseEnd_548510 : Nat := 187766182531836123868303

theorem tailTrace_548510 : CollatzResearch.WordTrace tailWord_548510 prefixEnd_548510 187766182531836123868303 := by
  unfold tailWord_548510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2500725405356177861877373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13337202161899615263345989 2500725405356177861877373)
  ·
    refine ⟨937772027008566698204015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2500725405356177861877373 937772027008566698204015)
    ·
      refine ⟨1406658040512850047306023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 937772027008566698204015 1406658040512850047306023)
      ·
        refine ⟨2109987060769275070959035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1406658040512850047306023 2109987060769275070959035)
        ·
          refine ⟨3164980591153912606438553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2109987060769275070959035 3164980591153912606438553)
          ·
            refine ⟨2373735443365434454828915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3164980591153912606438553 2373735443365434454828915)
            ·
              refine ⟨3560603165048151682243373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2373735443365434454828915 3560603165048151682243373)
              ·
                refine ⟨1335226186893056880841265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3560603165048151682243373 1335226186893056880841265)
                ·
                  refine ⟨1001419640169792660630949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1335226186893056880841265 1001419640169792660630949)
                  ·
                    refine ⟨187766182531836123868303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1001419640169792660630949 187766182531836123868303)
                    ·
                      rfl

theorem cell22_548510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_548510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548510 prefixEnd_548510 := by exact prefixLift 548510
  have htrace : WordTrace (prefixWord ++ tailWord_548510) baseStart_548510 baseEnd_548510 := by
    simpa [prefixWord, tailWord_548510, baseEnd_548510] using wordTrace_append hprefix tailTrace_548510
  have hstable : (prefixWord ++ tailWord_548510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548510).length < 2 ^ (prefixWord ++ tailWord_548510).sum := by decide
  have hdescent : baseEnd_548510 < baseStart_548510 := by decide
  rcases family_descends (prefixWord ++ tailWord_548510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548536 : List Nat := [2, 1, 2, 1, 2, 1, 1, 5, 7]
def baseStart_548536 : Nat := 118140960795 + 548536 * 2 ^ 59
def prefixEnd_548536 : Nat := 4983230072969 + 3 ^ 40 * 548536 * 2
def baseEnd_548536 : Nat := 62591694287726907572741

theorem tailTrace_548536 : CollatzResearch.WordTrace tailWord_548536 prefixEnd_548536 62591694287726907572741 := by
  unfold tailWord_548536
  simp only [CollatzResearch.WordTrace]
  refine ⟨10003375770377614667732731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13337834360503486223643641 10003375770377614667732731)
  ·
    refine ⟨15005063655566422001599097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10003375770377614667732731 15005063655566422001599097)
    ·
      refine ⟨11253797741674816501199323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15005063655566422001599097 11253797741674816501199323)
      ·
        refine ⟨16880696612512224751798985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11253797741674816501199323 16880696612512224751798985)
        ·
          refine ⟨12660522459384168563849239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16880696612512224751798985 12660522459384168563849239)
          ·
            refine ⟨18990783689076252845773859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12660522459384168563849239 18990783689076252845773859)
            ·
              refine ⟨28486175533614379268660789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18990783689076252845773859 28486175533614379268660789)
              ·
                refine ⟨2670578956276348056436949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28486175533614379268660789 2670578956276348056436949)
                ·
                  refine ⟨62591694287726907572741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2670578956276348056436949 62591694287726907572741)
                  ·
                    rfl

theorem cell22_548536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 7].length) (baseStart_548536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548536 prefixEnd_548536 := by exact prefixLift 548536
  have htrace : WordTrace (prefixWord ++ tailWord_548536) baseStart_548536 baseEnd_548536 := by
    simpa [prefixWord, tailWord_548536, baseEnd_548536] using wordTrace_append hprefix tailTrace_548536
  have hstable : (prefixWord ++ tailWord_548536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548536).length < 2 ^ (prefixWord ++ tailWord_548536).sum := by decide
  have hdescent : baseEnd_548536 < baseStart_548536 := by decide
  rcases family_descends (prefixWord ++ tailWord_548536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548557 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 5, 3]
def baseStart_548557 : Nat := 118140960795 + 548557 * 2 ^ 59
def prefixEnd_548557 : Nat := 4983230072969 + 3 ^ 40 * 548557 * 2
def baseEnd_548557 : Nat := 187782271592343667943159

theorem tailTrace_548557 : CollatzResearch.WordTrace tailWord_548557 prefixEnd_548557 187782271592343667943159 := by
  unfold tailWord_548557
  simp only [CollatzResearch.WordTrace]
  refine ⟨20007517473679149921979925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13338344982452766614653283 20007517473679149921979925)
  ·
    refine ⟨937852381578710152592809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20007517473679149921979925 937852381578710152592809)
    ·
      refine ⟨703389286184032614444607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 937852381578710152592809 703389286184032614444607)
      ·
        refine ⟨1055083929276048921666911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 703389286184032614444607 1055083929276048921666911)
        ·
          refine ⟨1582625893914073382500367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1055083929276048921666911 1582625893914073382500367)
          ·
            refine ⟨2373938840871110073750551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1582625893914073382500367 2373938840871110073750551)
            ·
              refine ⟨3560908261306665110625827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2373938840871110073750551 3560908261306665110625827)
              ·
                refine ⟨5341362391959997665938741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3560908261306665110625827 5341362391959997665938741)
                ·
                  refine ⟨500752724246249781181757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5341362391959997665938741 500752724246249781181757)
                  ·
                    refine ⟨187782271592343667943159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 500752724246249781181757 187782271592343667943159)
                    ·
                      rfl

theorem cell22_548557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_548557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548557 prefixEnd_548557 := by exact prefixLift 548557
  have htrace : WordTrace (prefixWord ++ tailWord_548557) baseStart_548557 baseEnd_548557 := by
    simpa [prefixWord, tailWord_548557, baseEnd_548557] using wordTrace_append hprefix tailTrace_548557
  have hstable : (prefixWord ++ tailWord_548557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548557).length < 2 ^ (prefixWord ++ tailWord_548557).sum := by decide
  have hdescent : baseEnd_548557 < baseStart_548557 := by decide
  rcases family_descends (prefixWord ++ tailWord_548557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548645 : List Nat := [1, 3, 1, 2, 3, 3, 1, 2, 2, 4]
def baseStart_548645 : Nat := 118140960795 + 548645 * 2 ^ 59
def prefixEnd_548645 : Nat := 4983230072969 + 3 ^ 40 * 548645 * 2
def baseEnd_548645 : Nat := 187812395790740771742889

theorem tailTrace_548645 : CollatzResearch.WordTrace tailWord_548645 prefixEnd_548645 187812395790740771742889 := by
  unfold tailWord_548645
  simp only [CollatzResearch.WordTrace]
  refine ⟨20010727097360340951183389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13340484731573560634122259 20010727097360340951183389)
  ·
    refine ⟨7504022661510127856693771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20010727097360340951183389 7504022661510127856693771)
    ·
      refine ⟨11256033992265191785040657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7504022661510127856693771 11256033992265191785040657)
      ·
        refine ⟨8442025494198893838780493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11256033992265191785040657 8442025494198893838780493)
        ·
          refine ⟨3165759560324585189542685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8442025494198893838780493 3165759560324585189542685)
          ·
            refine ⟨1187159835121719446078507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3165759560324585189542685 1187159835121719446078507)
            ·
              refine ⟨1780739752682579169117761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1187159835121719446078507 1780739752682579169117761)
              ·
                refine ⟨1335554814511934376838321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1780739752682579169117761 1335554814511934376838321)
                ·
                  refine ⟨1001666110883950782628741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1335554814511934376838321 1001666110883950782628741)
                  ·
                    refine ⟨187812395790740771742889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1001666110883950782628741 187812395790740771742889)
                    ·
                      rfl

theorem cell22_548645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_548645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548645 prefixEnd_548645 := by exact prefixLift 548645
  have htrace : WordTrace (prefixWord ++ tailWord_548645) baseStart_548645 baseEnd_548645 := by
    simpa [prefixWord, tailWord_548645, baseEnd_548645] using wordTrace_append hprefix tailTrace_548645
  have hstable : (prefixWord ++ tailWord_548645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548645).length < 2 ^ (prefixWord ++ tailWord_548645).sum := by decide
  have hdescent : baseEnd_548645 < baseStart_548645 := by decide
  rcases family_descends (prefixWord ++ tailWord_548645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548660 : List Nat := [2, 5, 1, 1, 2, 1, 1, 9]
def baseStart_548660 : Nat := 118140960795 + 548660 * 2 ^ 59
def prefixEnd_548660 : Nat := 4983230072969 + 3 ^ 40 * 548660 * 2
def baseEnd_548660 : Nat := 20868614510809525846427

theorem tailTrace_548660 : CollatzResearch.WordTrace tailWord_548660 prefixEnd_548660 20868614510809525846427 := by
  unfold tailWord_548660
  simp only [CollatzResearch.WordTrace]
  refine ⟨10005637096152999256489717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13340849461537332341986289 10005637096152999256489717)
  ·
    refine ⟨938028477764343680295911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10005637096152999256489717 938028477764343680295911)
    ·
      refine ⟨1407042716646515520443867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 938028477764343680295911 1407042716646515520443867)
      ·
        refine ⟨2110564074969773280665801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1407042716646515520443867 2110564074969773280665801)
        ·
          refine ⟨1582923056227329960499351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2110564074969773280665801 1582923056227329960499351)
          ·
            refine ⟨2374384584340994940749027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1582923056227329960499351 2374384584340994940749027)
            ·
              refine ⟨3561576876511492411123541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2374384584340994940749027 3561576876511492411123541)
              ·
                refine ⟨20868614510809525846427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3561576876511492411123541 20868614510809525846427)
                ·
                  rfl

theorem cell22_548660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 9].length) (baseStart_548660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548660 prefixEnd_548660 := by exact prefixLift 548660
  have htrace : WordTrace (prefixWord ++ tailWord_548660) baseStart_548660 baseEnd_548660 := by
    simpa [prefixWord, tailWord_548660, baseEnd_548660] using wordTrace_append hprefix tailTrace_548660
  have hstable : (prefixWord ++ tailWord_548660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548660).length < 2 ^ (prefixWord ++ tailWord_548660).sum := by decide
  have hdescent : baseEnd_548660 < baseStart_548660 := by decide
  rcases family_descends (prefixWord ++ tailWord_548660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548664 : List Nat := [2, 1, 2, 1, 3, 5, 2, 1, 2, 3]
def baseStart_548664 : Nat := 118140960795 + 548664 * 2 ^ 59
def prefixEnd_548664 : Nat := 4983230072969 + 3 ^ 40 * 548664 * 2
def baseEnd_548664 : Nat := 187818899879031055517831

theorem tailTrace_548664 : CollatzResearch.WordTrace tailWord_548664 prefixEnd_548664 187818899879031055517831 := by
  unfold tailWord_548664
  simp only [CollatzResearch.WordTrace]
  refine ⟨10005710042145753598062523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13340946722861004797416697 10005710042145753598062523)
  ·
    refine ⟨15008565063218630397093785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10005710042145753598062523 15008565063218630397093785)
    ·
      refine ⟨11256423797413972797820339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15008565063218630397093785 11256423797413972797820339)
      ·
        refine ⟨16884635696120959196730509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11256423797413972797820339 16884635696120959196730509)
        ·
          refine ⟨6331738386045359698773941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16884635696120959196730509 6331738386045359698773941)
          ·
            refine ⟨593600473691752471760057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6331738386045359698773941 593600473691752471760057)
            ·
              refine ⟨445200355268814353820043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 593600473691752471760057 445200355268814353820043)
              ·
                refine ⟨667800532903221530730065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 445200355268814353820043 667800532903221530730065)
                ·
                  refine ⟨500850399677416148047549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 667800532903221530730065 500850399677416148047549)
                  ·
                    refine ⟨187818899879031055517831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 500850399677416148047549 187818899879031055517831)
                    ·
                      rfl

theorem cell22_548664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 2, 3].length) (baseStart_548664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548664 prefixEnd_548664 := by exact prefixLift 548664
  have htrace : WordTrace (prefixWord ++ tailWord_548664) baseStart_548664 baseEnd_548664 := by
    simpa [prefixWord, tailWord_548664, baseEnd_548664] using wordTrace_append hprefix tailTrace_548664
  have hstable : (prefixWord ++ tailWord_548664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548664).length < 2 ^ (prefixWord ++ tailWord_548664).sum := by decide
  have hdescent : baseEnd_548664 < baseStart_548664 := by decide
  rcases family_descends (prefixWord ++ tailWord_548664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548705 : List Nat := [1, 2, 3, 1, 1, 1, 6, 2, 5]
def baseStart_548705 : Nat := 118140960795 + 548705 * 2 ^ 59
def prefixEnd_548705 : Nat := 4983230072969 + 3 ^ 40 * 548705 * 2
def baseEnd_548705 : Nat := 62610978338973538414235

theorem tailTrace_548705 : CollatzResearch.WordTrace tailWord_548705 prefixEnd_548705 62610978338973538414235 := by
  unfold tailWord_548705
  simp only [CollatzResearch.WordTrace]
  refine ⟨20012915477142971198367569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13341943651428647465578379 20012915477142971198367569)
  ·
    refine ⟨15009686607857228398775677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20012915477142971198367569 15009686607857228398775677)
    ·
      refine ⟨5628632477946460649540879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15009686607857228398775677 5628632477946460649540879)
      ·
        refine ⟨8442948716919690974311319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5628632477946460649540879 8442948716919690974311319)
        ·
          refine ⟨12664423075379536461466979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8442948716919690974311319 12664423075379536461466979)
          ·
            refine ⟨18996634613069304692200469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12664423075379536461466979 18996634613069304692200469)
            ·
              refine ⟨890467247487623657446897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18996634613069304692200469 890467247487623657446897)
              ·
                refine ⟨667850435615717743085173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 890467247487623657446897 667850435615717743085173)
                ·
                  refine ⟨62610978338973538414235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 667850435615717743085173 62610978338973538414235)
                  ·
                    rfl

theorem cell22_548705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 5].length) (baseStart_548705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548705 prefixEnd_548705 := by exact prefixLift 548705
  have htrace : WordTrace (prefixWord ++ tailWord_548705) baseStart_548705 baseEnd_548705 := by
    simpa [prefixWord, tailWord_548705, baseEnd_548705] using wordTrace_append hprefix tailTrace_548705
  have hstable : (prefixWord ++ tailWord_548705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548705).length < 2 ^ (prefixWord ++ tailWord_548705).sum := by decide
  have hdescent : baseEnd_548705 < baseStart_548705 := by decide
  rcases family_descends (prefixWord ++ tailWord_548705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548735 : List Nat := [1, 1, 2, 2, 1, 1, 3, 6, 1, 4]
def baseStart_548735 : Nat := 118140960795 + 548735 * 2 ^ 59
def prefixEnd_548735 : Nat := 4983230072969 + 3 ^ 40 * 548735 * 2
def baseEnd_548735 : Nat := 187843204630010536992613

theorem tailTrace_548735 : CollatzResearch.WordTrace tailWord_548735 prefixEnd_548735 187843204630010536992613 := by
  unfold tailWord_548735
  simp only [CollatzResearch.WordTrace]
  refine ⟨20014009667034286321959659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13342673111356190881306439 20014009667034286321959659)
  ·
    refine ⟨30021014500551429482939489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20014009667034286321959659 30021014500551429482939489)
    ·
      refine ⟨22515760875413572112204617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30021014500551429482939489 22515760875413572112204617)
      ·
        refine ⟨16886820656560179084153463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22515760875413572112204617 16886820656560179084153463)
        ·
          refine ⟨25330230984840268626230195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16886820656560179084153463 25330230984840268626230195)
          ·
            refine ⟨37995346477260402939345293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25330230984840268626230195 37995346477260402939345293)
            ·
              refine ⟨14248254928972651102254485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37995346477260402939345293 14248254928972651102254485)
              ·
                refine ⟨667886949795593020418179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14248254928972651102254485 667886949795593020418179)
                ·
                  refine ⟨1001830424693389530627269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 667886949795593020418179 1001830424693389530627269)
                  ·
                    refine ⟨187843204630010536992613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1001830424693389530627269 187843204630010536992613)
                    ·
                      rfl

theorem cell22_548735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 4].length) (baseStart_548735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548735 prefixEnd_548735 := by exact prefixLift 548735
  have htrace : WordTrace (prefixWord ++ tailWord_548735) baseStart_548735 baseEnd_548735 := by
    simpa [prefixWord, tailWord_548735, baseEnd_548735] using wordTrace_append hprefix tailTrace_548735
  have hstable : (prefixWord ++ tailWord_548735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548735).length < 2 ^ (prefixWord ++ tailWord_548735).sum := by decide
  have hdescent : baseEnd_548735 < baseStart_548735 := by decide
  rcases family_descends (prefixWord ++ tailWord_548735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548767 : List Nat := [1, 1, 2, 5, 3, 1, 2, 1, 6]
def baseStart_548767 : Nat := 118140960795 + 548767 * 2 ^ 59
def prefixEnd_548767 : Nat := 4983230072969 + 3 ^ 40 * 548767 * 2
def baseEnd_548767 : Nat := 62618052961324373397505

theorem tailTrace_548767 : CollatzResearch.WordTrace tailWord_548767 prefixEnd_548767 62618052961324373397505 := by
  unfold tailWord_548767
  simp only [CollatzResearch.WordTrace]
  refine ⟨20015176802918355787124555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13343451201945570524749703 20015176802918355787124555)
  ·
    refine ⟨30022765204377533680686833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20015176802918355787124555 30022765204377533680686833)
    ·
      refine ⟨22517073903283150260515125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30022765204377533680686833 22517073903283150260515125)
      ·
        refine ⟨2110975678432795336923293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22517073903283150260515125 2110975678432795336923293)
        ·
          refine ⟨791615879412298251346235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2110975678432795336923293 791615879412298251346235)
          ·
            refine ⟨1187423819118447377019353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 791615879412298251346235 1187423819118447377019353)
            ·
              refine ⟨890567864338835532764515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1187423819118447377019353 890567864338835532764515)
              ·
                refine ⟨1335851796508253299146773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 890567864338835532764515 1335851796508253299146773)
                ·
                  refine ⟨62618052961324373397505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1335851796508253299146773 62618052961324373397505)
                  ·
                    rfl

theorem cell22_548767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 6].length) (baseStart_548767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548767 prefixEnd_548767 := by exact prefixLift 548767
  have htrace : WordTrace (prefixWord ++ tailWord_548767) baseStart_548767 baseEnd_548767 := by
    simpa [prefixWord, tailWord_548767, baseEnd_548767] using wordTrace_append hprefix tailTrace_548767
  have hstable : (prefixWord ++ tailWord_548767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548767).length < 2 ^ (prefixWord ++ tailWord_548767).sum := by decide
  have hdescent : baseEnd_548767 < baseStart_548767 := by decide
  rcases family_descends (prefixWord ++ tailWord_548767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548874 : List Nat := [3, 1, 2, 2, 4, 1, 2, 2, 5]
def baseStart_548874 : Nat := 118140960795 + 548874 * 2 ^ 59
def prefixEnd_548874 : Nat := 4983230072969 + 3 ^ 40 * 548874 * 2
def baseEnd_548874 : Nat := 62630262390220169255729

theorem tailTrace_548874 : CollatzResearch.WordTrace tailWord_548874 prefixEnd_548874 62630262390220169255729 := by
  unfold tailWord_548874
  simp only [CollatzResearch.WordTrace]
  refine ⟨5004769853382678265317419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13346052942353808707513117 5004769853382678265317419)
  ·
    refine ⟨7507154780074017397976129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5004769853382678265317419 7507154780074017397976129)
    ·
      refine ⟨5630366085055513048482097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7507154780074017397976129 5630366085055513048482097)
      ·
        refine ⟨4222774563791634786361573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5630366085055513048482097 4222774563791634786361573)
        ·
          refine ⟨791770230710931522442795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4222774563791634786361573 791770230710931522442795)
          ·
            refine ⟨1187655346066397283664193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 791770230710931522442795 1187655346066397283664193)
            ·
              refine ⟨890741509549797962748145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1187655346066397283664193 890741509549797962748145)
              ·
                refine ⟨668056132162348472061109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 890741509549797962748145 668056132162348472061109)
                ·
                  refine ⟨62630262390220169255729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 668056132162348472061109 62630262390220169255729)
                  ·
                    rfl

theorem cell22_548874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 5].length) (baseStart_548874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548874 prefixEnd_548874 := by exact prefixLift 548874
  have htrace : WordTrace (prefixWord ++ tailWord_548874) baseStart_548874 baseEnd_548874 := by
    simpa [prefixWord, tailWord_548874, baseEnd_548874] using wordTrace_append hprefix tailTrace_548874
  have hstable : (prefixWord ++ tailWord_548874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548874).length < 2 ^ (prefixWord ++ tailWord_548874).sum := by decide
  have hdescent : baseEnd_548874 < baseStart_548874 := by decide
  rcases family_descends (prefixWord ++ tailWord_548874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548917 : List Nat := [1, 3, 3, 1, 1, 1, 4, 2, 1, 5]
def baseStart_548917 : Nat := 118140960795 + 548917 * 2 ^ 59
def prefixEnd_548917 : Nat := 4983230072969 + 3 ^ 40 * 548917 * 2
def baseEnd_548917 : Nat := 187905506949422728942055

theorem tailTrace_548917 : CollatzResearch.WordTrace tailWord_548917 prefixEnd_548917 187905506949422728942055 := by
  unfold tailWord_548917
  simp only [CollatzResearch.WordTrace]
  refine ⟨20020647752374931405085005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13347098501583287603390003 20020647752374931405085005)
  ·
    refine ⟨7507742907140599276906877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20020647752374931405085005 7507742907140599276906877)
    ·
      refine ⟨2815403590177724728840079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7507742907140599276906877 2815403590177724728840079)
      ·
        refine ⟨4223105385266587093260119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2815403590177724728840079 4223105385266587093260119)
        ·
          refine ⟨6334658077899880639890179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4223105385266587093260119 6334658077899880639890179)
          ·
            refine ⟨9501987116849820959835269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6334658077899880639890179 9501987116849820959835269)
            ·
              refine ⟨1781622584409341429969113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9501987116849820959835269 1781622584409341429969113)
              ·
                refine ⟨1336216938307006072476835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1781622584409341429969113 1336216938307006072476835)
                ·
                  refine ⟨2004325407460509108715253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1336216938307006072476835 2004325407460509108715253)
                  ·
                    refine ⟨187905506949422728942055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2004325407460509108715253 187905506949422728942055)
                    ·
                      rfl

theorem cell22_548917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_548917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548917 prefixEnd_548917 := by exact prefixLift 548917
  have htrace : WordTrace (prefixWord ++ tailWord_548917) baseStart_548917 baseEnd_548917 := by
    simpa [prefixWord, tailWord_548917, baseEnd_548917] using wordTrace_append hprefix tailTrace_548917
  have hstable : (prefixWord ++ tailWord_548917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548917).length < 2 ^ (prefixWord ++ tailWord_548917).sum := by decide
  have hdescent : baseEnd_548917 < baseStart_548917 := by decide
  rcases family_descends (prefixWord ++ tailWord_548917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548992 : List Nat := [2, 1, 1, 2, 1, 3, 1, 6, 5]
def baseStart_548992 : Nat := 118140960795 + 548992 * 2 ^ 59
def prefixEnd_548992 : Nat := 4983230072969 + 3 ^ 40 * 548992 * 2
def baseEnd_548992 : Nat := 62643726994049177772275

theorem tailTrace_548992 : CollatzResearch.WordTrace tailWord_548992 prefixEnd_548992 62643726994049177772275 := by
  unfold tailWord_548992
  simp only [CollatzResearch.WordTrace]
  refine ⟨10011691613551609607032615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13348922151402146142710153 10011691613551609607032615)
  ·
    refine ⟨15017537420327414410548923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10011691613551609607032615 15017537420327414410548923)
    ·
      refine ⟨22526306130491121615823385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15017537420327414410548923 22526306130491121615823385)
      ·
        refine ⟨16894729597868341211867539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22526306130491121615823385 16894729597868341211867539)
        ·
          refine ⟨25342094396802511817801309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16894729597868341211867539 25342094396802511817801309)
          ·
            refine ⟨9503285398800941931675491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25342094396802511817801309 9503285398800941931675491)
            ·
              refine ⟨14254928098201412897513237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9503285398800941931675491 14254928098201412897513237)
              ·
                refine ⟨668199754603191229570933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14254928098201412897513237 668199754603191229570933)
                ·
                  refine ⟨62643726994049177772275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 668199754603191229570933 62643726994049177772275)
                  ·
                    rfl

theorem cell22_548992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 5].length) (baseStart_548992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_548992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_548992 prefixEnd_548992 := by exact prefixLift 548992
  have htrace : WordTrace (prefixWord ++ tailWord_548992) baseStart_548992 baseEnd_548992 := by
    simpa [prefixWord, tailWord_548992, baseEnd_548992] using wordTrace_append hprefix tailTrace_548992
  have hstable : (prefixWord ++ tailWord_548992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548992).length < 2 ^ (prefixWord ++ tailWord_548992).sum := by decide
  have hdescent : baseEnd_548992 < baseStart_548992 := by decide
  rcases family_descends (prefixWord ++ tailWord_548992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549058 : List Nat := [3, 5, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_549058 : Nat := 118140960795 + 549058 * 2 ^ 59
def prefixEnd_549058 : Nat := 4983230072969 + 3 ^ 40 * 549058 * 2
def baseEnd_549058 : Nat := 187953774130945361166623

theorem tailTrace_549058 : CollatzResearch.WordTrace tailWord_549058 prefixEnd_549058 187953774130945361166623 := by
  unfold tailWord_549058
  simp only [CollatzResearch.WordTrace]
  refine ⟨5006447611216028121491957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13350526963242741657311885 5006447611216028121491957)
  ·
    refine ⟨469354463551502636389871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5006447611216028121491957 469354463551502636389871)
    ·
      refine ⟨704031695327253954584807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 469354463551502636389871 704031695327253954584807)
      ·
        refine ⟨1056047542990880931877211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 704031695327253954584807 1056047542990880931877211)
        ·
          refine ⟨1584071314486321397815817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1056047542990880931877211 1584071314486321397815817)
          ·
            refine ⟨1188053485864741048361863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1584071314486321397815817 1188053485864741048361863)
            ·
              refine ⟨1782080228797111572542795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1188053485864741048361863 1782080228797111572542795)
              ·
                refine ⟨2673120343195667358814193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1782080228797111572542795 2673120343195667358814193)
                ·
                  refine ⟨2004840257396750519110645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2673120343195667358814193 2004840257396750519110645)
                  ·
                    refine ⟨187953774130945361166623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2004840257396750519110645 187953774130945361166623)
                    ·
                      rfl

theorem cell22_549058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_549058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549058 prefixEnd_549058 := by exact prefixLift 549058
  have htrace : WordTrace (prefixWord ++ tailWord_549058) baseStart_549058 baseEnd_549058 := by
    simpa [prefixWord, tailWord_549058, baseEnd_549058] using wordTrace_append hprefix tailTrace_549058
  have hstable : (prefixWord ++ tailWord_549058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549058).length < 2 ^ (prefixWord ++ tailWord_549058).sum := by decide
  have hdescent : baseEnd_549058 < baseStart_549058 := by decide
  rcases family_descends (prefixWord ++ tailWord_549058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549067 : List Nat := [1, 1, 1, 1, 3, 2, 4, 2, 1, 6]
def baseStart_549067 : Nat := 118140960795 + 549067 * 2 ^ 59
def prefixEnd_549067 : Nat := 4983230072969 + 3 ^ 40 * 549067 * 2
def baseEnd_549067 : Nat := 187956855014872337691595

theorem tailTrace_549067 : CollatzResearch.WordTrace tailWord_549067 prefixEnd_549067 187956855014872337691595 := by
  unfold tailWord_549067
  simp only [CollatzResearch.WordTrace]
  refine ⟨20026118701831507023045455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13350745801221004682030303 20026118701831507023045455)
  ·
    refine ⟨30039178052747260534568183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20026118701831507023045455 30039178052747260534568183)
    ·
      refine ⟨45058767079120890801852275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30039178052747260534568183 45058767079120890801852275)
      ·
        refine ⟨67588150618681336202778413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45058767079120890801852275 67588150618681336202778413)
        ·
          refine ⟨25345556482005501076041905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67588150618681336202778413 25345556482005501076041905)
          ·
            refine ⟨19009167361504125807031429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25345556482005501076041905 19009167361504125807031429)
            ·
              refine ⟨3564218880282023588818393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19009167361504125807031429 3564218880282023588818393)
              ·
                refine ⟨2673164160211517691613795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3564218880282023588818393 2673164160211517691613795)
                ·
                  refine ⟨4009746240317276537420693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2673164160211517691613795 4009746240317276537420693)
                  ·
                    refine ⟨187956855014872337691595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4009746240317276537420693 187956855014872337691595)
                    ·
                      rfl

theorem cell22_549067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 6].length) (baseStart_549067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549067 prefixEnd_549067 := by exact prefixLift 549067
  have htrace : WordTrace (prefixWord ++ tailWord_549067) baseStart_549067 baseEnd_549067 := by
    simpa [prefixWord, tailWord_549067, baseEnd_549067] using wordTrace_append hprefix tailTrace_549067
  have hstable : (prefixWord ++ tailWord_549067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549067).length < 2 ^ (prefixWord ++ tailWord_549067).sum := by decide
  have hdescent : baseEnd_549067 < baseStart_549067 := by decide
  rcases family_descends (prefixWord ++ tailWord_549067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549082 : List Nat := [3, 1, 1, 2, 2, 1, 2, 10]
def baseStart_549082 : Nat := 118140960795 + 549082 * 2 ^ 59
def prefixEnd_549082 : Nat := 4983230072969 + 3 ^ 40 * 549082 * 2
def baseEnd_549082 : Nat := 20884665535713033174061

theorem tailTrace_549082 : CollatzResearch.WordTrace tailWord_549082 prefixEnd_549082 20884665535713033174061 := by
  unfold tailWord_549082
  simp only [CollatzResearch.WordTrace]
  refine ⟨5006666449194291146210375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13351110531184776389894333 5006666449194291146210375)
  ·
    refine ⟨7509999673791436719315563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5006666449194291146210375 7509999673791436719315563)
    ·
      refine ⟨11264999510687155078973345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7509999673791436719315563 11264999510687155078973345)
      ·
        refine ⟨8448749633015366309230009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11264999510687155078973345 8448749633015366309230009)
        ·
          refine ⟨6336562224761524731922507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8448749633015366309230009 6336562224761524731922507)
          ·
            refine ⟨9504843337142287097883761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6336562224761524731922507 9504843337142287097883761)
            ·
              refine ⟨7128632502856715323412821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9504843337142287097883761 7128632502856715323412821)
              ·
                refine ⟨20884665535713033174061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7128632502856715323412821 20884665535713033174061)
                ·
                  rfl

theorem cell22_549082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 10].length) (baseStart_549082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549082 prefixEnd_549082 := by exact prefixLift 549082
  have htrace : WordTrace (prefixWord ++ tailWord_549082) baseStart_549082 baseEnd_549082 := by
    simpa [prefixWord, tailWord_549082, baseEnd_549082] using wordTrace_append hprefix tailTrace_549082
  have hstable : (prefixWord ++ tailWord_549082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549082).length < 2 ^ (prefixWord ++ tailWord_549082).sum := by decide
  have hdescent : baseEnd_549082 < baseStart_549082 := by decide
  rcases family_descends (prefixWord ++ tailWord_549082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549103 : List Nat := [1, 1, 2, 1, 6, 3, 1, 2, 2, 3]
def baseStart_549103 : Nat := 118140960795 + 549103 * 2 ^ 59
def prefixEnd_549103 : Nat := 4983230072969 + 3 ^ 40 * 549103 * 2
def baseEnd_549103 : Nat := 187969178550580243791485

theorem tailTrace_549103 : CollatzResearch.WordTrace tailWord_549103 prefixEnd_549103 187969178550580243791485 := by
  unfold tailWord_549103
  simp only [CollatzResearch.WordTrace]
  refine ⟨20027431729701085171355963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13351621153134056780903975 20027431729701085171355963)
  ·
    refine ⟨30041147594551627757033945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20027431729701085171355963 30041147594551627757033945)
    ·
      refine ⟨22530860695913720817775459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30041147594551627757033945 22530860695913720817775459)
      ·
        refine ⟨33796291043870581226663189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22530860695913720817775459 33796291043870581226663189)
        ·
          refine ⟨1584201142681433494999837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33796291043870581226663189 1584201142681433494999837)
          ·
            refine ⟨594075428505537560624939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1584201142681433494999837 594075428505537560624939)
            ·
              refine ⟨891113142758306340937409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 594075428505537560624939 891113142758306340937409)
              ·
                refine ⟨668334857068729755703057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 891113142758306340937409 668334857068729755703057)
                ·
                  refine ⟨501251142801547316777293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 668334857068729755703057 501251142801547316777293)
                  ·
                    refine ⟨187969178550580243791485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 501251142801547316777293 187969178550580243791485)
                    ·
                      rfl

theorem cell22_549103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 2, 3].length) (baseStart_549103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549103 prefixEnd_549103 := by exact prefixLift 549103
  have htrace : WordTrace (prefixWord ++ tailWord_549103) baseStart_549103 baseEnd_549103 := by
    simpa [prefixWord, tailWord_549103, baseEnd_549103] using wordTrace_append hprefix tailTrace_549103
  have hstable : (prefixWord ++ tailWord_549103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549103).length < 2 ^ (prefixWord ++ tailWord_549103).sum := by decide
  have hdescent : baseEnd_549103 < baseStart_549103 := by decide
  rcases family_descends (prefixWord ++ tailWord_549103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549112 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 1, 8]
def baseStart_549112 : Nat := 118140960795 + 549112 * 2 ^ 59
def prefixEnd_549112 : Nat := 4983230072969 + 3 ^ 40 * 549112 * 2
def baseEnd_549112 : Nat := 187972259434507220316457

theorem tailTrace_549112 : CollatzResearch.WordTrace tailWord_549112 prefixEnd_549112 187972259434507220316457 := by
  unfold tailWord_549112
  simp only [CollatzResearch.WordTrace]
  refine ⟨10013879993334239854216795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13351839991112319805622393 10013879993334239854216795)
  ·
    refine ⟨15020819990001359781325193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10013879993334239854216795 15020819990001359781325193)
    ·
      refine ⟨11265614992501019835993895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15020819990001359781325193 11265614992501019835993895)
      ·
        refine ⟨16898422488751529753990843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11265614992501019835993895 16898422488751529753990843)
        ·
          refine ⟨25347633733127294630986265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16898422488751529753990843 25347633733127294630986265)
          ·
            refine ⟨19010725299845470973239699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25347633733127294630986265 19010725299845470973239699)
            ·
              refine ⟨28516087949768206459859549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19010725299845470973239699 28516087949768206459859549)
              ·
                refine ⟨10693532981163077422447331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28516087949768206459859549 10693532981163077422447331)
                ·
                  refine ⟨16040299471744616133670997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10693532981163077422447331 16040299471744616133670997)
                  ·
                    refine ⟨187972259434507220316457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 16040299471744616133670997 187972259434507220316457)
                    ·
                      rfl

theorem cell22_549112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_549112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549112 prefixEnd_549112 := by exact prefixLift 549112
  have htrace : WordTrace (prefixWord ++ tailWord_549112) baseStart_549112 baseEnd_549112 := by
    simpa [prefixWord, tailWord_549112, baseEnd_549112] using wordTrace_append hprefix tailTrace_549112
  have hstable : (prefixWord ++ tailWord_549112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549112).length < 2 ^ (prefixWord ++ tailWord_549112).sum := by decide
  have hdescent : baseEnd_549112 < baseStart_549112 := by decide
  rcases family_descends (prefixWord ++ tailWord_549112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549178 : List Nat := [3, 1, 1, 1, 4, 4, 2, 1, 5]
def baseStart_549178 : Nat := 118140960795 + 549178 * 2 ^ 59
def prefixEnd_549178 : Nat := 4983230072969 + 3 ^ 40 * 549178 * 2
def baseEnd_549178 : Nat := 62664950861101682722085

theorem tailTrace_549178 : CollatzResearch.WordTrace tailWord_549178 prefixEnd_549178 62664950861101682722085 := by
  unfold tailWord_549178
  simp only [CollatzResearch.WordTrace]
  refine ⟨5007541801107343245084047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13353444802952915320224125 5007541801107343245084047)
  ·
    refine ⟨7511312701661014867626071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5007541801107343245084047 7511312701661014867626071)
    ·
      refine ⟨11266969052491522301439107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7511312701661014867626071 11266969052491522301439107)
      ·
        refine ⟨16900453578737283452158661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11266969052491522301439107 16900453578737283452158661)
        ·
          refine ⟨3168835046013240647279749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16900453578737283452158661 3168835046013240647279749)
          ·
            refine ⟨594156571127482621364953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3168835046013240647279749 594156571127482621364953)
            ·
              refine ⟨445617428345611966023715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 594156571127482621364953 445617428345611966023715)
              ·
                refine ⟨668426142518417949035573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 445617428345611966023715 668426142518417949035573)
                ·
                  refine ⟨62664950861101682722085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 668426142518417949035573 62664950861101682722085)
                  ·
                    rfl

theorem cell22_549178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 5].length) (baseStart_549178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549178 prefixEnd_549178 := by exact prefixLift 549178
  have htrace : WordTrace (prefixWord ++ tailWord_549178) baseStart_549178 baseEnd_549178 := by
    simpa [prefixWord, tailWord_549178, baseEnd_549178] using wordTrace_append hprefix tailTrace_549178
  have hstable : (prefixWord ++ tailWord_549178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549178).length < 2 ^ (prefixWord ++ tailWord_549178).sum := by decide
  have hdescent : baseEnd_549178 < baseStart_549178 := by decide
  rcases family_descends (prefixWord ++ tailWord_549178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549223 : List Nat := [1, 1, 5, 1, 3, 2, 1, 4, 4]
def baseStart_549223 : Nat := 118140960795 + 549223 * 2 ^ 59
def prefixEnd_549223 : Nat := 4983230072969 + 3 ^ 40 * 549223 * 2
def baseEnd_549223 : Nat := 62670085667646643597039

theorem tailTrace_549223 : CollatzResearch.WordTrace tailWord_549223 prefixEnd_549223 62670085667646643597039 := by
  unfold tailWord_549223
  simp only [CollatzResearch.WordTrace]
  refine ⟨20031808489266345665724323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13354538992844230443816215 20031808489266345665724323)
  ·
    refine ⟨30047712733899518498586485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20031808489266345665724323 30047712733899518498586485)
    ·
      refine ⟨2816973068803079859242483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30047712733899518498586485 2816973068803079859242483)
      ·
        refine ⟨4225459603204619788863725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2816973068803079859242483 4225459603204619788863725)
        ·
          refine ⟨1584547351201732420823897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4225459603204619788863725 1584547351201732420823897)
          ·
            refine ⟨1188410513401299315617923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1584547351201732420823897 1188410513401299315617923)
            ·
              refine ⟨1782615770101948973426885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1188410513401299315617923 1782615770101948973426885)
              ·
                refine ⟨334240456894115432517541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1782615770101948973426885 334240456894115432517541)
                ·
                  refine ⟨62670085667646643597039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 334240456894115432517541 62670085667646643597039)
                  ·
                    rfl

theorem cell22_549223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 4, 4].length) (baseStart_549223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549223 prefixEnd_549223 := by exact prefixLift 549223
  have htrace : WordTrace (prefixWord ++ tailWord_549223) baseStart_549223 baseEnd_549223 := by
    simpa [prefixWord, tailWord_549223, baseEnd_549223] using wordTrace_append hprefix tailTrace_549223
  have hstable : (prefixWord ++ tailWord_549223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549223).length < 2 ^ (prefixWord ++ tailWord_549223).sum := by decide
  have hdescent : baseEnd_549223 < baseStart_549223 := by decide
  rcases family_descends (prefixWord ++ tailWord_549223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549283 : List Nat := [1, 1, 1, 4, 1, 5, 2, 1, 3, 3]
def baseStart_549283 : Nat := 118140960795 + 549283 * 2 ^ 59
def prefixEnd_549283 : Nat := 4983230072969 + 3 ^ 40 * 549283 * 2
def baseEnd_549283 : Nat := 188030796229119774290933

theorem tailTrace_549283 : CollatzResearch.WordTrace tailWord_549283 prefixEnd_549283 188030796229119774290933 := by
  unfold tailWord_549283
  simp only [CollatzResearch.WordTrace]
  refine ⟨20033996869048975912908503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13355997912699317275272335 20033996869048975912908503)
  ·
    refine ⟨30050995303573463869362755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20033996869048975912908503 30050995303573463869362755)
    ·
      refine ⟨45076492955360195804044133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30050995303573463869362755 45076492955360195804044133)
      ·
        refine ⟨8451842429130036713258275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45076492955360195804044133 8451842429130036713258275)
        ·
          refine ⟨12677763643695055069887413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8451842429130036713258275 12677763643695055069887413)
          ·
            refine ⟨1188540341596411412801945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12677763643695055069887413 1188540341596411412801945)
            ·
              refine ⟨891405256197308559601459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1188540341596411412801945 891405256197308559601459)
              ·
                refine ⟨1337107884295962839402189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 891405256197308559601459 1337107884295962839402189)
                ·
                  refine ⟨501415456610986064775821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1337107884295962839402189 501415456610986064775821)
                  ·
                    refine ⟨188030796229119774290933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 501415456610986064775821 188030796229119774290933)
                    ·
                      rfl

theorem cell22_549283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 3, 3].length) (baseStart_549283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549283 prefixEnd_549283 := by exact prefixLift 549283
  have htrace : WordTrace (prefixWord ++ tailWord_549283) baseStart_549283 baseEnd_549283 := by
    simpa [prefixWord, tailWord_549283, baseEnd_549283] using wordTrace_append hprefix tailTrace_549283
  have hstable : (prefixWord ++ tailWord_549283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549283).length < 2 ^ (prefixWord ++ tailWord_549283).sum := by decide
  have hdescent : baseEnd_549283 < baseStart_549283 := by decide
  rcases family_descends (prefixWord ++ tailWord_549283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549326 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 5, 4]
def baseStart_549326 : Nat := 118140960795 + 549326 * 2 ^ 59
def prefixEnd_549326 : Nat := 4983230072969 + 3 ^ 40 * 549326 * 2
def baseEnd_549326 : Nat := 188045516007881995465801

theorem tailTrace_549326 : CollatzResearch.WordTrace tailWord_549326 prefixEnd_549326 188045516007881995465801 := by
  unfold tailWord_549326
  simp only [CollatzResearch.WordTrace]
  refine ⟨2504445650986649282090479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13357043471928796171149221 2504445650986649282090479)
  ·
    refine ⟨3756668476479973923135719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2504445650986649282090479 3756668476479973923135719)
    ·
      refine ⟨5635002714719960884703579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3756668476479973923135719 5635002714719960884703579)
      ·
        refine ⟨8452504072079941327055369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5635002714719960884703579 8452504072079941327055369)
        ·
          refine ⟨6339378054059955995291527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8452504072079941327055369 6339378054059955995291527)
          ·
            refine ⟨9509067081089933992937291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6339378054059955995291527 9509067081089933992937291)
            ·
              refine ⟨14263600621634900989405937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9509067081089933992937291 14263600621634900989405937)
              ·
                refine ⟨10697700466226175742054453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14263600621634900989405937 10697700466226175742054453)
                ·
                  refine ⟨1002909418708703975817605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10697700466226175742054453 1002909418708703975817605)
                  ·
                    refine ⟨188045516007881995465801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1002909418708703975817605 188045516007881995465801)
                    ·
                      rfl

theorem cell22_549326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_549326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549326 prefixEnd_549326 := by exact prefixLift 549326
  have htrace : WordTrace (prefixWord ++ tailWord_549326) baseStart_549326 baseEnd_549326 := by
    simpa [prefixWord, tailWord_549326, baseEnd_549326] using wordTrace_append hprefix tailTrace_549326
  have hstable : (prefixWord ++ tailWord_549326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549326).length < 2 ^ (prefixWord ++ tailWord_549326).sum := by decide
  have hdescent : baseEnd_549326 < baseStart_549326 := by decide
  rcases family_descends (prefixWord ++ tailWord_549326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549334 : List Nat := [5, 2, 1, 1, 1, 1, 5, 2, 1, 3]
def baseStart_549334 : Nat := 118140960795 + 549334 * 2 ^ 59
def prefixEnd_549334 : Nat := 4983230072969 + 3 ^ 40 * 549334 * 2
def baseEnd_549334 : Nat := 188048254571372641265777

theorem tailTrace_549334 : CollatzResearch.WordTrace tailWord_549334 prefixEnd_549334 188048254571372641265777 := by
  unfold tailWord_549334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1252241061991513226438441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13357237994576141082010037 1252241061991513226438441)
  ·
    refine ⟨939180796493634919828831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1252241061991513226438441 939180796493634919828831)
    ·
      refine ⟨1408771194740452379743247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 939180796493634919828831 1408771194740452379743247)
      ·
        refine ⟨2113156792110678569614871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1408771194740452379743247 2113156792110678569614871)
        ·
          refine ⟨3169735188166017854422307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2113156792110678569614871 3169735188166017854422307)
          ·
            refine ⟨4754602782249026781633461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3169735188166017854422307 4754602782249026781633461)
            ·
              refine ⟨445744010835846260778137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4754602782249026781633461 445744010835846260778137)
              ·
                refine ⟨334308008126884695583603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 445744010835846260778137 334308008126884695583603)
                ·
                  refine ⟨501462012190327043375405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 334308008126884695583603 501462012190327043375405)
                  ·
                    refine ⟨188048254571372641265777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 501462012190327043375405 188048254571372641265777)
                    ·
                      rfl

theorem cell22_549334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_549334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549334 prefixEnd_549334 := by exact prefixLift 549334
  have htrace : WordTrace (prefixWord ++ tailWord_549334) baseStart_549334 baseEnd_549334 := by
    simpa [prefixWord, tailWord_549334, baseEnd_549334] using wordTrace_append hprefix tailTrace_549334
  have hstable : (prefixWord ++ tailWord_549334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549334).length < 2 ^ (prefixWord ++ tailWord_549334).sum := by decide
  have hdescent : baseEnd_549334 < baseStart_549334 := by decide
  rcases family_descends (prefixWord ++ tailWord_549334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549347 : List Nat := [1, 1, 1, 6, 4, 1, 2, 1, 5]
def baseStart_549347 : Nat := 118140960795 + 549347 * 2 ^ 59
def prefixEnd_549347 : Nat := 4983230072969 + 3 ^ 40 * 549347 * 2
def baseEnd_549347 : Nat := 62684234912348313563579

theorem tailTrace_549347 : CollatzResearch.WordTrace tailWord_549347 prefixEnd_549347 62684234912348313563579 := by
  unfold tailWord_549347
  simp only [CollatzResearch.WordTrace]
  refine ⟨20036331140817114843238295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13357554093878076562158863 20036331140817114843238295)
  ·
    refine ⟨30054496711225672264857443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20036331140817114843238295 30054496711225672264857443)
    ·
      refine ⟨45081745066838508397286165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30054496711225672264857443 45081745066838508397286165)
      ·
        refine ⟨2113206800008055081122789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 45081745066838508397286165 2113206800008055081122789)
        ·
          refine ⟨396226275001510327710523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2113206800008055081122789 396226275001510327710523)
          ·
            refine ⟨594339412502265491565785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396226275001510327710523 594339412502265491565785)
            ·
              refine ⟨445754559376699118674339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 594339412502265491565785 445754559376699118674339)
              ·
                refine ⟨668631839065048678011509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 445754559376699118674339 668631839065048678011509)
                ·
                  refine ⟨62684234912348313563579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 668631839065048678011509 62684234912348313563579)
                  ·
                    rfl

theorem cell22_549347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 5].length) (baseStart_549347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549347 prefixEnd_549347 := by exact prefixLift 549347
  have htrace : WordTrace (prefixWord ++ tailWord_549347) baseStart_549347 baseEnd_549347 := by
    simpa [prefixWord, tailWord_549347, baseEnd_549347] using wordTrace_append hprefix tailTrace_549347
  have hstable : (prefixWord ++ tailWord_549347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549347).length < 2 ^ (prefixWord ++ tailWord_549347).sum := by decide
  have hdescent : baseEnd_549347 < baseStart_549347 := by decide
  rcases family_descends (prefixWord ++ tailWord_549347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549356 : List Nat := [2, 2, 1, 1, 2, 1, 4, 3, 1, 5]
def baseStart_549356 : Nat := 118140960795 + 549356 * 2 ^ 59
def prefixEnd_549356 : Nat := 4983230072969 + 3 ^ 40 * 549356 * 2
def baseEnd_549356 : Nat := 188055785620971917215709

theorem tailTrace_549356 : CollatzResearch.WordTrace tailWord_549356 prefixEnd_549356 188055785620971917215709 := by
  unfold tailWord_549356
  simp only [CollatzResearch.WordTrace]
  refine ⟨10018329698892254690157961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13357772931856339586877281 10018329698892254690157961)
  ·
    refine ⟨7513747274169191017618471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10018329698892254690157961 7513747274169191017618471)
    ·
      refine ⟨11270620911253786526427707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7513747274169191017618471 11270620911253786526427707)
      ·
        refine ⟨16905931366880679789641561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11270620911253786526427707 16905931366880679789641561)
        ·
          refine ⟨12679448525160509842231171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16905931366880679789641561 12679448525160509842231171)
          ·
            refine ⟨19019172787740764763346757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12679448525160509842231171 19019172787740764763346757)
            ·
              refine ⟨3566094897701393393127517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19019172787740764763346757 3566094897701393393127517)
              ·
                refine ⟨1337285586638022522422819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3566094897701393393127517 1337285586638022522422819)
                ·
                  refine ⟨2005928379957033783634229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1337285586638022522422819 2005928379957033783634229)
                  ·
                    refine ⟨188055785620971917215709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2005928379957033783634229 188055785620971917215709)
                    ·
                      rfl

theorem cell22_549356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_549356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549356 prefixEnd_549356 := by exact prefixLift 549356
  have htrace : WordTrace (prefixWord ++ tailWord_549356) baseStart_549356 baseEnd_549356 := by
    simpa [prefixWord, tailWord_549356, baseEnd_549356] using wordTrace_append hprefix tailTrace_549356
  have hstable : (prefixWord ++ tailWord_549356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549356).length < 2 ^ (prefixWord ++ tailWord_549356).sum := by decide
  have hdescent : baseEnd_549356 < baseStart_549356 := by decide
  rcases family_descends (prefixWord ++ tailWord_549356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549388 : List Nat := [2, 2, 1, 2, 4, 1, 2, 2, 2, 4]
def baseStart_549388 : Nat := 118140960795 + 549388 * 2 ^ 59
def prefixEnd_549388 : Nat := 4983230072969 + 3 ^ 40 * 549388 * 2
def baseEnd_549388 : Nat := 188066739874934500415611

theorem tailTrace_549388 : CollatzResearch.WordTrace tailWord_549388 prefixEnd_549388 188066739874934500415611 := by
  unfold tailWord_549388
  simp only [CollatzResearch.WordTrace]
  refine ⟨10018913266834289422740409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13358551022445719230320545 10018913266834289422740409)
  ·
    refine ⟨7514184950125717067055307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10018913266834289422740409 7514184950125717067055307)
    ·
      refine ⟨11271277425188575600582961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7514184950125717067055307 11271277425188575600582961)
      ·
        refine ⟨8453458068891431700437221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11271277425188575600582961 8453458068891431700437221)
        ·
          refine ⟨1585023387917143443831979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8453458068891431700437221 1585023387917143443831979)
          ·
            refine ⟨2377535081875715165747969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1585023387917143443831979 2377535081875715165747969)
            ·
              refine ⟨1783151311406786374310977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2377535081875715165747969 1783151311406786374310977)
              ·
                refine ⟨1337363483555089780733233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1783151311406786374310977 1337363483555089780733233)
                ·
                  refine ⟨1003022612666317335549925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1337363483555089780733233 1003022612666317335549925)
                  ·
                    refine ⟨188066739874934500415611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1003022612666317335549925 188066739874934500415611)
                    ·
                      rfl

theorem cell22_549388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_549388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549388 prefixEnd_549388 := by exact prefixLift 549388
  have htrace : WordTrace (prefixWord ++ tailWord_549388) baseStart_549388 baseEnd_549388 := by
    simpa [prefixWord, tailWord_549388, baseEnd_549388] using wordTrace_append hprefix tailTrace_549388
  have hstable : (prefixWord ++ tailWord_549388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549388).length < 2 ^ (prefixWord ++ tailWord_549388).sum := by decide
  have hdescent : baseEnd_549388 < baseStart_549388 := by decide
  rcases family_descends (prefixWord ++ tailWord_549388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549390 : List Nat := [4, 1, 1, 2, 3, 1, 1, 4, 2, 3]
def baseStart_549390 : Nat := 118140960795 + 549390 * 2 ^ 59
def prefixEnd_549390 : Nat := 4983230072969 + 3 ^ 40 * 549390 * 2
def baseEnd_549390 : Nat := 188067424515807161865605

theorem tailTrace_549390 : CollatzResearch.WordTrace tailWord_549390 prefixEnd_549390 188067424515807161865605 := by
  unfold tailWord_549390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2504737434957666648381703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13358599653107555458035749 2504737434957666648381703)
  ·
    refine ⟨3757106152436499972572555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2504737434957666648381703 3757106152436499972572555)
    ·
      refine ⟨5635659228654749958858833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3757106152436499972572555 5635659228654749958858833)
      ·
        refine ⟨4226744421491062469144125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5635659228654749958858833 4226744421491062469144125)
        ·
          refine ⟨1585029158059148425929047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4226744421491062469144125 1585029158059148425929047)
          ·
            refine ⟨2377543737088722638893571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1585029158059148425929047 2377543737088722638893571)
            ·
              refine ⟨3566315605633083958340357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2377543737088722638893571 3566315605633083958340357)
              ·
                refine ⟨668684176056203242188817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3566315605633083958340357 668684176056203242188817)
                ·
                  refine ⟨501513132042152431641613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 668684176056203242188817 501513132042152431641613)
                  ·
                    refine ⟨188067424515807161865605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 501513132042152431641613 188067424515807161865605)
                    ·
                      rfl

theorem cell22_549390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_549390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549390 prefixEnd_549390 := by exact prefixLift 549390
  have htrace : WordTrace (prefixWord ++ tailWord_549390) baseStart_549390 baseEnd_549390 := by
    simpa [prefixWord, tailWord_549390, baseEnd_549390] using wordTrace_append hprefix tailTrace_549390
  have hstable : (prefixWord ++ tailWord_549390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549390).length < 2 ^ (prefixWord ++ tailWord_549390).sum := by decide
  have hdescent : baseEnd_549390 < baseStart_549390 := by decide
  rcases family_descends (prefixWord ++ tailWord_549390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549422 : List Nat := [4, 1, 3, 1, 3, 2, 1, 1, 2, 4]
def baseStart_549422 : Nat := 118140960795 + 549422 * 2 ^ 59
def prefixEnd_549422 : Nat := 4983230072969 + 3 ^ 40 * 549422 * 2
def baseEnd_549422 : Nat := 188078378769769745065507

theorem tailTrace_549422 : CollatzResearch.WordTrace tailWord_549422 prefixEnd_549422 188078378769769745065507 := by
  unfold tailWord_549422
  simp only [CollatzResearch.WordTrace]
  refine ⟨2504883326943175331527315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13359377743696935101479013 2504883326943175331527315)
  ·
    refine ⟨3757324990414762997290973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2504883326943175331527315 3757324990414762997290973)
    ·
      refine ⟨1408996871405536123984115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3757324990414762997290973 1408996871405536123984115)
      ·
        refine ⟨2113495307108304185976173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1408996871405536123984115 2113495307108304185976173)
        ·
          refine ⟨792560740165614069741065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2113495307108304185976173 792560740165614069741065)
          ·
            refine ⟨594420555124210552305799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 792560740165614069741065 594420555124210552305799)
            ·
              refine ⟨891630832686315828458699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 594420555124210552305799 891630832686315828458699)
              ·
                refine ⟨1337446249029473742688049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 891630832686315828458699 1337446249029473742688049)
                ·
                  refine ⟨1003084686772105307016037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1337446249029473742688049 1003084686772105307016037)
                  ·
                    refine ⟨188078378769769745065507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1003084686772105307016037 188078378769769745065507)
                    ·
                      rfl

theorem cell22_549422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_549422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549422 prefixEnd_549422 := by exact prefixLift 549422
  have htrace : WordTrace (prefixWord ++ tailWord_549422) baseStart_549422 baseEnd_549422 := by
    simpa [prefixWord, tailWord_549422, baseEnd_549422] using wordTrace_append hprefix tailTrace_549422
  have hstable : (prefixWord ++ tailWord_549422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549422).length < 2 ^ (prefixWord ++ tailWord_549422).sum := by decide
  have hdescent : baseEnd_549422 < baseStart_549422 := by decide
  rcases family_descends (prefixWord ++ tailWord_549422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549431 : List Nat := [1, 1, 3, 1, 2, 3, 2, 2, 7]
def baseStart_549431 : Nat := 118140960795 + 549431 * 2 ^ 59
def prefixEnd_549431 : Nat := 4983230072969 + 3 ^ 40 * 549431 * 2
def baseEnd_549431 : Nat := 62693819884565573863493

theorem tailTrace_549431 : CollatzResearch.WordTrace tailWord_549431 prefixEnd_549431 62693819884565573863493 := by
  unfold tailWord_549431
  simp only [CollatzResearch.WordTrace]
  refine ⟨20039394872512797189296147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13359596581675198126197431 20039394872512797189296147)
  ·
    refine ⟨30059092308769195783944221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20039394872512797189296147 30059092308769195783944221)
    ·
      refine ⟨11272159615788448418979083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30059092308769195783944221 11272159615788448418979083)
      ·
        refine ⟨16908239423682672628468625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11272159615788448418979083 16908239423682672628468625)
        ·
          refine ⟨12681179567762004471351469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16908239423682672628468625 12681179567762004471351469)
          ·
            refine ⟨4755442337910751676756801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12681179567762004471351469 4755442337910751676756801)
            ·
              refine ⟨3566581753433063757567601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4755442337910751676756801 3566581753433063757567601)
              ·
                refine ⟨2674936315074797818175701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3566581753433063757567601 2674936315074797818175701)
                ·
                  refine ⟨62693819884565573863493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2674936315074797818175701 62693819884565573863493)
                  ·
                    rfl

theorem cell22_549431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 7].length) (baseStart_549431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549431 prefixEnd_549431 := by exact prefixLift 549431
  have htrace : WordTrace (prefixWord ++ tailWord_549431) baseStart_549431 baseEnd_549431 := by
    simpa [prefixWord, tailWord_549431, baseEnd_549431] using wordTrace_append hprefix tailTrace_549431
  have hstable : (prefixWord ++ tailWord_549431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549431).length < 2 ^ (prefixWord ++ tailWord_549431).sum := by decide
  have hdescent : baseEnd_549431 < baseStart_549431 := by decide
  rcases family_descends (prefixWord ++ tailWord_549431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549540 : List Nat := [2, 3, 1, 2, 2, 1, 4, 1, 2, 4]
def baseStart_549540 : Nat := 118140960795 + 549540 * 2 ^ 59
def prefixEnd_549540 : Nat := 4983230072969 + 3 ^ 40 * 549540 * 2
def baseEnd_549540 : Nat := 188118772581256770615145

theorem tailTrace_549540 : CollatzResearch.WordTrace tailWord_549540 prefixEnd_549540 188118772581256770615145 := by
  unfold tailWord_549540
  simp only [CollatzResearch.WordTrace]
  refine ⟨10021685214558954402507037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13362246952745272536676049 10021685214558954402507037)
  ·
    refine ⟨3758131955459607900940139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10021685214558954402507037 3758131955459607900940139)
    ·
      refine ⟨5637197933189411851410209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3758131955459607900940139 5637197933189411851410209)
      ·
        refine ⟨4227898449892058888557657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5637197933189411851410209 4227898449892058888557657)
        ·
          refine ⟨3170923837419044166418243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4227898449892058888557657 3170923837419044166418243)
          ·
            refine ⟨4756385756128566249627365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3170923837419044166418243 4756385756128566249627365)
            ·
              refine ⟨891822329274106171805131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4756385756128566249627365 891822329274106171805131)
              ·
                refine ⟨1337733493911159257707697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 891822329274106171805131 1337733493911159257707697)
                ·
                  refine ⟨1003300120433369443280773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1337733493911159257707697 1003300120433369443280773)
                  ·
                    refine ⟨188118772581256770615145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1003300120433369443280773 188118772581256770615145)
                    ·
                      rfl

theorem cell22_549540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_549540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549540 prefixEnd_549540 := by exact prefixLift 549540
  have htrace : WordTrace (prefixWord ++ tailWord_549540) baseStart_549540 baseEnd_549540 := by
    simpa [prefixWord, tailWord_549540, baseEnd_549540] using wordTrace_append hprefix tailTrace_549540
  have hstable : (prefixWord ++ tailWord_549540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549540).length < 2 ^ (prefixWord ++ tailWord_549540).sum := by decide
  have hdescent : baseEnd_549540 < baseStart_549540 := by decide
  rcases family_descends (prefixWord ++ tailWord_549540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549546 : List Nat := [3, 1, 5, 2, 1, 1, 3, 1, 1, 4]
def baseStart_549546 : Nat := 118140960795 + 549546 * 2 ^ 59
def prefixEnd_549546 : Nat := 4983230072969 + 3 ^ 40 * 549546 * 2
def baseEnd_549546 : Nat := 188120826503874754965127

theorem tailTrace_549546 : CollatzResearch.WordTrace tailWord_549546 prefixEnd_549546 188120826503874754965127 := by
  unfold tailWord_549546
  simp only [CollatzResearch.WordTrace]
  refine ⟨5010897316774042957433123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13362392844730781219821661 5010897316774042957433123)
  ·
    refine ⟨7516345975161064436149685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5010897316774042957433123 7516345975161064436149685)
    ·
      refine ⟨704657435171349790889033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7516345975161064436149685 704657435171349790889033)
      ·
        refine ⟨528493076378512343166775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 704657435171349790889033 528493076378512343166775)
        ·
          refine ⟨792739614567768514750163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 528493076378512343166775 792739614567768514750163)
          ·
            refine ⟨1189109421851652772125245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 792739614567768514750163 1189109421851652772125245)
            ·
              refine ⟨445916033194369789546967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1189109421851652772125245 445916033194369789546967)
              ·
                refine ⟨668874049791554684320451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 445916033194369789546967 668874049791554684320451)
                ·
                  refine ⟨1003311074687332026480677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 668874049791554684320451 1003311074687332026480677)
                  ·
                    refine ⟨188120826503874754965127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1003311074687332026480677 188120826503874754965127)
                    ·
                      rfl

theorem cell22_549546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_549546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549546 prefixEnd_549546 := by exact prefixLift 549546
  have htrace : WordTrace (prefixWord ++ tailWord_549546) baseStart_549546 baseEnd_549546 := by
    simpa [prefixWord, tailWord_549546, baseEnd_549546] using wordTrace_append hprefix tailTrace_549546
  have hstable : (prefixWord ++ tailWord_549546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549546).length < 2 ^ (prefixWord ++ tailWord_549546).sum := by decide
  have hdescent : baseEnd_549546 < baseStart_549546 := by decide
  rcases family_descends (prefixWord ++ tailWord_549546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549568 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 2, 6]
def baseStart_549568 : Nat := 118140960795 + 549568 * 2 ^ 59
def prefixEnd_549568 : Nat := 4983230072969 + 3 ^ 40 * 549568 * 2
def baseEnd_549568 : Nat := 188128357553474030915059

theorem tailTrace_549568 : CollatzResearch.WordTrace tailWord_549568 prefixEnd_549568 188128357553474030915059 := by
  unfold tailWord_549568
  simp only [CollatzResearch.WordTrace]
  refine ⟨10022195836508234793516679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13362927782010979724688905 10022195836508234793516679)
  ·
    refine ⟨15033293754762352190275019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10022195836508234793516679 15033293754762352190275019)
    ·
      refine ⟨22549940632143528285412529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15033293754762352190275019 22549940632143528285412529)
      ·
        refine ⟨16912455474107646214059397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22549940632143528285412529 16912455474107646214059397)
        ·
          refine ⟨3171085401395183665136137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16912455474107646214059397 3171085401395183665136137)
          ·
            refine ⟨2378314051046387748852103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3171085401395183665136137 2378314051046387748852103)
            ·
              refine ⟨3567471076569581623278155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2378314051046387748852103 3567471076569581623278155)
              ·
                refine ⟨5351206614854372434917233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3567471076569581623278155 5351206614854372434917233)
                ·
                  refine ⟨4013404961140779326187925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5351206614854372434917233 4013404961140779326187925)
                  ·
                    refine ⟨188128357553474030915059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4013404961140779326187925 188128357553474030915059)
                    ·
                      rfl

theorem cell22_549568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 2, 6].length) (baseStart_549568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549568 prefixEnd_549568 := by exact prefixLift 549568
  have htrace : WordTrace (prefixWord ++ tailWord_549568) baseStart_549568 baseEnd_549568 := by
    simpa [prefixWord, tailWord_549568, baseEnd_549568] using wordTrace_append hprefix tailTrace_549568
  have hstable : (prefixWord ++ tailWord_549568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549568).length < 2 ^ (prefixWord ++ tailWord_549568).sum := by decide
  have hdescent : baseEnd_549568 < baseStart_549568 := by decide
  rcases family_descends (prefixWord ++ tailWord_549568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549604 : List Nat := [2, 3, 1, 1, 1, 5, 2, 3, 1, 3]
def baseStart_549604 : Nat := 118140960795 + 549604 * 2 ^ 59
def prefixEnd_549604 : Nat := 4983230072969 + 3 ^ 40 * 549604 * 2
def baseEnd_549604 : Nat := 188140681089181937014949

theorem tailTrace_549604 : CollatzResearch.WordTrace tailWord_549604 prefixEnd_549604 188140681089181937014949 := by
  unfold tailWord_549604
  simp only [CollatzResearch.WordTrace]
  refine ⟨10022852350443023867671933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13363803133924031823562577 10022852350443023867671933)
  ·
    refine ⟨3758569631416133950376975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10022852350443023867671933 3758569631416133950376975)
    ·
      refine ⟨5637854447124200925565463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3758569631416133950376975 5637854447124200925565463)
      ·
        refine ⟨8456781670686301388348195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5637854447124200925565463 8456781670686301388348195)
        ·
          refine ⟨12685172506029452082522293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8456781670686301388348195 12685172506029452082522293)
          ·
            refine ⟨1189234922440261132736465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12685172506029452082522293 1189234922440261132736465)
            ·
              refine ⟨891926191830195849552349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1189234922440261132736465 891926191830195849552349)
              ·
                refine ⟨334472321936323443582131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 891926191830195849552349 334472321936323443582131)
                ·
                  refine ⟨501708482904485165373197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 334472321936323443582131 501708482904485165373197)
                  ·
                    refine ⟨188140681089181937014949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 501708482904485165373197 188140681089181937014949)
                    ·
                      rfl

theorem cell22_549604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_549604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549604 prefixEnd_549604 := by exact prefixLift 549604
  have htrace : WordTrace (prefixWord ++ tailWord_549604) baseStart_549604 baseEnd_549604 := by
    simpa [prefixWord, tailWord_549604, baseEnd_549604] using wordTrace_append hprefix tailTrace_549604
  have hstable : (prefixWord ++ tailWord_549604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549604).length < 2 ^ (prefixWord ++ tailWord_549604).sum := by decide
  have hdescent : baseEnd_549604 < baseStart_549604 := by decide
  rcases family_descends (prefixWord ++ tailWord_549604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549634 : List Nat := [3, 4, 1, 1, 1, 3, 3, 1, 5]
def baseStart_549634 : Nat := 118140960795 + 549634 * 2 ^ 59
def prefixEnd_549634 : Nat := 4983230072969 + 3 ^ 40 * 549634 * 2
def baseEnd_549634 : Nat := 62716983567423952921619

theorem tailTrace_549634 : CollatzResearch.WordTrace tailWord_549634 prefixEnd_549634 62716983567423952921619 := by
  unfold tailWord_549634
  simp only [CollatzResearch.WordTrace]
  refine ⟨5011699722694340714733989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13364532593851575239290637 5011699722694340714733989)
  ·
    refine ⟨939693698005188884012623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5011699722694340714733989 939693698005188884012623)
    ·
      refine ⟨1409540547007783326018935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 939693698005188884012623 1409540547007783326018935)
      ·
        refine ⟨2114310820511674989028403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1409540547007783326018935 2114310820511674989028403)
        ·
          refine ⟨3171466230767512483542605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2114310820511674989028403 3171466230767512483542605)
          ·
            refine ⟨1189299836537817181328477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3171466230767512483542605 1189299836537817181328477)
            ·
              refine ⟨445987438701681442998179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1189299836537817181328477 445987438701681442998179)
              ·
                refine ⟨668981158052522164497269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 445987438701681442998179 668981158052522164497269)
                ·
                  refine ⟨62716983567423952921619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 668981158052522164497269 62716983567423952921619)
                  ·
                    rfl

theorem cell22_549634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_549634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549634 prefixEnd_549634 := by exact prefixLift 549634
  have htrace : WordTrace (prefixWord ++ tailWord_549634) baseStart_549634 baseEnd_549634 := by
    simpa [prefixWord, tailWord_549634, baseEnd_549634] using wordTrace_append hprefix tailTrace_549634
  have hstable : (prefixWord ++ tailWord_549634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549634).length < 2 ^ (prefixWord ++ tailWord_549634).sum := by decide
  have hdescent : baseEnd_549634 < baseStart_549634 := by decide
  rcases family_descends (prefixWord ++ tailWord_549634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549786 : List Nat := [3, 1, 1, 4, 4, 1, 1, 2, 5]
def baseStart_549786 : Nat := 118140960795 + 549786 * 2 ^ 59
def prefixEnd_549786 : Nat := 4983230072969 + 3 ^ 40 * 549786 * 2
def baseEnd_549786 : Nat := 62734327802864709654797

theorem tailTrace_549786 : CollatzResearch.WordTrace tailWord_549786 prefixEnd_549786 62734327802864709654797 := by
  unfold tailWord_549786
  simp only [CollatzResearch.WordTrace]
  refine ⟨5013085696556673204617303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13368228524151128545646141 5013085696556673204617303)
  ·
    refine ⟨7519628544835009806925955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5013085696556673204617303 7519628544835009806925955)
    ·
      refine ⟨11279442817252514710388933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7519628544835009806925955 11279442817252514710388933)
      ·
        refine ⟨2114895528234846508197925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11279442817252514710388933 2114895528234846508197925)
        ·
          refine ⟨396542911544033720287111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2114895528234846508197925 396542911544033720287111)
          ·
            refine ⟨594814367316050580430667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396542911544033720287111 594814367316050580430667)
            ·
              refine ⟨892221550974075870646001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 594814367316050580430667 892221550974075870646001)
              ·
                refine ⟨669166163230556902984501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 892221550974075870646001 669166163230556902984501)
                ·
                  refine ⟨62734327802864709654797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 669166163230556902984501 62734327802864709654797)
                  ·
                    rfl

theorem cell22_549786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 5].length) (baseStart_549786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549786 prefixEnd_549786 := by exact prefixLift 549786
  have htrace : WordTrace (prefixWord ++ tailWord_549786) baseStart_549786 baseEnd_549786 := by
    simpa [prefixWord, tailWord_549786, baseEnd_549786] using wordTrace_append hprefix tailTrace_549786
  have hstable : (prefixWord ++ tailWord_549786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549786).length < 2 ^ (prefixWord ++ tailWord_549786).sum := by decide
  have hdescent : baseEnd_549786 < baseStart_549786 := by decide
  rcases family_descends (prefixWord ++ tailWord_549786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549795 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 3, 5]
def baseStart_549795 : Nat := 118140960795 + 549795 * 2 ^ 59
def prefixEnd_549795 : Nat := 4983230072969 + 3 ^ 40 * 549795 * 2
def baseEnd_549795 : Nat := 188206064292521105489363

theorem tailTrace_549795 : CollatzResearch.WordTrace tailWord_549795 prefixEnd_549795 188206064292521105489363 := by
  unfold tailWord_549795
  simp only [CollatzResearch.WordTrace]
  refine ⟨20052671043194087355546839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13368447362129391570364559 20052671043194087355546839)
  ·
    refine ⟨30079006564791131033320259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20052671043194087355546839 30079006564791131033320259)
    ·
      refine ⟨45118509847186696549980389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30079006564791131033320259 45118509847186696549980389)
      ·
        refine ⟨8459720596347505603121323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45118509847186696549980389 8459720596347505603121323)
        ·
          refine ⟨12689580894521258404681985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8459720596347505603121323 12689580894521258404681985)
          ·
            refine ⟨9517185670890943803511489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12689580894521258404681985 9517185670890943803511489)
            ·
              refine ⟨7137889253168207852633617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9517185670890943803511489 7137889253168207852633617)
              ·
                refine ⟨5353416939876155889475213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7137889253168207852633617 5353416939876155889475213)
                ·
                  refine ⟨2007531352453558458553205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5353416939876155889475213 2007531352453558458553205)
                  ·
                    refine ⟨188206064292521105489363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2007531352453558458553205 188206064292521105489363)
                    ·
                      rfl

theorem cell22_549795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 5].length) (baseStart_549795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549795 prefixEnd_549795 := by exact prefixLift 549795
  have htrace : WordTrace (prefixWord ++ tailWord_549795) baseStart_549795 baseEnd_549795 := by
    simpa [prefixWord, tailWord_549795, baseEnd_549795] using wordTrace_append hprefix tailTrace_549795
  have hstable : (prefixWord ++ tailWord_549795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549795).length < 2 ^ (prefixWord ++ tailWord_549795).sum := by decide
  have hdescent : baseEnd_549795 < baseStart_549795 := by decide
  rcases family_descends (prefixWord ++ tailWord_549795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549842 : List Nat := [3, 2, 2, 3, 1, 1, 10]
def baseStart_549842 : Nat := 118140960795 + 549842 * 2 ^ 59
def prefixEnd_549842 : Nat := 4983230072969 + 3 ^ 40 * 549842 * 2
def baseEnd_549842 : Nat := 6971190864926987020897

theorem tailTrace_549842 : CollatzResearch.WordTrace tailWord_549842 prefixEnd_549842 6971190864926987020897 := by
  unfold tailWord_549842
  simp only [CollatzResearch.WordTrace]
  refine ⟨5013596318505953595626945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13369590182682542921671853 5013596318505953595626945)
  ·
    refine ⟨3760197238879465196720209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5013596318505953595626945 3760197238879465196720209)
    ·
      refine ⟨2820147929159598897540157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3760197238879465196720209 2820147929159598897540157)
      ·
        refine ⟨1057555473434849586577559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2820147929159598897540157 1057555473434849586577559)
        ·
          refine ⟨1586333210152274379866339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1057555473434849586577559 1586333210152274379866339)
          ·
            refine ⟨2379499815228411569799509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1586333210152274379866339 2379499815228411569799509)
            ·
              refine ⟨6971190864926987020897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2379499815228411569799509 6971190864926987020897)
              ·
                rfl

theorem cell22_549842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 10].length) (baseStart_549842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549842 prefixEnd_549842 := by exact prefixLift 549842
  have htrace : WordTrace (prefixWord ++ tailWord_549842) baseStart_549842 baseEnd_549842 := by
    simpa [prefixWord, tailWord_549842, baseEnd_549842] using wordTrace_append hprefix tailTrace_549842
  have hstable : (prefixWord ++ tailWord_549842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549842).length < 2 ^ (prefixWord ++ tailWord_549842).sum := by decide
  have hdescent : baseEnd_549842 < baseStart_549842 := by decide
  rcases family_descends (prefixWord ++ tailWord_549842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549844 : List Nat := [2, 4, 1, 2, 1, 3, 1, 2, 2, 4]
def baseStart_549844 : Nat := 118140960795 + 549844 * 2 ^ 59
def prefixEnd_549844 : Nat := 4983230072969 + 3 ^ 40 * 549844 * 2
def baseEnd_549844 : Nat := 188222837993901311014213

theorem tailTrace_549844 : CollatzResearch.WordTrace tailWord_549844 prefixEnd_549844 188222837993901311014213 := by
  unfold tailWord_549844
  simp only [CollatzResearch.WordTrace]
  refine ⟨10027229110008284362040293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13369638813344379149387057 10027229110008284362040293)
  ·
    refine ⟨1880105458126553317882555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10027229110008284362040293 1880105458126553317882555)
    ·
      refine ⟨2820158187189829976823833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1880105458126553317882555 2820158187189829976823833)
      ·
        refine ⟨2115118640392372482617875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2820158187189829976823833 2115118640392372482617875)
        ·
          refine ⟨3172677960588558723926813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2115118640392372482617875 3172677960588558723926813)
          ·
            refine ⟨1189754235220709521472555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3172677960588558723926813 1189754235220709521472555)
            ·
              refine ⟨1784631352831064282208833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1189754235220709521472555 1784631352831064282208833)
              ·
                refine ⟨1338473514623298211656625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1784631352831064282208833 1338473514623298211656625)
                ·
                  refine ⟨1003855135967473658742469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1338473514623298211656625 1003855135967473658742469)
                  ·
                    refine ⟨188222837993901311014213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1003855135967473658742469 188222837993901311014213)
                    ·
                      rfl

theorem cell22_549844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_549844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549844 prefixEnd_549844 := by exact prefixLift 549844
  have htrace : WordTrace (prefixWord ++ tailWord_549844) baseStart_549844 baseEnd_549844 := by
    simpa [prefixWord, tailWord_549844, baseEnd_549844] using wordTrace_append hprefix tailTrace_549844
  have hstable : (prefixWord ++ tailWord_549844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549844).length < 2 ^ (prefixWord ++ tailWord_549844).sum := by decide
  have hdescent : baseEnd_549844 < baseStart_549844 := by decide
  rcases family_descends (prefixWord ++ tailWord_549844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549846 : List Nat := [5, 2, 1, 1, 2, 1, 2, 1, 4, 3]
def baseStart_549846 : Nat := 118140960795 + 549846 * 2 ^ 59
def prefixEnd_549846 : Nat := 4983230072969 + 3 ^ 40 * 549846 * 2
def baseEnd_549846 : Nat := 188223522634773972464207

theorem tailTrace_549846 : CollatzResearch.WordTrace tailWord_549846 prefixEnd_549846 188223522634773972464207 := by
  unfold tailWord_549846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1253408197875582691603337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13369687444006215377102261 1253408197875582691603337)
  ·
    refine ⟨940056148406687018702503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1253408197875582691603337 940056148406687018702503)
    ·
      refine ⟨1410084222610030528053755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 940056148406687018702503 1410084222610030528053755)
      ·
        refine ⟨2115126333915045792080633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1410084222610030528053755 2115126333915045792080633)
        ·
          refine ⟨1586344750436284344060475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2115126333915045792080633 1586344750436284344060475)
          ·
            refine ⟨2379517125654426516090713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1586344750436284344060475 2379517125654426516090713)
            ·
              refine ⟨1784637844240819887068035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2379517125654426516090713 1784637844240819887068035)
              ·
                refine ⟨2676956766361229830602053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1784637844240819887068035 2676956766361229830602053)
                ·
                  refine ⟨501929393692730593237885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2676956766361229830602053 501929393692730593237885)
                  ·
                    refine ⟨188223522634773972464207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 501929393692730593237885 188223522634773972464207)
                    ·
                      rfl

theorem cell22_549846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_549846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549846 prefixEnd_549846 := by exact prefixLift 549846
  have htrace : WordTrace (prefixWord ++ tailWord_549846) baseStart_549846 baseEnd_549846 := by
    simpa [prefixWord, tailWord_549846, baseEnd_549846] using wordTrace_append hprefix tailTrace_549846
  have hstable : (prefixWord ++ tailWord_549846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549846).length < 2 ^ (prefixWord ++ tailWord_549846).sum := by decide
  have hdescent : baseEnd_549846 < baseStart_549846 := by decide
  rcases family_descends (prefixWord ++ tailWord_549846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549863 : List Nat := [1, 1, 5, 2, 2, 3, 2, 1, 2, 3]
def baseStart_549863 : Nat := 118140960795 + 549863 * 2 ^ 59
def prefixEnd_549863 : Nat := 4983230072969 + 3 ^ 40 * 549863 * 2
def baseEnd_549863 : Nat := 188229342082191594789155

theorem tailTrace_549863 : CollatzResearch.WordTrace tailWord_549863 prefixEnd_549863 188229342082191594789155 := by
  unfold tailWord_549863
  simp only [CollatzResearch.WordTrace]
  refine ⟨20055151206947734969022243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13370100804631823312681495 20055151206947734969022243)
  ·
    refine ⟨30082726810421602453533365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20055151206947734969022243 30082726810421602453533365)
    ·
      refine ⟨2820255638477025230018753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30082726810421602453533365 2820255638477025230018753)
      ·
        refine ⟨2115191728857768922514065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2820255638477025230018753 2115191728857768922514065)
        ·
          refine ⟨1586393796643326691885549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2115191728857768922514065 1586393796643326691885549)
          ·
            refine ⟨594897673741247509457081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1586393796643326691885549 594897673741247509457081)
            ·
              refine ⟨446173255305935632092811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 594897673741247509457081 446173255305935632092811)
              ·
                refine ⟨669259882958903448139217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 446173255305935632092811 669259882958903448139217)
                ·
                  refine ⟨501944912219177586104413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 669259882958903448139217 501944912219177586104413)
                  ·
                    refine ⟨188229342082191594789155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 501944912219177586104413 188229342082191594789155)
                    ·
                      rfl

theorem cell22_549863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_549863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549863 prefixEnd_549863 := by exact prefixLift 549863
  have htrace : WordTrace (prefixWord ++ tailWord_549863) baseStart_549863 baseEnd_549863 := by
    simpa [prefixWord, tailWord_549863, baseEnd_549863] using wordTrace_append hprefix tailTrace_549863
  have hstable : (prefixWord ++ tailWord_549863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549863).length < 2 ^ (prefixWord ++ tailWord_549863).sum := by decide
  have hdescent : baseEnd_549863 < baseStart_549863 := by decide
  rcases family_descends (prefixWord ++ tailWord_549863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549932 : List Nat := [2, 2, 1, 1, 1, 2, 5, 2, 6]
def baseStart_549932 : Nat := 118140960795 + 549932 * 2 ^ 59
def prefixEnd_549932 : Nat := 4983230072969 + 3 ^ 40 * 549932 * 2
def baseEnd_549932 : Nat := 62750987397432804937981

theorem tailTrace_549932 : CollatzResearch.WordTrace tailWord_549932 prefixEnd_549932 62750987397432804937981 := by
  unfold tailWord_549932
  simp only [CollatzResearch.WordTrace]
  refine ⟨10028833921848879876642025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13371778562465173168856033 10028833921848879876642025)
  ·
    refine ⟨7521625441386659907481519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10028833921848879876642025 7521625441386659907481519)
    ·
      refine ⟨11282438162079989861222279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7521625441386659907481519 11282438162079989861222279)
      ·
        refine ⟨16923657243119984791833419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11282438162079989861222279 16923657243119984791833419)
        ·
          refine ⟨25385485864679977187750129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16923657243119984791833419 25385485864679977187750129)
          ·
            refine ⟨19039114398509982890812597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25385485864679977187750129 19039114398509982890812597)
            ·
              refine ⟨1784916974860310896013681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19039114398509982890812597 1784916974860310896013681)
              ·
                refine ⟨1338687731145233172010261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1784916974860310896013681 1338687731145233172010261)
                ·
                  refine ⟨62750987397432804937981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1338687731145233172010261 62750987397432804937981)
                  ·
                    rfl

theorem cell22_549932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 6].length) (baseStart_549932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549932 prefixEnd_549932 := by exact prefixLift 549932
  have htrace : WordTrace (prefixWord ++ tailWord_549932) baseStart_549932 baseEnd_549932 := by
    simpa [prefixWord, tailWord_549932, baseEnd_549932] using wordTrace_append hprefix tailTrace_549932
  have hstable : (prefixWord ++ tailWord_549932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549932).length < 2 ^ (prefixWord ++ tailWord_549932).sum := by decide
  have hdescent : baseEnd_549932 < baseStart_549932 := by decide
  rcases family_descends (prefixWord ++ tailWord_549932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549934 : List Nat := [4, 1, 3, 1, 1, 1, 1, 3, 3, 4]
def baseStart_549934 : Nat := 118140960795 + 549934 * 2 ^ 59
def prefixEnd_549934 : Nat := 4983230072969 + 3 ^ 40 * 549934 * 2
def baseEnd_549934 : Nat := 188253646833171076263937

theorem tailTrace_549934 : CollatzResearch.WordTrace tailWord_549934 prefixEnd_549934 188253646833171076263937 := by
  unfold tailWord_549934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2507217598711314261857107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13371827193127009396571237 2507217598711314261857107)
  ·
    refine ⟨3760826398066971392785661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2507217598711314261857107 3760826398066971392785661)
    ·
      refine ⟨1410309899275114272294623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3760826398066971392785661 1410309899275114272294623)
      ·
        refine ⟨2115464848912671408441935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1410309899275114272294623 2115464848912671408441935)
        ·
          refine ⟨3173197273369007112662903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2115464848912671408441935 3173197273369007112662903)
          ·
            refine ⟨4759795910053510668994355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3173197273369007112662903 4759795910053510668994355)
            ·
              refine ⟨7139693865080266003491533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4759795910053510668994355 7139693865080266003491533)
              ·
                refine ⟨2677385199405099751309325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7139693865080266003491533 2677385199405099751309325)
                ·
                  refine ⟨1004019449776912406740997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2677385199405099751309325 1004019449776912406740997)
                  ·
                    refine ⟨188253646833171076263937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1004019449776912406740997 188253646833171076263937)
                    ·
                      rfl

theorem cell22_549934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_549934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549934 prefixEnd_549934 := by exact prefixLift 549934
  have htrace : WordTrace (prefixWord ++ tailWord_549934) baseStart_549934 baseEnd_549934 := by
    simpa [prefixWord, tailWord_549934, baseEnd_549934] using wordTrace_append hprefix tailTrace_549934
  have hstable : (prefixWord ++ tailWord_549934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549934).length < 2 ^ (prefixWord ++ tailWord_549934).sum := by decide
  have hdescent : baseEnd_549934 < baseStart_549934 := by decide
  rcases family_descends (prefixWord ++ tailWord_549934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549994 : List Nat := [3, 1, 3, 2, 2, 2, 1, 8]
def baseStart_549994 : Nat := 118140960795 + 549994 * 2 ^ 59
def prefixEnd_549994 : Nat := 4983230072969 + 3 ^ 40 * 549994 * 2
def baseEnd_549994 : Nat := 20919354006594546640417

theorem tailTrace_549994 : CollatzResearch.WordTrace tailWord_549994 prefixEnd_549994 20919354006594546640417 := by
  unfold tailWord_549994
  simp only [CollatzResearch.WordTrace]
  refine ⟨5014982292368286085510259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13373286112982096228027357 5014982292368286085510259)
  ·
    refine ⟨7522473438552429128265389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5014982292368286085510259 7522473438552429128265389)
    ·
      refine ⟨2820927539457160923099521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7522473438552429128265389 2820927539457160923099521)
      ·
        refine ⟨2115695654592870692324641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2820927539457160923099521 2115695654592870692324641)
        ·
          refine ⟨1586771740944653019243481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2115695654592870692324641 1586771740944653019243481)
          ·
            refine ⟨1190078805708489764432611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1586771740944653019243481 1190078805708489764432611)
            ·
              refine ⟨1785118208562734646648917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1190078805708489764432611 1785118208562734646648917)
              ·
                refine ⟨20919354006594546640417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1785118208562734646648917 20919354006594546640417)
                ·
                  rfl

theorem cell22_549994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 8].length) (baseStart_549994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_549994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_549994 prefixEnd_549994 := by exact prefixLift 549994
  have htrace : WordTrace (prefixWord ++ tailWord_549994) baseStart_549994 baseEnd_549994 := by
    simpa [prefixWord, tailWord_549994, baseEnd_549994] using wordTrace_append hprefix tailTrace_549994
  have hstable : (prefixWord ++ tailWord_549994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549994).length < 2 ^ (prefixWord ++ tailWord_549994).sum := by decide
  have hdescent : baseEnd_549994 < baseStart_549994 := by decide
  rcases family_descends (prefixWord ++ tailWord_549994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550101 : List Nat := [1, 3, 2, 4, 1, 2, 1, 2, 6]
def baseStart_550101 : Nat := 118140960795 + 550101 * 2 ^ 59
def prefixEnd_550101 : Nat := 4983230072969 + 3 ^ 40 * 550101 * 2
def baseEnd_550101 : Nat := 62770271448679435779475

theorem tailTrace_550101 : CollatzResearch.WordTrace tailWord_550101 prefixEnd_550101 62770271448679435779475 := by
  unfold tailWord_550101
  simp only [CollatzResearch.WordTrace]
  refine ⟨20063831780085501616186157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13375887853390334410790771 20063831780085501616186157)
  ·
    refine ⟨7523936917532063106069809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20063831780085501616186157 7523936917532063106069809)
    ·
      refine ⟨5642952688149047329552357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7523936917532063106069809 5642952688149047329552357)
      ·
        refine ⟨1058053629027946374291067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5642952688149047329552357 1058053629027946374291067)
        ·
          refine ⟨1587080443541919561436601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1058053629027946374291067 1587080443541919561436601)
          ·
            refine ⟨1190310332656439671077451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1587080443541919561436601 1190310332656439671077451)
            ·
              refine ⟨1785465498984659506616177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1190310332656439671077451 1785465498984659506616177)
              ·
                refine ⟨1339099124238494629962133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1785465498984659506616177 1339099124238494629962133)
                ·
                  refine ⟨62770271448679435779475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1339099124238494629962133 62770271448679435779475)
                  ·
                    rfl

theorem cell22_550101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 6].length) (baseStart_550101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_550101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_550101 prefixEnd_550101 := by exact prefixLift 550101
  have htrace : WordTrace (prefixWord ++ tailWord_550101) baseStart_550101 baseEnd_550101 := by
    simpa [prefixWord, tailWord_550101, baseEnd_550101] using wordTrace_append hprefix tailTrace_550101
  have hstable : (prefixWord ++ tailWord_550101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550101).length < 2 ^ (prefixWord ++ tailWord_550101).sum := by decide
  have hdescent : baseEnd_550101 < baseStart_550101 := by decide
  rcases family_descends (prefixWord ++ tailWord_550101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550161 : List Nat := [1, 2, 2, 1, 1, 4, 1, 4, 3, 3]
def baseStart_550161 : Nat := 118140960795 + 550161 * 2 ^ 59
def prefixEnd_550161 : Nat := 4983230072969 + 3 ^ 40 * 550161 * 2
def baseEnd_550161 : Nat := 188331353572218150838241

theorem tailTrace_550161 : CollatzResearch.WordTrace tailWord_550161 prefixEnd_550161 188331353572218150838241 := by
  unfold tailWord_550161
  simp only [CollatzResearch.WordTrace]
  refine ⟨20066020159868131863370337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13377346773245421242246891 20066020159868131863370337)
  ·
    refine ⟨15049515119901098897527753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20066020159868131863370337 15049515119901098897527753)
    ·
      refine ⟨11287136339925824173145815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15049515119901098897527753 11287136339925824173145815)
      ·
        refine ⟨16930704509888736259718723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11287136339925824173145815 16930704509888736259718723)
        ·
          refine ⟨25396056764833104389578085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16930704509888736259718723 25396056764833104389578085)
          ·
            refine ⟨4761760643406207073045891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25396056764833104389578085 4761760643406207073045891)
            ·
              refine ⟨7142640965109310609568837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4761760643406207073045891 7142640965109310609568837)
              ·
                refine ⟨1339245180957995739294157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7142640965109310609568837 1339245180957995739294157)
                ·
                  refine ⟨502216942859248402235309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1339245180957995739294157 502216942859248402235309)
                  ·
                    refine ⟨188331353572218150838241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 502216942859248402235309 188331353572218150838241)
                    ·
                      rfl

theorem cell22_550161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3, 3].length) (baseStart_550161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_550161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_550161 prefixEnd_550161 := by exact prefixLift 550161
  have htrace : WordTrace (prefixWord ++ tailWord_550161) baseStart_550161 baseEnd_550161 := by
    simpa [prefixWord, tailWord_550161, baseEnd_550161] using wordTrace_append hprefix tailTrace_550161
  have hstable : (prefixWord ++ tailWord_550161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550161).length < 2 ^ (prefixWord ++ tailWord_550161).sum := by decide
  have hdescent : baseEnd_550161 < baseStart_550161 := by decide
  rcases family_descends (prefixWord ++ tailWord_550161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550206 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 1, 7]
def baseStart_550206 : Nat := 118140960795 + 550206 * 2 ^ 59
def prefixEnd_550206 : Nat := 4983230072969 + 3 ^ 40 * 550206 * 2
def baseEnd_550206 : Nat := 188346757991853033463103

theorem tailTrace_550206 : CollatzResearch.WordTrace tailWord_550206 prefixEnd_550206 188346757991853033463103 := by
  unfold tailWord_550206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2508457680588138068594809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13378440963136736365838981 2508457680588138068594809)
  ·
    refine ⟨1881343260441103551446107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2508457680588138068594809 1881343260441103551446107)
    ·
      refine ⟨2822014890661655327169161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1881343260441103551446107 2822014890661655327169161)
      ·
        refine ⟨2116511167996241495376871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2822014890661655327169161 2116511167996241495376871)
        ·
          refine ⟨3174766751994362243065307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2116511167996241495376871 3174766751994362243065307)
          ·
            refine ⟨4762150127991543364597961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3174766751994362243065307 4762150127991543364597961)
            ·
              refine ⟨3571612595993657523448471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4762150127991543364597961 3571612595993657523448471)
              ·
                refine ⟨5357418893990486285172707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3571612595993657523448471 5357418893990486285172707)
                ·
                  refine ⟨8036128340985729427759061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5357418893990486285172707 8036128340985729427759061)
                  ·
                    refine ⟨188346757991853033463103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8036128340985729427759061 188346757991853033463103)
                    ·
                      rfl

theorem cell22_550206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_550206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_550206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_550206 prefixEnd_550206 := by exact prefixLift 550206
  have htrace : WordTrace (prefixWord ++ tailWord_550206) baseStart_550206 baseEnd_550206 := by
    simpa [prefixWord, tailWord_550206, baseEnd_550206] using wordTrace_append hprefix tailTrace_550206
  have hstable : (prefixWord ++ tailWord_550206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550206).length < 2 ^ (prefixWord ++ tailWord_550206).sum := by decide
  have hdescent : baseEnd_550206 < baseStart_550206 := by decide
  rcases family_descends (prefixWord ++ tailWord_550206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550268 : List Nat := [2, 2, 2, 1, 1, 1, 3, 5, 2, 3]
def baseStart_550268 : Nat := 118140960795 + 550268 * 2 ^ 59
def prefixEnd_550268 : Nat := 4983230072969 + 3 ^ 40 * 550268 * 2
def baseEnd_550268 : Nat := 188367981858905538412913

theorem tailTrace_550268 : CollatzResearch.WordTrace tailWord_550268 prefixEnd_550268 188367981858905538412913 := by
  unfold tailWord_550268
  simp only [CollatzResearch.WordTrace]
  refine ⟨10034961385240244568757729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13379948513653659425010305 10034961385240244568757729)
  ·
    refine ⟨7526221038930183426568297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10034961385240244568757729 7526221038930183426568297)
    ·
      refine ⟨5644665779197637569926223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7526221038930183426568297 5644665779197637569926223)
      ·
        refine ⟨8466998668796456354889335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5644665779197637569926223 8466998668796456354889335)
        ·
          refine ⟨12700498003194684532334003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8466998668796456354889335 12700498003194684532334003)
          ·
            refine ⟨19050747004792026798501005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12700498003194684532334003 19050747004792026798501005)
            ·
              refine ⟨7144030126797010049437877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19050747004792026798501005 7144030126797010049437877)
              ·
                refine ⟨669752824387219692134801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7144030126797010049437877 669752824387219692134801)
                ·
                  refine ⟨502314618290414769101101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 669752824387219692134801 502314618290414769101101)
                  ·
                    refine ⟨188367981858905538412913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 502314618290414769101101 188367981858905538412913)
                    ·
                      rfl

theorem cell22_550268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_550268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_550268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_550268 prefixEnd_550268 := by exact prefixLift 550268
  have htrace : WordTrace (prefixWord ++ tailWord_550268) baseStart_550268 baseEnd_550268 := by
    simpa [prefixWord, tailWord_550268, baseEnd_550268] using wordTrace_append hprefix tailTrace_550268
  have hstable : (prefixWord ++ tailWord_550268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550268).length < 2 ^ (prefixWord ++ tailWord_550268).sum := by decide
  have hdescent : baseEnd_550268 < baseStart_550268 := by decide
  rcases family_descends (prefixWord ++ tailWord_550268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550302 : List Nat := [4, 3, 1, 2, 2, 1, 1, 1, 4, 3]
def baseStart_550302 : Nat := 118140960795 + 550302 * 2 ^ 59
def prefixEnd_550302 : Nat := 4983230072969 + 3 ^ 40 * 550302 * 2
def baseEnd_550302 : Nat := 188379620753740783062809

theorem tailTrace_550302 : CollatzResearch.WordTrace tailWord_550302 prefixEnd_550302 188379620753740783062809 := by
  unfold tailWord_550302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2508895356544664118031645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13380775234904875296168773 2508895356544664118031645)
  ·
    refine ⟨940835758704249044261867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2508895356544664118031645 940835758704249044261867)
    ·
      refine ⟨1411253638056373566392801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 940835758704249044261867 1411253638056373566392801)
      ·
        refine ⟨1058440228542280174794601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1411253638056373566392801 1058440228542280174794601)
        ·
          refine ⟨793830171406710131095951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1058440228542280174794601 793830171406710131095951)
          ·
            refine ⟨1190745257110065196643927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 793830171406710131095951 1190745257110065196643927)
            ·
              refine ⟨1786117885665097794965891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1190745257110065196643927 1786117885665097794965891)
              ·
                refine ⟨2679176828497646692448837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1786117885665097794965891 2679176828497646692448837)
                ·
                  refine ⟨502345655343308754834157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2679176828497646692448837 502345655343308754834157)
                  ·
                    refine ⟨188379620753740783062809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 502345655343308754834157 188379620753740783062809)
                    ·
                      rfl

theorem cell22_550302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_550302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_550302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_550302 prefixEnd_550302 := by exact prefixLift 550302
  have htrace : WordTrace (prefixWord ++ tailWord_550302) baseStart_550302 baseEnd_550302 := by
    simpa [prefixWord, tailWord_550302, baseEnd_550302] using wordTrace_append hprefix tailTrace_550302
  have hstable : (prefixWord ++ tailWord_550302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550302).length < 2 ^ (prefixWord ++ tailWord_550302).sum := by decide
  have hdescent : baseEnd_550302 < baseStart_550302 := by decide
  rcases family_descends (prefixWord ++ tailWord_550302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550332 : List Nat := [2, 2, 2, 4, 3, 1, 2, 6]
def baseStart_550332 : Nat := 118140960795 + 550332 * 2 ^ 59
def prefixEnd_550332 : Nat := 4983230072969 + 3 ^ 40 * 550332 * 2
def baseEnd_550332 : Nat := 20932210040758967201413

theorem tailTrace_550332 : CollatzResearch.WordTrace tailWord_550332 prefixEnd_550332 20932210040758967201413 := by
  unfold tailWord_550332
  simp only [CollatzResearch.WordTrace]
  refine ⟨10036128521124314033922625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13381504694832418711896833 10036128521124314033922625)
  ·
    refine ⟨7527096390843235525441969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10036128521124314033922625 7527096390843235525441969)
    ·
      refine ⟨5645322293132426644081477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7527096390843235525441969 5645322293132426644081477)
      ·
        refine ⟨1058497929962329995765277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5645322293132426644081477 1058497929962329995765277)
        ·
          refine ⟨396936723735873748411979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1058497929962329995765277 396936723735873748411979)
          ·
            refine ⟨595405085603810622617969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396936723735873748411979 595405085603810622617969)
            ·
              refine ⟨446553814202857966963477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 595405085603810622617969 446553814202857966963477)
              ·
                refine ⟨20932210040758967201413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 446553814202857966963477 20932210040758967201413)
                ·
                  rfl

theorem cell22_550332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 6].length) (baseStart_550332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_550332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_550332 prefixEnd_550332 := by exact prefixLift 550332
  have htrace : WordTrace (prefixWord ++ tailWord_550332) baseStart_550332 baseEnd_550332 := by
    simpa [prefixWord, tailWord_550332, baseEnd_550332] using wordTrace_append hprefix tailTrace_550332
  have hstable : (prefixWord ++ tailWord_550332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550332).length < 2 ^ (prefixWord ++ tailWord_550332).sum := by decide
  have hdescent : baseEnd_550332 < baseStart_550332 := by decide
  rcases family_descends (prefixWord ++ tailWord_550332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550338 : List Nat := [3, 5, 2, 1, 1, 2, 1, 3, 4]
def baseStart_550338 : Nat := 118140960795 + 550338 * 2 ^ 59
def prefixEnd_550338 : Nat := 4983230072969 + 3 ^ 40 * 550338 * 2
def baseEnd_550338 : Nat := 62797314763149563054233

theorem tailTrace_550338 : CollatzResearch.WordTrace tailWord_550338 prefixEnd_550338 62797314763149563054233 := by
  unfold tailWord_550338
  simp only [CollatzResearch.WordTrace]
  refine ⟨5018118970056722773140917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13381650586817927395042445 5018118970056722773140917)
  ·
    refine ⟨470448653442817759981961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5018118970056722773140917 470448653442817759981961)
    ·
      refine ⟨352836490082113319986471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 470448653442817759981961 352836490082113319986471)
      ·
        refine ⟨529254735123169979979707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352836490082113319986471 529254735123169979979707)
        ·
          refine ⟨793882102684754969969561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529254735123169979979707 793882102684754969969561)
          ·
            refine ⟨595411577013566227477171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 793882102684754969969561 595411577013566227477171)
            ·
              refine ⟨893117365520349341215757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595411577013566227477171 893117365520349341215757)
              ·
                refine ⟨334919012070131002955909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 893117365520349341215757 334919012070131002955909)
                ·
                  refine ⟨62797314763149563054233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 334919012070131002955909 62797314763149563054233)
                  ·
                    rfl

theorem cell22_550338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_550338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_550338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_550338 prefixEnd_550338 := by exact prefixLift 550338
  have htrace : WordTrace (prefixWord ++ tailWord_550338) baseStart_550338 baseEnd_550338 := by
    simpa [prefixWord, tailWord_550338, baseEnd_550338] using wordTrace_append hprefix tailTrace_550338
  have hstable : (prefixWord ++ tailWord_550338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550338).length < 2 ^ (prefixWord ++ tailWord_550338).sum := by decide
  have hdescent : baseEnd_550338 < baseStart_550338 := by decide
  rcases family_descends (prefixWord ++ tailWord_550338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550390 : List Nat := [5, 1, 1, 1, 2, 3, 1, 1, 3, 4]
def baseStart_550390 : Nat := 118140960795 + 550390 * 2 ^ 59
def prefixEnd_550390 : Nat := 4983230072969 + 3 ^ 40 * 550390 * 2
def baseEnd_550390 : Nat := 188409744952137886862539

theorem tailTrace_550390 : CollatzResearch.WordTrace tailWord_550390 prefixEnd_550390 188409744952137886862539 := by
  unfold tailWord_550390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1254648279752406498341039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13382914984025669315637749 1254648279752406498341039)
  ·
    refine ⟨1881972419628609747511559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1254648279752406498341039 1881972419628609747511559)
    ·
      refine ⟨2822958629442914621267339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1881972419628609747511559 2822958629442914621267339)
      ·
        refine ⟨4234437944164371931901009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2822958629442914621267339 4234437944164371931901009)
        ·
          refine ⟨3175828458123278948925757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4234437944164371931901009 3175828458123278948925757)
          ·
            refine ⟨1190935671796229605847159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3175828458123278948925757 1190935671796229605847159)
            ·
              refine ⟨1786403507694344408770739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1190935671796229605847159 1786403507694344408770739)
              ·
                refine ⟨2679605261541516613156109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1786403507694344408770739 2679605261541516613156109)
                ·
                  refine ⟨1004851973078068729933541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2679605261541516613156109 1004851973078068729933541)
                  ·
                    refine ⟨188409744952137886862539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1004851973078068729933541 188409744952137886862539)
                    ·
                      rfl

theorem cell22_550390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_550390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_550390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_550390 prefixEnd_550390 := by exact prefixLift 550390
  have htrace : WordTrace (prefixWord ++ tailWord_550390) baseStart_550390 baseEnd_550390 := by
    simpa [prefixWord, tailWord_550390, baseEnd_550390] using wordTrace_append hprefix tailTrace_550390
  have hstable : (prefixWord ++ tailWord_550390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550390).length < 2 ^ (prefixWord ++ tailWord_550390).sum := by decide
  have hdescent : baseEnd_550390 < baseStart_550390 := by decide
  rcases family_descends (prefixWord ++ tailWord_550390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550403 : List Nat := [1, 1, 1, 3, 2, 1, 2, 4, 4, 3]
def baseStart_550403 : Nat := 118140960795 + 550403 * 2 ^ 59
def prefixEnd_550403 : Nat := 4983230072969 + 3 ^ 40 * 550403 * 2
def baseEnd_550403 : Nat := 188414195117810186287499

theorem tailTrace_550403 : CollatzResearch.WordTrace tailWord_550403 prefixEnd_550403 188414195117810186287499 := by
  unfold tailWord_550403
  simp only [CollatzResearch.WordTrace]
  refine ⟨20074846624991407193679863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13383231083327604795786575 20074846624991407193679863)
  ·
    refine ⟨30112269937487110790519795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20074846624991407193679863 30112269937487110790519795)
    ·
      refine ⟨45168404906230666185779693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30112269937487110790519795 45168404906230666185779693)
      ·
        refine ⟨16938151839836499819667385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45168404906230666185779693 16938151839836499819667385)
        ·
          refine ⟨12703613879877374864750539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16938151839836499819667385 12703613879877374864750539)
          ·
            refine ⟨19055420819816062297125809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12703613879877374864750539 19055420819816062297125809)
            ·
              refine ⟨14291565614862046722844357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19055420819816062297125809 14291565614862046722844357)
              ·
                refine ⟨2679668552786633760533317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14291565614862046722844357 2679668552786633760533317)
                ·
                  refine ⟨502437853647493830099997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2679668552786633760533317 502437853647493830099997)
                  ·
                    refine ⟨188414195117810186287499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 502437853647493830099997 188414195117810186287499)
                    ·
                      rfl

theorem cell22_550403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 4, 3].length) (baseStart_550403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_550403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_550403 prefixEnd_550403 := by exact prefixLift 550403
  have htrace : WordTrace (prefixWord ++ tailWord_550403) baseStart_550403 baseEnd_550403 := by
    simpa [prefixWord, tailWord_550403, baseEnd_550403] using wordTrace_append hprefix tailTrace_550403
  have hstable : (prefixWord ++ tailWord_550403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550403).length < 2 ^ (prefixWord ++ tailWord_550403).sum := by decide
  have hdescent : baseEnd_550403 < baseStart_550403 := by decide
  rcases family_descends (prefixWord ++ tailWord_550403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550407 : List Nat := [1, 1, 4, 3, 2, 2, 3, 1, 1, 4]
def baseStart_550407 : Nat := 118140960795 + 550407 * 2 ^ 59
def prefixEnd_550407 : Nat := 4983230072969 + 3 ^ 40 * 550407 * 2
def baseEnd_550407 : Nat := 188415564399555509187487

theorem tailTrace_550407 : CollatzResearch.WordTrace tailWord_550407 prefixEnd_550407 188415564399555509187487 := by
  unfold tailWord_550407
  simp only [CollatzResearch.WordTrace]
  refine ⟨20074992516976915876825475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13383328344651277251216983 20074992516976915876825475)
  ·
    refine ⟨30112488775465373815238213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20074992516976915876825475 30112488775465373815238213)
    ·
      refine ⟨5646091645399757590357165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30112488775465373815238213 5646091645399757590357165)
      ·
        refine ⟨2117284367024909096383937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5646091645399757590357165 2117284367024909096383937)
        ·
          refine ⟨1587963275268681822287953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2117284367024909096383937 1587963275268681822287953)
          ·
            refine ⟨1190972456451511366715965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1587963275268681822287953 1190972456451511366715965)
            ·
              refine ⟨446614671169316762518487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1190972456451511366715965 446614671169316762518487)
              ·
                refine ⟨669922006753975143777731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 446614671169316762518487 669922006753975143777731)
                ·
                  refine ⟨1004883010130962715666597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 669922006753975143777731 1004883010130962715666597)
                  ·
                    refine ⟨188415564399555509187487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1004883010130962715666597 188415564399555509187487)
                    ·
                      rfl

theorem cell22_550407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_550407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_550407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_550407 prefixEnd_550407 := by exact prefixLift 550407
  have htrace : WordTrace (prefixWord ++ tailWord_550407) baseStart_550407 baseEnd_550407 := by
    simpa [prefixWord, tailWord_550407, baseEnd_550407] using wordTrace_append hprefix tailTrace_550407
  have hstable : (prefixWord ++ tailWord_550407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550407).length < 2 ^ (prefixWord ++ tailWord_550407).sum := by decide
  have hdescent : baseEnd_550407 < baseStart_550407 := by decide
  rcases family_descends (prefixWord ++ tailWord_550407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550433 : List Nat := [1, 2, 3, 2, 2, 2, 3, 7]
def baseStart_550433 : Nat := 118140960795 + 550433 * 2 ^ 59
def prefixEnd_550433 : Nat := 4983230072969 + 3 ^ 40 * 550433 * 2
def baseEnd_550433 : Nat := 20936051636766678670823

theorem tailTrace_550433 : CollatzResearch.WordTrace tailWord_550433 prefixEnd_550433 20936051636766678670823 := by
  unfold tailWord_550433
  simp only [CollatzResearch.WordTrace]
  refine ⟨20075940814882722317271953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13383960543255148211514635 20075940814882722317271953)
  ·
    refine ⟨15056955611162041737953965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20075940814882722317271953 15056955611162041737953965)
    ·
      refine ⟨5646358354185765651732737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15056955611162041737953965 5646358354185765651732737)
      ·
        refine ⟨4234768765639324238799553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5646358354185765651732737 4234768765639324238799553)
        ·
          refine ⟨3176076574229493179099665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4234768765639324238799553 3176076574229493179099665)
          ·
            refine ⟨2382057430672119884324749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3176076574229493179099665 2382057430672119884324749)
            ·
              refine ⟨893271536502044956621781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2382057430672119884324749 893271536502044956621781)
              ·
                refine ⟨20936051636766678670823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 893271536502044956621781 20936051636766678670823)
                ·
                  rfl

theorem cell22_550433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 7].length) (baseStart_550433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_550433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_550433 prefixEnd_550433 := by exact prefixLift 550433
  have htrace : WordTrace (prefixWord ++ tailWord_550433) baseStart_550433 baseEnd_550433 := by
    simpa [prefixWord, tailWord_550433, baseEnd_550433] using wordTrace_append hprefix tailTrace_550433
  have hstable : (prefixWord ++ tailWord_550433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550433).length < 2 ^ (prefixWord ++ tailWord_550433).sum := by decide
  have hdescent : baseEnd_550433 < baseStart_550433 := by decide
  rcases family_descends (prefixWord ++ tailWord_550433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550465 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 5, 3]
def baseStart_550465 : Nat := 118140960795 + 550465 * 2 ^ 59
def prefixEnd_550465 : Nat := 4983230072969 + 3 ^ 40 * 550465 * 2
def baseEnd_550465 : Nat := 188435418984862691237309

theorem tailTrace_550465 : CollatzResearch.WordTrace tailWord_550465 prefixEnd_550465 188435418984862691237309 := by
  unfold tailWord_550465
  simp only [CollatzResearch.WordTrace]
  refine ⟨20077107950766791782436849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13384738633844527854957899 20077107950766791782436849)
  ·
    refine ⟨15057830963075093836827637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20077107950766791782436849 15057830963075093836827637)
    ·
      refine ⟨1411671652788290047202591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15057830963075093836827637 1411671652788290047202591)
      ·
        refine ⟨2117507479182435070803887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1411671652788290047202591 2117507479182435070803887)
        ·
          refine ⟨3176261218773652606205831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2117507479182435070803887 3176261218773652606205831)
          ·
            refine ⟨4764391828160478909308747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3176261218773652606205831 4764391828160478909308747)
            ·
              refine ⟨7146587742240718363963121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4764391828160478909308747 7146587742240718363963121)
              ·
                refine ⟨5359940806680538772972341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7146587742240718363963121 5359940806680538772972341)
                ·
                  refine ⟨502494450626300509966157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5359940806680538772972341 502494450626300509966157)
                  ·
                    refine ⟨188435418984862691237309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 502494450626300509966157 188435418984862691237309)
                    ·
                      rfl

theorem cell22_550465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_550465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_550465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_550465 prefixEnd_550465 := by exact prefixLift 550465
  have htrace : WordTrace (prefixWord ++ tailWord_550465) baseStart_550465 baseEnd_550465 := by
    simpa [prefixWord, tailWord_550465, baseEnd_550465] using wordTrace_append hprefix tailTrace_550465
  have hstable : (prefixWord ++ tailWord_550465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550465).length < 2 ^ (prefixWord ++ tailWord_550465).sum := by decide
  have hdescent : baseEnd_550465 < baseStart_550465 := by decide
  rcases family_descends (prefixWord ++ tailWord_550465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550482 : List Nat := [3, 2, 2, 1, 2, 3, 2, 1, 3, 3]
def baseStart_550482 : Nat := 118140960795 + 550482 * 2 ^ 59
def prefixEnd_550482 : Nat := 4983230072969 + 3 ^ 40 * 550482 * 2
def baseEnd_550482 : Nat := 188441238432280313562257

theorem tailTrace_550482 : CollatzResearch.WordTrace tailWord_550482 prefixEnd_550482 188441238432280313562257 := by
  unfold tailWord_550482
  simp only [CollatzResearch.WordTrace]
  refine ⟨5019431997926300921451425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13385151994470135790537133 5019431997926300921451425)
  ·
    refine ⟨3764573998444725691088569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5019431997926300921451425 3764573998444725691088569)
    ·
      refine ⟨2823430498833544268316427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3764573998444725691088569 2823430498833544268316427)
      ·
        refine ⟨4235145748250316402474641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2823430498833544268316427 4235145748250316402474641)
        ·
          refine ⟨3176359311187737301855981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4235145748250316402474641 3176359311187737301855981)
          ·
            refine ⟨1191134741695401488195993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3176359311187737301855981 1191134741695401488195993)
            ·
              refine ⟨893351056271551116146995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1191134741695401488195993 893351056271551116146995)
              ·
                refine ⟨1340026584407326674220493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 893351056271551116146995 1340026584407326674220493)
                ·
                  refine ⟨502509969152747502832685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1340026584407326674220493 502509969152747502832685)
                  ·
                    refine ⟨188441238432280313562257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 502509969152747502832685 188441238432280313562257)
                    ·
                      rfl

theorem cell22_550482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_550482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_550482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_550482 prefixEnd_550482 := by exact prefixLift 550482
  have htrace : WordTrace (prefixWord ++ tailWord_550482) baseStart_550482 baseEnd_550482 := by
    simpa [prefixWord, tailWord_550482, baseEnd_550482] using wordTrace_append hprefix tailTrace_550482
  have hstable : (prefixWord ++ tailWord_550482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550482).length < 2 ^ (prefixWord ++ tailWord_550482).sum := by decide
  have hdescent : baseEnd_550482 < baseStart_550482 := by decide
  rcases family_descends (prefixWord ++ tailWord_550482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550546 : List Nat := [3, 2, 3, 1, 4, 1, 2, 1, 5]
def baseStart_550546 : Nat := 118140960795 + 550546 * 2 ^ 59
def prefixEnd_550546 : Nat := 4983230072969 + 3 ^ 40 * 550546 * 2
def baseEnd_550546 : Nat := 62821048980068493320687

theorem tailTrace_550546 : CollatzResearch.WordTrace tailWord_550546 prefixEnd_550546 62821048980068493320687 := by
  unfold tailWord_550546
  simp only [CollatzResearch.WordTrace]
  refine ⟨5020015565868335654033873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13386708175648895077423661 5020015565868335654033873)
  ·
    refine ⟨3765011674401251740525405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5020015565868335654033873 3765011674401251740525405)
    ·
      refine ⟨1411879377900469402697027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3765011674401251740525405 1411879377900469402697027)
      ·
        refine ⟨2117819066850704104045541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1411879377900469402697027 2117819066850704104045541)
        ·
          refine ⟨397091075034507019508539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2117819066850704104045541 397091075034507019508539)
          ·
            refine ⟨595636612551760529262809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397091075034507019508539 595636612551760529262809)
            ·
              refine ⟨446727459413820396947107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 595636612551760529262809 446727459413820396947107)
              ·
                refine ⟨670091189120730595420661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 446727459413820396947107 670091189120730595420661)
                ·
                  refine ⟨62821048980068493320687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 670091189120730595420661 62821048980068493320687)
                  ·
                    rfl

theorem cell22_550546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_550546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_550546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_550546 prefixEnd_550546 := by exact prefixLift 550546
  have htrace : WordTrace (prefixWord ++ tailWord_550546) baseStart_550546 baseEnd_550546 := by
    simpa [prefixWord, tailWord_550546, baseEnd_550546] using wordTrace_append hprefix tailTrace_550546
  have hstable : (prefixWord ++ tailWord_550546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550546).length < 2 ^ (prefixWord ++ tailWord_550546).sum := by decide
  have hdescent : baseEnd_550546 < baseStart_550546 := by decide
  rcases family_descends (prefixWord ++ tailWord_550546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550553 : List Nat := [1, 2, 1, 2, 1, 2, 2, 4, 1, 6]
def baseStart_550553 : Nat := 118140960795 + 550553 * 2 ^ 59
def prefixEnd_550553 : Nat := 4983230072969 + 3 ^ 40 * 550553 * 2
def baseEnd_550553 : Nat := 188465543183259795037039

theorem tailTrace_550553 : CollatzResearch.WordTrace tailWord_550553 prefixEnd_550553 188465543183259795037039 := by
  unfold tailWord_550553
  simp only [CollatzResearch.WordTrace]
  refine ⟨20080317574447982811640313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13386878382965321874426875 20080317574447982811640313)
  ·
    refine ⟨15060238180835987108730235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20080317574447982811640313 15060238180835987108730235)
    ·
      refine ⟨22590357271253980663095353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15060238180835987108730235 22590357271253980663095353)
      ·
        refine ⟨16942767953440485497321515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22590357271253980663095353 16942767953440485497321515)
        ·
          refine ⟨25414151930160728245982273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16942767953440485497321515 25414151930160728245982273)
          ·
            refine ⟨19060613947620546184486705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25414151930160728245982273 19060613947620546184486705)
            ·
              refine ⟨14295460460715409638365029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19060613947620546184486705 14295460460715409638365029)
              ·
                refine ⟨2680398836384139307193443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14295460460715409638365029 2680398836384139307193443)
                ·
                  refine ⟨4020598254576208960790165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2680398836384139307193443 4020598254576208960790165)
                  ·
                    refine ⟨188465543183259795037039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4020598254576208960790165 188465543183259795037039)
                    ·
                      rfl

theorem cell22_550553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 6].length) (baseStart_550553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_550553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_550553 prefixEnd_550553 := by exact prefixLift 550553
  have htrace : WordTrace (prefixWord ++ tailWord_550553) baseStart_550553 baseEnd_550553 := by
    simpa [prefixWord, tailWord_550553, baseEnd_550553] using wordTrace_append hprefix tailTrace_550553
  have hstable : (prefixWord ++ tailWord_550553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550553).length < 2 ^ (prefixWord ++ tailWord_550553).sum := by decide
  have hdescent : baseEnd_550553 < baseStart_550553 := by decide
  rcases family_descends (prefixWord ++ tailWord_550553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550602 : List Nat := [3, 1, 2, 1, 5, 2, 1, 7]
def baseStart_550602 : Nat := 118140960795 + 550602 * 2 ^ 59
def prefixEnd_550602 : Nat := 4983230072969 + 3 ^ 40 * 550602 * 2
def baseEnd_550602 : Nat := 20942479653848888951321

theorem tailTrace_550602 : CollatzResearch.WordTrace tailWord_550602 prefixEnd_550602 20942479653848888951321 := by
  unfold tailWord_550602
  simp only [CollatzResearch.WordTrace]
  refine ⟨5020526187817616045043515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13388069834180309453449373 5020526187817616045043515)
  ·
    refine ⟨7530789281726424067565273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5020526187817616045043515 7530789281726424067565273)
    ·
      refine ⟨5648091961294818050673955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7530789281726424067565273 5648091961294818050673955)
      ·
        refine ⟨8472137941942227076010933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5648091961294818050673955 8472137941942227076010933)
        ·
          refine ⟨794262932057083788376025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8472137941942227076010933 794262932057083788376025)
          ·
            refine ⟨595697199042812841282019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 794262932057083788376025 595697199042812841282019)
            ·
              refine ⟨893545798564219261923029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595697199042812841282019 893545798564219261923029)
              ·
                refine ⟨20942479653848888951321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 893545798564219261923029 20942479653848888951321)
                ·
                  rfl

theorem cell22_550602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 7].length) (baseStart_550602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_550602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_550602 prefixEnd_550602 := by exact prefixLift 550602
  have htrace : WordTrace (prefixWord ++ tailWord_550602) baseStart_550602 baseEnd_550602 := by
    simpa [prefixWord, tailWord_550602, baseEnd_550602] using wordTrace_append hprefix tailTrace_550602
  have hstable : (prefixWord ++ tailWord_550602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550602).length < 2 ^ (prefixWord ++ tailWord_550602).sum := by decide
  have hdescent : baseEnd_550602 < baseStart_550602 := by decide
  rcases family_descends (prefixWord ++ tailWord_550602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550617 : List Nat := [1, 2, 1, 2, 3, 4, 1, 2, 3, 3]
def baseStart_550617 : Nat := 118140960795 + 550617 * 2 ^ 59
def prefixEnd_550617 : Nat := 4983230072969 + 3 ^ 40 * 550617 * 2
def baseEnd_550617 : Nat := 188487451691184961436843

theorem tailTrace_550617 : CollatzResearch.WordTrace tailWord_550617 prefixEnd_550617 188487451691184961436843 := by
  unfold tailWord_550617
  simp only [CollatzResearch.WordTrace]
  refine ⟨20082651846216121741970105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13388434564144081161313403 20082651846216121741970105)
  ·
    refine ⟨15061988884662091306477579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20082651846216121741970105 15061988884662091306477579)
    ·
      refine ⟨22592983326993136959716369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15061988884662091306477579 22592983326993136959716369)
      ·
        refine ⟨16944737495244852719787277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22592983326993136959716369 16944737495244852719787277)
        ·
          refine ⟨6354276560716819769920229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16944737495244852719787277 6354276560716819769920229)
          ·
            refine ⟨1191426855134403706860043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6354276560716819769920229 1191426855134403706860043)
            ·
              refine ⟨1787140282701605560290065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1191426855134403706860043 1787140282701605560290065)
              ·
                refine ⟨1340355212026204170217549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1787140282701605560290065 1340355212026204170217549)
                ·
                  refine ⟨502633204509826563831581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1340355212026204170217549 502633204509826563831581)
                  ·
                    refine ⟨188487451691184961436843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 502633204509826563831581 188487451691184961436843)
                    ·
                      rfl

theorem cell22_550617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 3, 3].length) (baseStart_550617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_550617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_550617 prefixEnd_550617 := by exact prefixLift 550617
  have htrace : WordTrace (prefixWord ++ tailWord_550617) baseStart_550617 baseEnd_550617 := by
    simpa [prefixWord, tailWord_550617, baseEnd_550617] using wordTrace_append hprefix tailTrace_550617
  have hstable : (prefixWord ++ tailWord_550617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550617).length < 2 ^ (prefixWord ++ tailWord_550617).sum := by decide
  have hdescent : baseEnd_550617 < baseStart_550617 := by decide
  rcases family_descends (prefixWord ++ tailWord_550617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550621 : List Nat := [1, 4, 3, 3, 1, 2, 1, 1, 2, 4]
def baseStart_550621 : Nat := 118140960795 + 550621 * 2 ^ 59
def prefixEnd_550621 : Nat := 4983230072969 + 3 ^ 40 * 550621 * 2
def baseEnd_550621 : Nat := 188488820972930284336831

theorem tailTrace_550621 : CollatzResearch.WordTrace tailWord_550621 prefixEnd_550621 188488820972930284336831 := by
  unfold tailWord_550621
  simp only [CollatzResearch.WordTrace]
  refine ⟨20082797738201630425115717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13388531825467753616743811 20082797738201630425115717)
  ·
    refine ⟨3765524575912805704709197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20082797738201630425115717 3765524575912805704709197)
    ·
      refine ⟨1412071715967302139265949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3765524575912805704709197 1412071715967302139265949)
      ·
        refine ⟨529526893487738302224731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1412071715967302139265949 529526893487738302224731)
        ·
          refine ⟨794290340231607453337097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529526893487738302224731 794290340231607453337097)
          ·
            refine ⟨595717755173705590002823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 794290340231607453337097 595717755173705590002823)
            ·
              refine ⟨893576632760558385004235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595717755173705590002823 893576632760558385004235)
              ·
                refine ⟨1340364949140837577506353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 893576632760558385004235 1340364949140837577506353)
                ·
                  refine ⟨1005273711855628183129765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1340364949140837577506353 1005273711855628183129765)
                  ·
                    refine ⟨188488820972930284336831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1005273711855628183129765 188488820972930284336831)
                    ·
                      rfl

theorem cell22_550621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_550621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_550621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_550621 prefixEnd_550621 := by exact prefixLift 550621
  have htrace : WordTrace (prefixWord ++ tailWord_550621) baseStart_550621 baseEnd_550621 := by
    simpa [prefixWord, tailWord_550621, baseEnd_550621] using wordTrace_append hprefix tailTrace_550621
  have hstable : (prefixWord ++ tailWord_550621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550621).length < 2 ^ (prefixWord ++ tailWord_550621).sum := by decide
  have hdescent : baseEnd_550621 < baseStart_550621 := by decide
  rcases family_descends (prefixWord ++ tailWord_550621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550634 : List Nat := [3, 1, 3, 1, 1, 1, 3, 5, 1, 3]
def baseStart_550634 : Nat := 118140960795 + 550634 * 2 ^ 59
def prefixEnd_550634 : Nat := 4983230072969 + 3 ^ 40 * 550634 * 2
def baseEnd_550634 : Nat := 188493271138602583761791

theorem tailTrace_550634 : CollatzResearch.WordTrace tailWord_550634 prefixEnd_550634 188493271138602583761791 := by
  unfold tailWord_550634
  simp only [CollatzResearch.WordTrace]
  refine ⟨5020817971788633411334739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13388847924769689096892637 5020817971788633411334739)
  ·
    refine ⟨7531226957682950117002109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5020817971788633411334739 7531226957682950117002109)
    ·
      refine ⟨2824210109131106293875791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7531226957682950117002109 2824210109131106293875791)
      ·
        refine ⟨4236315163696659440813687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2824210109131106293875791 4236315163696659440813687)
        ·
          refine ⟨6354472745544989161220531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4236315163696659440813687 6354472745544989161220531)
          ·
            refine ⟨9531709118317483741830797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6354472745544989161220531 9531709118317483741830797)
            ·
              refine ⟨3574390919369056403186549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9531709118317483741830797 3574390919369056403186549)
              ·
                refine ⟨335099148690849037798739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3574390919369056403186549 335099148690849037798739)
                ·
                  refine ⟨502648723036273556698109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 335099148690849037798739 502648723036273556698109)
                  ·
                    refine ⟨188493271138602583761791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 502648723036273556698109 188493271138602583761791)
                    ·
                      rfl

theorem cell22_550634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_550634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_550634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_550634 prefixEnd_550634 := by exact prefixLift 550634
  have htrace : WordTrace (prefixWord ++ tailWord_550634) baseStart_550634 baseEnd_550634 := by
    simpa [prefixWord, tailWord_550634, baseEnd_550634] using wordTrace_append hprefix tailTrace_550634
  have hstable : (prefixWord ++ tailWord_550634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550634).length < 2 ^ (prefixWord ++ tailWord_550634).sum := by decide
  have hdescent : baseEnd_550634 < baseStart_550634 := by decide
  rcases family_descends (prefixWord ++ tailWord_550634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550677 : List Nat := [1, 3, 2, 1, 2, 3, 1, 4, 1, 4]
def baseStart_550677 : Nat := 118140960795 + 550677 * 2 ^ 59
def prefixEnd_550677 : Nat := 4983230072969 + 3 ^ 40 * 550677 * 2
def baseEnd_550677 : Nat := 188507990917364804936659

theorem tailTrace_550677 : CollatzResearch.WordTrace tailWord_550677 prefixEnd_550677 188507990917364804936659 := by
  unfold tailWord_550677
  simp only [CollatzResearch.WordTrace]
  refine ⟨20084840225998751989154285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13389893483999167992769523 20084840225998751989154285)
  ·
    refine ⟨7531815084749531995932857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20084840225998751989154285 7531815084749531995932857)
    ·
      refine ⟨5648861313562148996949643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7531815084749531995932857 5648861313562148996949643)
      ·
        refine ⟨8473291970343223495424465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5648861313562148996949643 8473291970343223495424465)
        ·
          refine ⟨6354968977757417621568349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8473291970343223495424465 6354968977757417621568349)
          ·
            refine ⟨2383113366659031608088131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6354968977757417621568349 2383113366659031608088131)
            ·
              refine ⟨3574670049988547412132197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2383113366659031608088131 3574670049988547412132197)
              ·
                refine ⟨670250634372852639774787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3574670049988547412132197 670250634372852639774787)
                ·
                  refine ⟨1005375951559278959662181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 670250634372852639774787 1005375951559278959662181)
                  ·
                    refine ⟨188507990917364804936659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1005375951559278959662181 188507990917364804936659)
                    ·
                      rfl

theorem cell22_550677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_550677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_550677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_550677 prefixEnd_550677 := by exact prefixLift 550677
  have htrace : WordTrace (prefixWord ++ tailWord_550677) baseStart_550677 baseEnd_550677 := by
    simpa [prefixWord, tailWord_550677, baseEnd_550677] using wordTrace_append hprefix tailTrace_550677
  have hstable : (prefixWord ++ tailWord_550677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550677).length < 2 ^ (prefixWord ++ tailWord_550677).sum := by decide
  have hdescent : baseEnd_550677 < baseStart_550677 := by decide
  rcases family_descends (prefixWord ++ tailWord_550677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550709 : List Nat := [1, 3, 3, 1, 4, 2, 1, 1, 6]
def baseStart_550709 : Nat := 118140960795 + 550709 * 2 ^ 59
def prefixEnd_550709 : Nat := 4983230072969 + 3 ^ 40 * 550709 * 2
def baseEnd_550709 : Nat := 62839648390442462712187

theorem tailTrace_550709 : CollatzResearch.WordTrace tailWord_550709 prefixEnd_550709 62839648390442462712187 := by
  unfold tailWord_550709
  simp only [CollatzResearch.WordTrace]
  refine ⟨20086007361882821454319181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13390671574588547636212787 20086007361882821454319181)
  ·
    refine ⟨7532252760706058045369693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20086007361882821454319181 7532252760706058045369693)
    ·
      refine ⟨2824594785264771767013635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7532252760706058045369693 2824594785264771767013635)
      ·
        refine ⟨4236892177897157650520453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2824594785264771767013635 4236892177897157650520453)
        ·
          refine ⟨794417283355717059472585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4236892177897157650520453 794417283355717059472585)
          ·
            refine ⟨595812962516787794604439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 794417283355717059472585 595812962516787794604439)
            ·
              refine ⟨893719443775181691906659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595812962516787794604439 893719443775181691906659)
              ·
                refine ⟨1340579165662772537859989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 893719443775181691906659 1340579165662772537859989)
                ·
                  refine ⟨62839648390442462712187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1340579165662772537859989 62839648390442462712187)
                  ·
                    rfl

theorem cell22_550709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 6].length) (baseStart_550709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_550709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_550709 prefixEnd_550709 := by exact prefixLift 550709
  have htrace : WordTrace (prefixWord ++ tailWord_550709) baseStart_550709 baseEnd_550709 := by
    simpa [prefixWord, tailWord_550709, baseEnd_550709] using wordTrace_append hprefix tailTrace_550709
  have hstable : (prefixWord ++ tailWord_550709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550709).length < 2 ^ (prefixWord ++ tailWord_550709).sum := by decide
  have hdescent : baseEnd_550709 < baseStart_550709 := by decide
  rcases family_descends (prefixWord ++ tailWord_550709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550842 : List Nat := [3, 1, 1, 1, 2, 1, 2, 5, 1, 5]
def baseStart_550842 : Nat := 118140960795 + 550842 * 2 ^ 59
def prefixEnd_550842 : Nat := 4983230072969 + 3 ^ 40 * 550842 * 2
def baseEnd_550842 : Nat := 188564473789359374561153

theorem tailTrace_550842 : CollatzResearch.WordTrace tailWord_550842 prefixEnd_550842 188564473789359374561153 := by
  unfold tailWord_550842
  simp only [CollatzResearch.WordTrace]
  refine ⟨5022714567600246292227695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13393905513600656779273853 5022714567600246292227695)
  ·
    refine ⟨7534071851400369438341543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5022714567600246292227695 7534071851400369438341543)
    ·
      refine ⟨11301107777100554157512315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7534071851400369438341543 11301107777100554157512315)
      ·
        refine ⟨16951661665650831236268473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11301107777100554157512315 16951661665650831236268473)
        ·
          refine ⟨12713746249238123427201355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16951661665650831236268473 12713746249238123427201355)
          ·
            refine ⟨19070619373857185140802033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12713746249238123427201355 19070619373857185140802033)
            ·
              refine ⟨14302964530392888855601525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19070619373857185140802033 14302964530392888855601525)
              ·
                refine ⟨1340902924724333330212643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14302964530392888855601525 1340902924724333330212643)
                ·
                  refine ⟨2011354387086499995318965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1340902924724333330212643 2011354387086499995318965)
                  ·
                    refine ⟨188564473789359374561153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2011354387086499995318965 188564473789359374561153)
                    ·
                      rfl

theorem cell22_550842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_550842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_550842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_550842 prefixEnd_550842 := by exact prefixLift 550842
  have htrace : WordTrace (prefixWord ++ tailWord_550842) baseStart_550842 baseEnd_550842 := by
    simpa [prefixWord, tailWord_550842, baseEnd_550842] using wordTrace_append hprefix tailTrace_550842
  have hstable : (prefixWord ++ tailWord_550842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550842).length < 2 ^ (prefixWord ++ tailWord_550842).sum := by decide
  have hdescent : baseEnd_550842 < baseStart_550842 := by decide
  rcases family_descends (prefixWord ++ tailWord_550842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550846 : List Nat := [4, 2, 1, 1, 1, 4, 2, 2, 1, 4]
def baseStart_550846 : Nat := 118140960795 + 550846 * 2 ^ 59
def prefixEnd_550846 : Nat := 4983230072969 + 3 ^ 40 * 550846 * 2
def baseEnd_550846 : Nat := 188565843071104697461141

theorem tailTrace_550846 : CollatzResearch.WordTrace tailWord_550846 prefixEnd_550846 188565843071104697461141 := by
  unfold tailWord_550846
  simp only [CollatzResearch.WordTrace]
  refine ⟨2511375520298311731507049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13394002774924329234704261 2511375520298311731507049)
  ·
    refine ⟨1883531640223733798630287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2511375520298311731507049 1883531640223733798630287)
    ·
      refine ⟨2825297460335600697945431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1883531640223733798630287 2825297460335600697945431)
      ·
        refine ⟨4237946190503401046918147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2825297460335600697945431 4237946190503401046918147)
        ·
          refine ⟨6356919285755101570377221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4237946190503401046918147 6356919285755101570377221)
          ·
            refine ⟨1191922366079081544445729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6356919285755101570377221 1191922366079081544445729)
            ·
              refine ⟨893941774559311158334297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1191922366079081544445729 893941774559311158334297)
              ·
                refine ⟨670456330919483368750723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 893941774559311158334297 670456330919483368750723)
                ·
                  refine ⟨1005684496379225053126085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 670456330919483368750723 1005684496379225053126085)
                  ·
                    refine ⟨188565843071104697461141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1005684496379225053126085 188565843071104697461141)
                    ·
                      rfl

theorem cell22_550846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_550846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_550846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_550846 prefixEnd_550846 := by exact prefixLift 550846
  have htrace : WordTrace (prefixWord ++ tailWord_550846) baseStart_550846 baseEnd_550846 := by
    simpa [prefixWord, tailWord_550846, baseEnd_550846] using wordTrace_append hprefix tailTrace_550846
  have hstable : (prefixWord ++ tailWord_550846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550846).length < 2 ^ (prefixWord ++ tailWord_550846).sum := by decide
  have hdescent : baseEnd_550846 < baseStart_550846 := by decide
  rcases family_descends (prefixWord ++ tailWord_550846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550904 : List Nat := [2, 1, 2, 1, 1, 3, 2, 4, 3, 3]
def baseStart_550904 : Nat := 118140960795 + 550904 * 2 ^ 59
def prefixEnd_550904 : Nat := 4983230072969 + 3 ^ 40 * 550904 * 2
def baseEnd_550904 : Nat := 188585697656411879510963

theorem tailTrace_550904 : CollatzResearch.WordTrace tailWord_550904 prefixEnd_550904 188585697656411879510963 := by
  unfold tailWord_550904
  simp only [CollatzResearch.WordTrace]
  refine ⟨10046559798088184878833883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13395413064117579838445177 10046559798088184878833883)
  ·
    refine ⟨15069839697132277318250825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10046559798088184878833883 15069839697132277318250825)
    ·
      refine ⟨11302379772849207988688119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15069839697132277318250825 11302379772849207988688119)
      ·
        refine ⟨16953569659273811983032179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11302379772849207988688119 16953569659273811983032179)
        ·
          refine ⟨25430354488910717974548269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16953569659273811983032179 25430354488910717974548269)
          ·
            refine ⟨9536382933341519240455601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25430354488910717974548269 9536382933341519240455601)
            ·
              refine ⟨7152287200006139430341701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9536382933341519240455601 7152287200006139430341701)
              ·
                refine ⟨1341053850001151143189069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7152287200006139430341701 1341053850001151143189069)
                ·
                  refine ⟨502895193750431678695901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1341053850001151143189069 502895193750431678695901)
                  ·
                    refine ⟨188585697656411879510963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 502895193750431678695901 188585697656411879510963)
                    ·
                      rfl

theorem cell22_550904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 3, 3].length) (baseStart_550904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_550904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_550904 prefixEnd_550904 := by exact prefixLift 550904
  have htrace : WordTrace (prefixWord ++ tailWord_550904) baseStart_550904 baseEnd_550904 := by
    simpa [prefixWord, tailWord_550904, baseEnd_550904] using wordTrace_append hprefix tailTrace_550904
  have hstable : (prefixWord ++ tailWord_550904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550904).length < 2 ^ (prefixWord ++ tailWord_550904).sum := by decide
  have hdescent : baseEnd_550904 < baseStart_550904 := by decide
  rcases family_descends (prefixWord ++ tailWord_550904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550938 : List Nat := [3, 1, 1, 3, 1, 4, 1, 4, 1, 3]
def baseStart_550938 : Nat := 118140960795 + 550938 * 2 ^ 59
def prefixEnd_550938 : Nat := 4983230072969 + 3 ^ 40 * 550938 * 2
def baseEnd_550938 : Nat := 188597336551247124160859

theorem tailTrace_550938 : CollatzResearch.WordTrace tailWord_550938 prefixEnd_550938 188597336551247124160859 := by
  unfold tailWord_550938
  simp only [CollatzResearch.WordTrace]
  refine ⟨5023589919513298391101367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13396239785368795709603645 5023589919513298391101367)
  ·
    refine ⟨7535384879269947586652051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5023589919513298391101367 7535384879269947586652051)
    ·
      refine ⟨11303077318904921379978077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7535384879269947586652051 11303077318904921379978077)
      ·
        refine ⟨4238653994589345517491779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11303077318904921379978077 4238653994589345517491779)
        ·
          refine ⟨6357980991884018276237669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4238653994589345517491779 6357980991884018276237669)
          ·
            refine ⟨1192121435978253426794563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6357980991884018276237669 1192121435978253426794563)
            ·
              refine ⟨1788182153967380140191845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1192121435978253426794563 1788182153967380140191845)
              ·
                refine ⟨335284153868883776285971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1788182153967380140191845 335284153868883776285971)
                ·
                  refine ⟨502926230803325664428957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 335284153868883776285971 502926230803325664428957)
                  ·
                    refine ⟨188597336551247124160859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 502926230803325664428957 188597336551247124160859)
                    ·
                      rfl

theorem cell22_550938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 4, 1, 3].length) (baseStart_550938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_550938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_550938 prefixEnd_550938 := by exact prefixLift 550938
  have htrace : WordTrace (prefixWord ++ tailWord_550938) baseStart_550938 baseEnd_550938 := by
    simpa [prefixWord, tailWord_550938, baseEnd_550938] using wordTrace_append hprefix tailTrace_550938
  have hstable : (prefixWord ++ tailWord_550938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550938).length < 2 ^ (prefixWord ++ tailWord_550938).sum := by decide
  have hdescent : baseEnd_550938 < baseStart_550938 := by decide
  rcases family_descends (prefixWord ++ tailWord_550938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550949 : List Nat := [1, 3, 1, 2, 2, 4, 1, 1, 2, 5]
def baseStart_550949 : Nat := 118140960795 + 550949 * 2 ^ 59
def prefixEnd_550949 : Nat := 4983230072969 + 3 ^ 40 * 550949 * 2
def baseEnd_550949 : Nat := 188601102076046762135825

theorem tailTrace_550949 : CollatzResearch.WordTrace tailWord_550949 prefixEnd_550949 188601102076046762135825 := by
  unfold tailWord_550949
  simp only [CollatzResearch.WordTrace]
  refine ⟨20094760881013342443055901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13396507254008894962037267 20094760881013342443055901)
  ·
    refine ⟨7535535330380003416145963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20094760881013342443055901 7535535330380003416145963)
    ·
      refine ⟨11303302995570005124218945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7535535330380003416145963 11303302995570005124218945)
      ·
        refine ⟨8477477246677503843164209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11303302995570005124218945 8477477246677503843164209)
        ·
          refine ⟨6358107935008127882373157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8477477246677503843164209 6358107935008127882373157)
          ·
            refine ⟨1192145237814023977944967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6358107935008127882373157 1192145237814023977944967)
            ·
              refine ⟨1788217856721035966917451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1192145237814023977944967 1788217856721035966917451)
              ·
                refine ⟨2682326785081553950376177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1788217856721035966917451 2682326785081553950376177)
                ·
                  refine ⟨2011745088811165462782133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2682326785081553950376177 2011745088811165462782133)
                  ·
                    refine ⟨188601102076046762135825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2011745088811165462782133 188601102076046762135825)
                    ·
                      rfl

theorem cell22_550949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_550949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_550949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_550949 prefixEnd_550949 := by exact prefixLift 550949
  have htrace : WordTrace (prefixWord ++ tailWord_550949) baseStart_550949 baseEnd_550949 := by
    simpa [prefixWord, tailWord_550949, baseEnd_550949] using wordTrace_append hprefix tailTrace_550949
  have hstable : (prefixWord ++ tailWord_550949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550949).length < 2 ^ (prefixWord ++ tailWord_550949).sum := by decide
  have hdescent : baseEnd_550949 < baseStart_550949 := by decide
  rcases family_descends (prefixWord ++ tailWord_550949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551011 : List Nat := [1, 1, 1, 5, 1, 1, 2, 5, 2, 3]
def baseStart_551011 : Nat := 118140960795 + 551011 * 2 ^ 59
def prefixEnd_551011 : Nat := 4983230072969 + 3 ^ 40 * 551011 * 2
def baseEnd_551011 : Nat := 188622325943099267085635

theorem tailTrace_551011 : CollatzResearch.WordTrace tailWord_551011 prefixEnd_551011 188622325943099267085635 := by
  unfold tailWord_551011
  simp only [CollatzResearch.WordTrace]
  refine ⟨20097022206788727031812887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13398014804525818021208591 20097022206788727031812887)
  ·
    refine ⟨30145533310183090547719331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20097022206788727031812887 30145533310183090547719331)
    ·
      refine ⟨45218299965274635821578997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30145533310183090547719331 45218299965274635821578997)
      ·
        refine ⟨4239215621744497108273031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45218299965274635821578997 4239215621744497108273031)
        ·
          refine ⟨6358823432616745662409547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4239215621744497108273031 6358823432616745662409547)
          ·
            refine ⟨9538235148925118493614321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6358823432616745662409547 9538235148925118493614321)
            ·
              refine ⟨7153676361693838870210741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9538235148925118493614321 7153676361693838870210741)
              ·
                refine ⟨670657158908797394082257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7153676361693838870210741 670657158908797394082257)
                ·
                  refine ⟨502992869181598045561693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 670657158908797394082257 502992869181598045561693)
                  ·
                    refine ⟨188622325943099267085635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 502992869181598045561693 188622325943099267085635)
                    ·
                      rfl

theorem cell22_551011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 2, 3].length) (baseStart_551011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551011 prefixEnd_551011 := by exact prefixLift 551011
  have htrace : WordTrace (prefixWord ++ tailWord_551011) baseStart_551011 baseEnd_551011 := by
    simpa [prefixWord, tailWord_551011, baseEnd_551011] using wordTrace_append hprefix tailTrace_551011
  have hstable : (prefixWord ++ tailWord_551011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551011).length < 2 ^ (prefixWord ++ tailWord_551011).sum := by decide
  have hdescent : baseEnd_551011 < baseStart_551011 := by decide
  rcases family_descends (prefixWord ++ tailWord_551011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551024 : List Nat := [2, 1, 1, 1, 5, 3, 1, 8]
def baseStart_551024 : Nat := 118140960795 + 551024 * 2 ^ 59
def prefixEnd_551024 : Nat := 4983230072969 + 3 ^ 40 * 551024 * 2
def baseEnd_551024 : Nat := 20958530678752396278955

theorem tailTrace_551024 : CollatzResearch.WordTrace tailWord_551024 prefixEnd_551024 20958530678752396278955 := by
  unfold tailWord_551024
  simp only [CollatzResearch.WordTrace]
  refine ⟨10048748177870815126018063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13398330903827753501357417 10048748177870815126018063)
  ·
    refine ⟨15073122266806222689027095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10048748177870815126018063 15073122266806222689027095)
    ·
      refine ⟨22609683400209334033540643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15073122266806222689027095 22609683400209334033540643)
      ·
        refine ⟨33914525100314001050310965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22609683400209334033540643 33914525100314001050310965)
        ·
          refine ⟨3179486728154437598466653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33914525100314001050310965 3179486728154437598466653)
          ·
            refine ⟨1192307523057914099424995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3179486728154437598466653 1192307523057914099424995)
            ·
              refine ⟨1788461284586871149137493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1192307523057914099424995 1788461284586871149137493)
              ·
                refine ⟨20958530678752396278955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1788461284586871149137493 20958530678752396278955)
                ·
                  rfl

theorem cell22_551024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 8].length) (baseStart_551024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551024 prefixEnd_551024 := by exact prefixLift 551024
  have htrace : WordTrace (prefixWord ++ tailWord_551024) baseStart_551024 baseEnd_551024 := by
    simpa [prefixWord, tailWord_551024, baseEnd_551024] using wordTrace_append hprefix tailTrace_551024
  have hstable : (prefixWord ++ tailWord_551024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551024).length < 2 ^ (prefixWord ++ tailWord_551024).sum := by decide
  have hdescent : baseEnd_551024 < baseStart_551024 := by decide
  rcases family_descends (prefixWord ++ tailWord_551024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551030 : List Nat := [5, 1, 1, 2, 1, 4, 1, 3, 4]
def baseStart_551030 : Nat := 118140960795 + 551030 * 2 ^ 59
def prefixEnd_551030 : Nat := 4983230072969 + 3 ^ 40 * 551030 * 2
def baseEnd_551030 : Nat := 62876276677129850286859

theorem tailTrace_551030 : CollatzResearch.WordTrace tailWord_551030 prefixEnd_551030 62876276677129850286859 := by
  unfold tailWord_551030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1256107199607493329797159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13398476795813262184503029 1256107199607493329797159)
  ·
    refine ⟨1884160799411239994695739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1256107199607493329797159 1884160799411239994695739)
    ·
      refine ⟨2826241199116859992043609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1884160799411239994695739 2826241199116859992043609)
      ·
        refine ⟨2119680899337644994032707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2826241199116859992043609 2119680899337644994032707)
        ·
          refine ⟨3179521349006467491049061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2119680899337644994032707 3179521349006467491049061)
          ·
            refine ⟨596160252938712654571699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3179521349006467491049061 596160252938712654571699)
            ·
              refine ⟨894240379408068981857549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 596160252938712654571699 894240379408068981857549)
              ·
                refine ⟨335340142278025868196581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 894240379408068981857549 335340142278025868196581)
                ·
                  refine ⟨62876276677129850286859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 335340142278025868196581 62876276677129850286859)
                  ·
                    rfl

theorem cell22_551030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_551030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551030 prefixEnd_551030 := by exact prefixLift 551030
  have htrace : WordTrace (prefixWord ++ tailWord_551030) baseStart_551030 baseEnd_551030 := by
    simpa [prefixWord, tailWord_551030, baseEnd_551030] using wordTrace_append hprefix tailTrace_551030
  have hstable : (prefixWord ++ tailWord_551030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551030).length < 2 ^ (prefixWord ++ tailWord_551030).sum := by decide
  have hdescent : baseEnd_551030 < baseStart_551030 := by decide
  rcases family_descends (prefixWord ++ tailWord_551030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551041 : List Nat := [1, 2, 4, 2, 3, 2, 8]
def baseStart_551041 : Nat := 118140960795 + 551041 * 2 ^ 59
def prefixEnd_551041 : Nat := 4983230072969 + 3 ^ 40 * 551041 * 2
def baseEnd_551041 : Nat := 6986392428007006993909

theorem tailTrace_551041 : CollatzResearch.WordTrace tailWord_551041 prefixEnd_551041 6986392428007006993909 := by
  unfold tailWord_551041
  simp only [CollatzResearch.WordTrace]
  refine ⟨20098116396680042155404977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13398744264453361436936651 20098116396680042155404977)
  ·
    refine ⟨15073587297510031616553733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20098116396680042155404977 15073587297510031616553733)
    ·
      refine ⟨2826297618283130928103825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15073587297510031616553733 2826297618283130928103825)
      ·
        refine ⟨2119723213712348196077869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2826297618283130928103825 2119723213712348196077869)
        ·
          refine ⟨794896205142130573529201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2119723213712348196077869 794896205142130573529201)
          ·
            refine ⟨596172153856597930146901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 794896205142130573529201 596172153856597930146901)
            ·
              refine ⟨6986392428007006993909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 596172153856597930146901 6986392428007006993909)
              ·
                rfl

theorem cell22_551041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 8].length) (baseStart_551041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551041 prefixEnd_551041 := by exact prefixLift 551041
  have htrace : WordTrace (prefixWord ++ tailWord_551041) baseStart_551041 baseEnd_551041 := by
    simpa [prefixWord, tailWord_551041, baseEnd_551041] using wordTrace_append hprefix tailTrace_551041
  have hstable : (prefixWord ++ tailWord_551041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551041).length < 2 ^ (prefixWord ++ tailWord_551041).sum := by decide
  have hdescent : baseEnd_551041 < baseStart_551041 := by decide
  rcases family_descends (prefixWord ++ tailWord_551041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551133 : List Nat := [1, 4, 3, 2, 1, 1, 2, 1, 3, 4]
def baseStart_551133 : Nat := 118140960795 + 551133 * 2 ^ 59
def prefixEnd_551133 : Nat := 4983230072969 + 3 ^ 40 * 551133 * 2
def baseEnd_551133 : Nat := 188664089036331615535261

theorem tailTrace_551133 : CollatzResearch.WordTrace tailWord_551133 prefixEnd_551133 188664089036331615535261 := by
  unfold tailWord_551133
  simp only [CollatzResearch.WordTrace]
  refine ⟨20101471912346741867754053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13400981274897827911836035 20101471912346741867754053)
  ·
    refine ⟨3769025983565014100203885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20101471912346741867754053 3769025983565014100203885)
    ·
      refine ⟨1413384743836880287576457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3769025983565014100203885 1413384743836880287576457)
      ·
        refine ⟨1060038557877660215682343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1413384743836880287576457 1060038557877660215682343)
        ·
          refine ⟨1590057836816490323523515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1060038557877660215682343 1590057836816490323523515)
          ·
            refine ⟨2385086755224735485285273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1590057836816490323523515 2385086755224735485285273)
            ·
              refine ⟨1788815066418551613963955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2385086755224735485285273 1788815066418551613963955)
              ·
                refine ⟨2683222599627827420945933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1788815066418551613963955 2683222599627827420945933)
                ·
                  refine ⟨1006208474860435282854725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2683222599627827420945933 1006208474860435282854725)
                  ·
                    refine ⟨188664089036331615535261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1006208474860435282854725 188664089036331615535261)
                    ·
                      rfl

theorem cell22_551133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_551133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551133 prefixEnd_551133 := by exact prefixLift 551133
  have htrace : WordTrace (prefixWord ++ tailWord_551133) baseStart_551133 baseEnd_551133 := by
    simpa [prefixWord, tailWord_551133, baseEnd_551133] using wordTrace_append hprefix tailTrace_551133
  have hstable : (prefixWord ++ tailWord_551133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551133).length < 2 ^ (prefixWord ++ tailWord_551133).sum := by decide
  have hdescent : baseEnd_551133 < baseStart_551133 := by decide
  rcases family_descends (prefixWord ++ tailWord_551133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551146 : List Nat := [3, 1, 3, 1, 1, 2, 1, 4, 1, 5]
def baseStart_551146 : Nat := 118140960795 + 551146 * 2 ^ 59
def prefixEnd_551146 : Nat := 4983230072969 + 3 ^ 40 * 551146 * 2
def baseEnd_551146 : Nat := 188668539202003914960221

theorem tailTrace_551146 : CollatzResearch.WordTrace tailWord_551146 prefixEnd_551146 188668539202003914960221 := by
  unfold tailWord_551146
  simp only [CollatzResearch.WordTrace]
  refine ⟨5025486515324911271994323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13401297374199763391984861 5025486515324911271994323)
  ·
    refine ⟨7538229772987366907991485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5025486515324911271994323 7538229772987366907991485)
    ·
      refine ⟨2826836164870262590496807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7538229772987366907991485 2826836164870262590496807)
      ·
        refine ⟨4240254247305393885745211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2826836164870262590496807 4240254247305393885745211)
        ·
          refine ⟨6360381370958090828617817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4240254247305393885745211 6360381370958090828617817)
          ·
            refine ⟨4770286028218568121463363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6360381370958090828617817 4770286028218568121463363)
            ·
              refine ⟨7155429042327852182195045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4770286028218568121463363 7155429042327852182195045)
              ·
                refine ⟨1341642945436472284161571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7155429042327852182195045 1341642945436472284161571)
                ·
                  refine ⟨2012464418154708426242357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1341642945436472284161571 2012464418154708426242357)
                  ·
                    refine ⟨188668539202003914960221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2012464418154708426242357 188668539202003914960221)
                    ·
                      rfl

theorem cell22_551146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_551146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551146 prefixEnd_551146 := by exact prefixLift 551146
  have htrace : WordTrace (prefixWord ++ tailWord_551146) baseStart_551146 baseEnd_551146 := by
    simpa [prefixWord, tailWord_551146, baseEnd_551146] using wordTrace_append hprefix tailTrace_551146
  have hstable : (prefixWord ++ tailWord_551146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551146).length < 2 ^ (prefixWord ++ tailWord_551146).sum := by decide
  have hdescent : baseEnd_551146 < baseStart_551146 := by decide
  rcases family_descends (prefixWord ++ tailWord_551146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551148 : List Nat := [2, 2, 1, 1, 2, 3, 4, 3, 4]
def baseStart_551148 : Nat := 118140960795 + 551148 * 2 ^ 59
def prefixEnd_551148 : Nat := 4983230072969 + 3 ^ 40 * 551148 * 2
def baseEnd_551148 : Nat := 62889741280958858803405

theorem tailTrace_551148 : CollatzResearch.WordTrace tailWord_551148 prefixEnd_551148 62889741280958858803405 := by
  unfold tailWord_551148
  simp only [CollatzResearch.WordTrace]
  refine ⟨10051009503646199714775049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13401346004861599619700065 10051009503646199714775049)
  ·
    refine ⟨7538257127734649786081287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10051009503646199714775049 7538257127734649786081287)
    ·
      refine ⟨11307385691601974679121931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7538257127734649786081287 11307385691601974679121931)
      ·
        refine ⟨16961078537402962018682897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11307385691601974679121931 16961078537402962018682897)
        ·
          refine ⟨12720808903052221514012173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16961078537402962018682897 12720808903052221514012173)
          ·
            refine ⟨4770303338644583067754565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12720808903052221514012173 4770303338644583067754565)
            ·
              refine ⟨894431875995859325203981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4770303338644583067754565 894431875995859325203981)
              ·
                refine ⟨335411953498447246951493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 894431875995859325203981 335411953498447246951493)
                ·
                  refine ⟨62889741280958858803405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 335411953498447246951493 62889741280958858803405)
                  ·
                    rfl

theorem cell22_551148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3, 4].length) (baseStart_551148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551148 prefixEnd_551148 := by exact prefixLift 551148
  have htrace : WordTrace (prefixWord ++ tailWord_551148) baseStart_551148 baseEnd_551148 := by
    simpa [prefixWord, tailWord_551148, baseEnd_551148] using wordTrace_append hprefix tailTrace_551148
  have hstable : (prefixWord ++ tailWord_551148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551148).length < 2 ^ (prefixWord ++ tailWord_551148).sum := by decide
  have hdescent : baseEnd_551148 < baseStart_551148 := by decide
  rcases family_descends (prefixWord ++ tailWord_551148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551180 : List Nat := [2, 2, 1, 2, 2, 2, 5, 1, 2, 3]
def baseStart_551180 : Nat := 118140960795 + 551180 * 2 ^ 59
def prefixEnd_551180 : Nat := 4983230072969 + 3 ^ 40 * 551180 * 2
def baseEnd_551180 : Nat := 188680178096839159610117

theorem tailTrace_551180 : CollatzResearch.WordTrace tailWord_551180 prefixEnd_551180 188680178096839159610117 := by
  unfold tailWord_551180
  simp only [CollatzResearch.WordTrace]
  refine ⟨10051593071588234447357497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13402124095450979263143329 10051593071588234447357497)
  ·
    refine ⟨7538694803691175835518123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10051593071588234447357497 7538694803691175835518123)
    ·
      refine ⟨11308042205536763753277185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7538694803691175835518123 11308042205536763753277185)
      ·
        refine ⟨8481031654152572814957889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11308042205536763753277185 8481031654152572814957889)
        ·
          refine ⟨6360773740614429611218417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8481031654152572814957889 6360773740614429611218417)
          ·
            refine ⟨4770580305460822208413813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6360773740614429611218417 4770580305460822208413813)
            ·
              refine ⟨447241903636952082038795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4770580305460822208413813 447241903636952082038795)
              ·
                refine ⟨670862855455428123058193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 447241903636952082038795 670862855455428123058193)
                ·
                  refine ⟨503147141591571092293645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 670862855455428123058193 503147141591571092293645)
                  ·
                    refine ⟨188680178096839159610117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 503147141591571092293645 188680178096839159610117)
                    ·
                      rfl

theorem cell22_551180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 2, 3].length) (baseStart_551180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551180 prefixEnd_551180 := by exact prefixLift 551180
  have htrace : WordTrace (prefixWord ++ tailWord_551180) baseStart_551180 baseEnd_551180 := by
    simpa [prefixWord, tailWord_551180, baseEnd_551180] using wordTrace_append hprefix tailTrace_551180
  have hstable : (prefixWord ++ tailWord_551180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551180).length < 2 ^ (prefixWord ++ tailWord_551180).sum := by decide
  have hdescent : baseEnd_551180 < baseStart_551180 := by decide
  rcases family_descends (prefixWord ++ tailWord_551180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551210 : List Nat := [3, 1, 4, 2, 3, 1, 8]
def baseStart_551210 : Nat := 118140960795 + 551210 * 2 ^ 59
def prefixEnd_551210 : Nat := 4983230072969 + 3 ^ 40 * 551210 * 2
def baseEnd_551210 : Nat := 6988535100367743754075

theorem tailTrace_551210 : CollatzResearch.WordTrace tailWord_551210 prefixEnd_551210 6988535100367743754075 := by
  unfold tailWord_551210
  simp only [CollatzResearch.WordTrace]
  refine ⟨5026070083266946004576771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13402853555378522678871389 5026070083266946004576771)
  ·
    refine ⟨7539105124900419006865157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5026070083266946004576771 7539105124900419006865157)
    ·
      refine ⟨1413582210918828563787217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7539105124900419006865157 1413582210918828563787217)
      ·
        refine ⟨1060186658189121422840413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1413582210918828563787217 1060186658189121422840413)
        ·
          refine ⟨397569996820920533565155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1060186658189121422840413 397569996820920533565155)
          ·
            refine ⟨596354995231380800347733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397569996820920533565155 596354995231380800347733)
            ·
              refine ⟨6988535100367743754075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 596354995231380800347733 6988535100367743754075)
              ·
                rfl

theorem cell22_551210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 8].length) (baseStart_551210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551210 prefixEnd_551210 := by exact prefixLift 551210
  have htrace : WordTrace (prefixWord ++ tailWord_551210) baseStart_551210 baseEnd_551210 := by
    simpa [prefixWord, tailWord_551210, baseEnd_551210] using wordTrace_append hprefix tailTrace_551210
  have hstable : (prefixWord ++ tailWord_551210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551210).length < 2 ^ (prefixWord ++ tailWord_551210).sum := by decide
  have hdescent : baseEnd_551210 < baseStart_551210 := by decide
  rcases family_descends (prefixWord ++ tailWord_551210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551221 : List Nat := [1, 3, 3, 1, 2, 1, 1, 3, 7]
def baseStart_551221 : Nat := 118140960795 + 551221 * 2 ^ 59
def prefixEnd_551221 : Nat := 4983230072969 + 3 ^ 40 * 551221 * 2
def baseEnd_551221 : Nat := 62898071078242906444997

theorem tailTrace_551221 : CollatzResearch.WordTrace tailWord_551221 prefixEnd_551221 62898071078242906444997 := by
  unfold tailWord_551221
  simp only [CollatzResearch.WordTrace]
  refine ⟨20104681536027932896957517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13403121024018621931305011 20104681536027932896957517)
  ·
    refine ⟨7539255576010474836359069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20104681536027932896957517 7539255576010474836359069)
    ·
      refine ⟨2827220841003928063634651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7539255576010474836359069 2827220841003928063634651)
      ·
        refine ⟨4240831261505892095451977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2827220841003928063634651 4240831261505892095451977)
        ·
          refine ⟨3180623446129419071588983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4240831261505892095451977 3180623446129419071588983)
          ·
            refine ⟨4770935169194128607383475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3180623446129419071588983 4770935169194128607383475)
            ·
              refine ⟨7156402753791192911075213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4770935169194128607383475 7156402753791192911075213)
              ·
                refine ⟨2683651032671697341653205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7156402753791192911075213 2683651032671697341653205)
                ·
                  refine ⟨62898071078242906444997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2683651032671697341653205 62898071078242906444997)
                  ·
                    rfl

theorem cell22_551221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 7].length) (baseStart_551221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551221 prefixEnd_551221 := by exact prefixLift 551221
  have htrace : WordTrace (prefixWord ++ tailWord_551221) baseStart_551221 baseEnd_551221 := by
    simpa [prefixWord, tailWord_551221, baseEnd_551221] using wordTrace_append hprefix tailTrace_551221
  have hstable : (prefixWord ++ tailWord_551221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551221).length < 2 ^ (prefixWord ++ tailWord_551221).sum := by decide
  have hdescent : baseEnd_551221 < baseStart_551221 := by decide
  rcases family_descends (prefixWord ++ tailWord_551221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551225 : List Nat := [1, 2, 1, 6, 1, 1, 3, 1, 3, 3]
def baseStart_551225 : Nat := 118140960795 + 551225 * 2 ^ 59
def prefixEnd_551225 : Nat := 4983230072969 + 3 ^ 40 * 551225 * 2
def baseEnd_551225 : Nat := 188695582516474042234979

theorem tailTrace_551225 : CollatzResearch.WordTrace tailWord_551225 prefixEnd_551225 188695582516474042234979 := by
  unfold tailWord_551225
  simp only [CollatzResearch.WordTrace]
  refine ⟨20104827428013441580103129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13403218285342294386735419 20104827428013441580103129)
  ·
    refine ⟨15078620571010081185077347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20104827428013441580103129 15078620571010081185077347)
    ·
      refine ⟨22617930856515121777616021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15078620571010081185077347 22617930856515121777616021)
      ·
        refine ⟨1060215508899146333325751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22617930856515121777616021 1060215508899146333325751)
        ·
          refine ⟨1590323263348719499988627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1060215508899146333325751 1590323263348719499988627)
          ·
            refine ⟨2385484895023079249982941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1590323263348719499988627 2385484895023079249982941)
            ·
              refine ⟨894556835633654718743603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2385484895023079249982941 894556835633654718743603)
              ·
                refine ⟨1341835253450482078115405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 894556835633654718743603 1341835253450482078115405)
                ·
                  refine ⟨503188220043930779293277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1341835253450482078115405 503188220043930779293277)
                  ·
                    refine ⟨188695582516474042234979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 503188220043930779293277 188695582516474042234979)
                    ·
                      rfl

theorem cell22_551225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 3, 3].length) (baseStart_551225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551225 prefixEnd_551225 := by exact prefixLift 551225
  have htrace : WordTrace (prefixWord ++ tailWord_551225) baseStart_551225 baseEnd_551225 := by
    simpa [prefixWord, tailWord_551225, baseEnd_551225] using wordTrace_append hprefix tailTrace_551225
  have hstable : (prefixWord ++ tailWord_551225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551225).length < 2 ^ (prefixWord ++ tailWord_551225).sum := by decide
  have hdescent : baseEnd_551225 < baseStart_551225 := by decide
  rcases family_descends (prefixWord ++ tailWord_551225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551276 : List Nat := [2, 2, 1, 1, 7, 1, 2, 2, 1, 3]
def baseStart_551276 : Nat := 118140960795 + 551276 * 2 ^ 59
def prefixEnd_551276 : Nat := 4983230072969 + 3 ^ 40 * 551276 * 2
def baseEnd_551276 : Nat := 188713040858726909209823

theorem tailTrace_551276 : CollatzResearch.WordTrace tailWord_551276 prefixEnd_551276 188713040858726909209823 := by
  unfold tailWord_551276
  simp only [CollatzResearch.WordTrace]
  refine ⟨10053343775414338645104841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13404458367219118193473121 10053343775414338645104841)
  ·
    refine ⟨7540007831560753983828631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10053343775414338645104841 7540007831560753983828631)
    ·
      refine ⟨11310011747341130975742947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7540007831560753983828631 11310011747341130975742947)
      ·
        refine ⟨16965017621011696463614421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11310011747341130975742947 16965017621011696463614421)
        ·
          refine ⟨397617600492461635865963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 16965017621011696463614421 397617600492461635865963)
          ·
            refine ⟨596426400738692453798945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397617600492461635865963 596426400738692453798945)
            ·
              refine ⟨447319800554019340349209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 596426400738692453798945 447319800554019340349209)
              ·
                refine ⟨335489850415514505261907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 447319800554019340349209 335489850415514505261907)
                ·
                  refine ⟨503234775623271757892861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 335489850415514505261907 503234775623271757892861)
                  ·
                    refine ⟨188713040858726909209823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 503234775623271757892861 188713040858726909209823)
                    ·
                      rfl

theorem cell22_551276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 2, 1, 3].length) (baseStart_551276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551276 prefixEnd_551276 := by exact prefixLift 551276
  have htrace : WordTrace (prefixWord ++ tailWord_551276) baseStart_551276 baseEnd_551276 := by
    simpa [prefixWord, tailWord_551276, baseEnd_551276] using wordTrace_append hprefix tailTrace_551276
  have hstable : (prefixWord ++ tailWord_551276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551276).length < 2 ^ (prefixWord ++ tailWord_551276).sum := by decide
  have hdescent : baseEnd_551276 < baseStart_551276 := by decide
  rcases family_descends (prefixWord ++ tailWord_551276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551281 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 5, 5]
def baseStart_551281 : Nat := 118140960795 + 551281 * 2 ^ 59
def prefixEnd_551281 : Nat := 4983230072969 + 3 ^ 40 * 551281 * 2
def baseEnd_551281 : Nat := 188714752460908562834807

theorem tailTrace_551281 : CollatzResearch.WordTrace tailWord_551281 prefixEnd_551281 188714752460908562834807 := by
  unfold tailWord_551281
  simp only [CollatzResearch.WordTrace]
  refine ⟨20106869915810563144141697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13404579943873708762761131 20106869915810563144141697)
  ·
    refine ⟨15080152436857922358106273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20106869915810563144141697 15080152436857922358106273)
    ·
      refine ⟨11310114327643441768579705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15080152436857922358106273 11310114327643441768579705)
      ·
        refine ⟨8482585745732581326434779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11310114327643441768579705 8482585745732581326434779)
        ·
          refine ⟨12723878618598871989652169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8482585745732581326434779 12723878618598871989652169)
          ·
            refine ⟨9542908963949153992239127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12723878618598871989652169 9542908963949153992239127)
            ·
              refine ⟨14314363445923730988358691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9542908963949153992239127 14314363445923730988358691)
              ·
                refine ⟨21471545168885596482538037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14314363445923730988358691 21471545168885596482538037)
                ·
                  refine ⟨2012957359583024670237941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21471545168885596482538037 2012957359583024670237941)
                  ·
                    refine ⟨188714752460908562834807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2012957359583024670237941 188714752460908562834807)
                    ·
                      rfl

theorem cell22_551281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_551281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551281 prefixEnd_551281 := by exact prefixLift 551281
  have htrace : WordTrace (prefixWord ++ tailWord_551281) baseStart_551281 baseEnd_551281 := by
    simpa [prefixWord, tailWord_551281, baseEnd_551281] using wordTrace_append hprefix tailTrace_551281
  have hstable : (prefixWord ++ tailWord_551281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551281).length < 2 ^ (prefixWord ++ tailWord_551281).sum := by decide
  have hdescent : baseEnd_551281 < baseStart_551281 := by decide
  rcases family_descends (prefixWord ++ tailWord_551281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551283 : List Nat := [1, 1, 1, 2, 2, 1, 2, 8, 4]
def baseStart_551283 : Nat := 118140960795 + 551283 * 2 ^ 59
def prefixEnd_551283 : Nat := 4983230072969 + 3 ^ 40 * 551283 * 2
def baseEnd_551283 : Nat := 62905145700593741428267

theorem tailTrace_551283 : CollatzResearch.WordTrace tailWord_551283 prefixEnd_551283 62905145700593741428267 := by
  unfold tailWord_551283
  simp only [CollatzResearch.WordTrace]
  refine ⟨20106942861803317485714503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13404628574535544990476335 20106942861803317485714503)
  ·
    refine ⟨30160414292704976228571755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20106942861803317485714503 30160414292704976228571755)
    ·
      refine ⟨45240621439057464342857633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30160414292704976228571755 45240621439057464342857633)
      ·
        refine ⟨33930466079293098257143225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45240621439057464342857633 33930466079293098257143225)
        ·
          refine ⟨25447849559469823692857419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33930466079293098257143225 25447849559469823692857419)
          ·
            refine ⟨38171774339204735539286129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25447849559469823692857419 38171774339204735539286129)
            ·
              refine ⟨28628830754403551654464597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38171774339204735539286129 28628830754403551654464597)
              ·
                refine ⟨335494110403166620950757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 28628830754403551654464597 335494110403166620950757)
                ·
                  refine ⟨62905145700593741428267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 335494110403166620950757 62905145700593741428267)
                  ·
                    rfl

theorem cell22_551283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 8, 4].length) (baseStart_551283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551283 prefixEnd_551283 := by exact prefixLift 551283
  have htrace : WordTrace (prefixWord ++ tailWord_551283) baseStart_551283 baseEnd_551283 := by
    simpa [prefixWord, tailWord_551283, baseEnd_551283] using wordTrace_append hprefix tailTrace_551283
  have hstable : (prefixWord ++ tailWord_551283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551283).length < 2 ^ (prefixWord ++ tailWord_551283).sum := by decide
  have hdescent : baseEnd_551283 < baseStart_551283 := by decide
  rcases family_descends (prefixWord ++ tailWord_551283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551349 : List Nat := [1, 3, 3, 2, 3, 1, 3, 1, 2, 3]
def baseStart_551349 : Nat := 118140960795 + 551349 * 2 ^ 59
def prefixEnd_551349 : Nat := 4983230072969 + 3 ^ 40 * 551349 * 2
def baseEnd_551349 : Nat := 188738030250579052134599

theorem tailTrace_551349 : CollatzResearch.WordTrace tailWord_551349 prefixEnd_551349 188738030250579052134599 := by
  unfold tailWord_551349
  simp only [CollatzResearch.WordTrace]
  refine ⟨20109350079564210757617101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13406233386376140505078067 20109350079564210757617101)
  ·
    refine ⟨7541006279836579034106413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20109350079564210757617101 7541006279836579034106413)
    ·
      refine ⟨2827877354938717137789905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7541006279836579034106413 2827877354938717137789905)
      ·
        refine ⟨2120908016204037853342429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2827877354938717137789905 2120908016204037853342429)
        ·
          refine ⟨795340506076514195003411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2120908016204037853342429 795340506076514195003411)
          ·
            refine ⟨1193010759114771292505117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 795340506076514195003411 1193010759114771292505117)
            ·
              refine ⟨447379034668039234689419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1193010759114771292505117 447379034668039234689419)
              ·
                refine ⟨671068552002058852034129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 447379034668039234689419 671068552002058852034129)
                ·
                  refine ⟨503301414001544139025597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 671068552002058852034129 503301414001544139025597)
                  ·
                    refine ⟨188738030250579052134599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 503301414001544139025597 188738030250579052134599)
                    ·
                      rfl

theorem cell22_551349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_551349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551349 prefixEnd_551349 := by exact prefixLift 551349
  have htrace : WordTrace (prefixWord ++ tailWord_551349) baseStart_551349 baseEnd_551349 := by
    simpa [prefixWord, tailWord_551349, baseEnd_551349] using wordTrace_append hprefix tailTrace_551349
  have hstable : (prefixWord ++ tailWord_551349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551349).length < 2 ^ (prefixWord ++ tailWord_551349).sum := by decide
  have hdescent : baseEnd_551349 < baseStart_551349 := by decide
  rcases family_descends (prefixWord ++ tailWord_551349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551358 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 2, 6]
def baseStart_551358 : Nat := 118140960795 + 551358 * 2 ^ 59
def prefixEnd_551358 : Nat := 4983230072969 + 3 ^ 40 * 551358 * 2
def baseEnd_551358 : Nat := 188741111134506028659571

theorem tailTrace_551358 : CollatzResearch.WordTrace tailWord_551358 prefixEnd_551358 188741111134506028659571 := by
  unfold tailWord_551358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2513709792066450661836841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13406452224354403529796485 2513709792066450661836841)
  ·
    refine ⟨1885282344049837996377631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2513709792066450661836841 1885282344049837996377631)
    ·
      refine ⟨2827923516074756994566447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1885282344049837996377631 2827923516074756994566447)
      ·
        refine ⟨4241885274112135491849671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2827923516074756994566447 4241885274112135491849671)
        ·
          refine ⟨6362827911168203237774507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4241885274112135491849671 6362827911168203237774507)
          ·
            refine ⟨9544241866752304856661761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6362827911168203237774507 9544241866752304856661761)
            ·
              refine ⟨7158181400064228642496321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9544241866752304856661761 7158181400064228642496321)
              ·
                refine ⟨5368636050048171481872241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7158181400064228642496321 5368636050048171481872241)
                ·
                  refine ⟨4026477037536128611404181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5368636050048171481872241 4026477037536128611404181)
                  ·
                    refine ⟨188741111134506028659571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4026477037536128611404181 188741111134506028659571)
                    ·
                      rfl

theorem cell22_551358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_551358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551358 prefixEnd_551358 := by exact prefixLift 551358
  have htrace : WordTrace (prefixWord ++ tailWord_551358) baseStart_551358 baseEnd_551358 := by
    simpa [prefixWord, tailWord_551358, baseEnd_551358] using wordTrace_append hprefix tailTrace_551358
  have hstable : (prefixWord ++ tailWord_551358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551358).length < 2 ^ (prefixWord ++ tailWord_551358).sum := by decide
  have hdescent : baseEnd_551358 < baseStart_551358 := by decide
  rcases family_descends (prefixWord ++ tailWord_551358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551403 : List Nat := [1, 1, 1, 1, 2, 3, 4, 2, 3, 4]
def baseStart_551403 : Nat := 118140960795 + 551403 * 2 ^ 59
def prefixEnd_551403 : Nat := 4983230072969 + 3 ^ 40 * 551403 * 2
def baseEnd_551403 : Nat := 188756515554140911284433

theorem tailTrace_551403 : CollatzResearch.WordTrace tailWord_551403 prefixEnd_551403 188756515554140911284433 := by
  unfold tailWord_551403
  simp only [CollatzResearch.WordTrace]
  refine ⟨20111319621368577980082863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13407546414245718653388575 20111319621368577980082863)
  ·
    refine ⟨30166979432052866970124295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20111319621368577980082863 30166979432052866970124295)
    ·
      refine ⟨45250469148079300455186443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30166979432052866970124295 45250469148079300455186443)
      ·
        refine ⟨67875703722118950682779665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45250469148079300455186443 67875703722118950682779665)
        ·
          refine ⟨50906777791589213012084749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67875703722118950682779665 50906777791589213012084749)
          ·
            refine ⟨19090041671845954879531781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50906777791589213012084749 19090041671845954879531781)
            ·
              refine ⟨3579382813471116539912209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19090041671845954879531781 3579382813471116539912209)
              ·
                refine ⟨2684537110103337404934157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3579382813471116539912209 2684537110103337404934157)
                ·
                  refine ⟨1006701416288751526850309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2684537110103337404934157 1006701416288751526850309)
                  ·
                    refine ⟨188756515554140911284433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1006701416288751526850309 188756515554140911284433)
                    ·
                      rfl

theorem cell22_551403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 4].length) (baseStart_551403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551403 prefixEnd_551403 := by exact prefixLift 551403
  have htrace : WordTrace (prefixWord ++ tailWord_551403) baseStart_551403 baseEnd_551403 := by
    simpa [prefixWord, tailWord_551403, baseEnd_551403] using wordTrace_append hprefix tailTrace_551403
  have hstable : (prefixWord ++ tailWord_551403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551403).length < 2 ^ (prefixWord ++ tailWord_551403).sum := by decide
  have hdescent : baseEnd_551403 < baseStart_551403 := by decide
  rcases family_descends (prefixWord ++ tailWord_551403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551450 : List Nat := [3, 1, 1, 3, 1, 1, 2, 3, 4, 3]
def baseStart_551450 : Nat := 118140960795 + 551450 * 2 ^ 59
def prefixEnd_551450 : Nat := 4983230072969 + 3 ^ 40 * 551450 * 2
def baseEnd_551450 : Nat := 188772604614648455359289

theorem tailTrace_551450 : CollatzResearch.WordTrace tailWord_551450 prefixEnd_551450 188772604614648455359289 := by
  unfold tailWord_551450
  simp only [CollatzResearch.WordTrace]
  refine ⟨5028258463049576251760951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13408689234798870004695869 5028258463049576251760951)
  ·
    refine ⟨7542387694574364377641427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5028258463049576251760951 7542387694574364377641427)
    ·
      refine ⟨11313581541861546566462141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7542387694574364377641427 11313581541861546566462141)
      ·
        refine ⟨4242593078198079962423303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11313581541861546566462141 4242593078198079962423303)
        ·
          refine ⟨6363889617297119943634955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4242593078198079962423303 6363889617297119943634955)
          ·
            refine ⟨9545834425945679915452433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6363889617297119943634955 9545834425945679915452433)
            ·
              refine ⟨7159375819459259936589325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9545834425945679915452433 7159375819459259936589325)
              ·
                refine ⟨2684765932297222476220997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7159375819459259936589325 2684765932297222476220997)
                ·
                  refine ⟨503393612305729214291437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2684765932297222476220997 503393612305729214291437)
                  ·
                    refine ⟨188772604614648455359289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 503393612305729214291437 188772604614648455359289)
                    ·
                      rfl

theorem cell22_551450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 4, 3].length) (baseStart_551450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551450 prefixEnd_551450 := by exact prefixLift 551450
  have htrace : WordTrace (prefixWord ++ tailWord_551450) baseStart_551450 baseEnd_551450 := by
    simpa [prefixWord, tailWord_551450, baseEnd_551450] using wordTrace_append hprefix tailTrace_551450
  have hstable : (prefixWord ++ tailWord_551450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551450).length < 2 ^ (prefixWord ++ tailWord_551450).sum := by decide
  have hdescent : baseEnd_551450 < baseStart_551450 := by decide
  rcases family_descends (prefixWord ++ tailWord_551450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551452 : List Nat := [2, 2, 3, 1, 2, 3, 1, 4, 4]
def baseStart_551452 : Nat := 118140960795 + 551452 * 2 ^ 59
def prefixEnd_551452 : Nat := 4983230072969 + 3 ^ 40 * 551452 * 2
def baseEnd_551452 : Nat := 62924429751840372269761

theorem tailTrace_551452 : CollatzResearch.WordTrace tailWord_551452 prefixEnd_551452 62924429751840372269761 := by
  unfold tailWord_551452
  simp only [CollatzResearch.WordTrace]
  refine ⟨10056553399095529674308305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13408737865460706232411073 10056553399095529674308305)
  ·
    refine ⟨7542415049321647255731229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10056553399095529674308305 7542415049321647255731229)
    ·
      refine ⟨2828405643495617720899211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7542415049321647255731229 2828405643495617720899211)
      ·
        refine ⟨4242608465243426581348817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2828405643495617720899211 4242608465243426581348817)
        ·
          refine ⟨3181956348932569936011613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4242608465243426581348817 3181956348932569936011613)
          ·
            refine ⟨1193233630849713726004355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3181956348932569936011613 1193233630849713726004355)
            ·
              refine ⟨1789850446274570589006533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1193233630849713726004355 1789850446274570589006533)
              ·
                refine ⟨335596958676481985438725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1789850446274570589006533 335596958676481985438725)
                ·
                  refine ⟨62924429751840372269761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 335596958676481985438725 62924429751840372269761)
                  ·
                    rfl

theorem cell22_551452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 4, 4].length) (baseStart_551452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551452 prefixEnd_551452 := by exact prefixLift 551452
  have htrace : WordTrace (prefixWord ++ tailWord_551452) baseStart_551452 baseEnd_551452 := by
    simpa [prefixWord, tailWord_551452, baseEnd_551452] using wordTrace_append hprefix tailTrace_551452
  have hstable : (prefixWord ++ tailWord_551452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551452).length < 2 ^ (prefixWord ++ tailWord_551452).sum := by decide
  have hdescent : baseEnd_551452 < baseStart_551452 := by decide
  rcases family_descends (prefixWord ++ tailWord_551452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551480 : List Nat := [2, 1, 2, 1, 4, 1, 5, 6]
def baseStart_551480 : Nat := 118140960795 + 551480 * 2 ^ 59
def prefixEnd_551480 : Nat := 4983230072969 + 3 ^ 40 * 551480 * 2
def baseEnd_551480 : Nat := 20975874914193153012133

theorem tailTrace_551480 : CollatzResearch.WordTrace tailWord_551480 prefixEnd_551480 20975874914193153012133 := by
  unfold tailWord_551480
  simp only [CollatzResearch.WordTrace]
  refine ⟨10057064021044810065317947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13409418694726413420423929 10057064021044810065317947)
  ·
    refine ⟨15085596031567215097976921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10057064021044810065317947 15085596031567215097976921)
    ·
      refine ⟨11314197023675411323482691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15085596031567215097976921 11314197023675411323482691)
      ·
        refine ⟨16971295535513116985224037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11314197023675411323482691 16971295535513116985224037)
        ·
          refine ⟨3182117912908709434729507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16971295535513116985224037 3182117912908709434729507)
          ·
            refine ⟨4773176869363064152094261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3182117912908709434729507 4773176869363064152094261)
            ·
              refine ⟨447485331502787264258837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4773176869363064152094261 447485331502787264258837)
              ·
                refine ⟨20975874914193153012133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 447485331502787264258837 20975874914193153012133)
                ·
                  rfl

theorem cell22_551480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 6].length) (baseStart_551480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551480 prefixEnd_551480 := by exact prefixLift 551480
  have htrace : WordTrace (prefixWord ++ tailWord_551480) baseStart_551480 baseEnd_551480 := by
    simpa [prefixWord, tailWord_551480, baseEnd_551480] using wordTrace_append hprefix tailTrace_551480
  have hstable : (prefixWord ++ tailWord_551480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551480).length < 2 ^ (prefixWord ++ tailWord_551480).sum := by decide
  have hdescent : baseEnd_551480 < baseStart_551480 := by decide
  rcases family_descends (prefixWord ++ tailWord_551480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551482 : List Nat := [3, 1, 1, 1, 3, 5, 1, 1, 2, 4]
def baseStart_551482 : Nat := 118140960795 + 551482 * 2 ^ 59
def prefixEnd_551482 : Nat := 4983230072969 + 3 ^ 40 * 551482 * 2
def baseEnd_551482 : Nat := 188783558868611038559191

theorem tailTrace_551482 : CollatzResearch.WordTrace tailWord_551482 prefixEnd_551482 188783558868611038559191 := by
  unfold tailWord_551482
  simp only [CollatzResearch.WordTrace]
  refine ⟨5028550247020593618052175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13409467325388249648139133 5028550247020593618052175)
  ·
    refine ⟨7542825370530890427078263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5028550247020593618052175 7542825370530890427078263)
    ·
      refine ⟨11314238055796335640617395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7542825370530890427078263 11314238055796335640617395)
      ·
        refine ⟨16971357083694503460926093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11314238055796335640617395 16971357083694503460926093)
        ·
          refine ⟨6364258906385438797847285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16971357083694503460926093 6364258906385438797847285)
          ·
            refine ⟨596649272473634887298183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6364258906385438797847285 596649272473634887298183)
            ·
              refine ⟨894973908710452330947275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 596649272473634887298183 894973908710452330947275)
              ·
                refine ⟨1342460863065678496420913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 894973908710452330947275 1342460863065678496420913)
                ·
                  refine ⟨1006845647299258872315685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1342460863065678496420913 1006845647299258872315685)
                  ·
                    refine ⟨188783558868611038559191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1006845647299258872315685 188783558868611038559191)
                    ·
                      rfl

theorem cell22_551482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 2, 4].length) (baseStart_551482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551482 prefixEnd_551482 := by exact prefixLift 551482
  have htrace : WordTrace (prefixWord ++ tailWord_551482) baseStart_551482 baseEnd_551482 := by
    simpa [prefixWord, tailWord_551482, baseEnd_551482] using wordTrace_append hprefix tailTrace_551482
  have hstable : (prefixWord ++ tailWord_551482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551482).length < 2 ^ (prefixWord ++ tailWord_551482).sum := by decide
  have hdescent : baseEnd_551482 < baseStart_551482 := by decide
  rcases family_descends (prefixWord ++ tailWord_551482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551486 : List Nat := [4, 2, 1, 4, 1, 1, 2, 3, 4]
def baseStart_551486 : Nat := 118140960795 + 551486 * 2 ^ 59
def prefixEnd_551486 : Nat := 4983230072969 + 3 ^ 40 * 551486 * 2
def baseEnd_551486 : Nat := 62928309383452120486393

theorem tailTrace_551486 : CollatzResearch.WordTrace tailWord_551486 prefixEnd_551486 62928309383452120486393 := by
  unfold tailWord_551486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2514293360008485394419289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13409564586711922103569541 2514293360008485394419289)
  ·
    refine ⟨1885720020006364045814467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2514293360008485394419289 1885720020006364045814467)
    ·
      refine ⟨2828580030009546068721701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1885720020006364045814467 2828580030009546068721701)
      ·
        refine ⟨530358755626789887885319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2828580030009546068721701 530358755626789887885319)
        ·
          refine ⟨795538133440184831827979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 530358755626789887885319 795538133440184831827979)
          ·
            refine ⟨1193307200160277247741969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 795538133440184831827979 1193307200160277247741969)
            ·
              refine ⟨894980400120207935806477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1193307200160277247741969 894980400120207935806477)
              ·
                refine ⟨335617650045077975927429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 894980400120207935806477 335617650045077975927429)
                ·
                  refine ⟨62928309383452120486393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 335617650045077975927429 62928309383452120486393)
                  ·
                    rfl

theorem cell22_551486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_551486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551486 prefixEnd_551486 := by exact prefixLift 551486
  have htrace : WordTrace (prefixWord ++ tailWord_551486) baseStart_551486 baseEnd_551486 := by
    simpa [prefixWord, tailWord_551486, baseEnd_551486] using wordTrace_append hprefix tailTrace_551486
  have hstable : (prefixWord ++ tailWord_551486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551486).length < 2 ^ (prefixWord ++ tailWord_551486).sum := by decide
  have hdescent : baseEnd_551486 < baseStart_551486 := by decide
  rcases family_descends (prefixWord ++ tailWord_551486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551501 : List Nat := [1, 6, 1, 1, 2, 3, 1, 2, 2, 3]
def baseStart_551501 : Nat := 118140960795 + 551501 * 2 ^ 59
def prefixEnd_551501 : Nat := 4983230072969 + 3 ^ 40 * 551501 * 2
def baseEnd_551501 : Nat := 188790062956901322334133

theorem tailTrace_551501 : CollatzResearch.WordTrace tailWord_551501 prefixEnd_551501 188790062956901322334133 := by
  unfold tailWord_551501
  simp only [CollatzResearch.WordTrace]
  refine ⟨20114893975013540717150357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13409929316675693811433571 20114893975013540717150357)
  ·
    refine ⟨942885655078759721116423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20114893975013540717150357 942885655078759721116423)
    ·
      refine ⟨1414328482618139581674635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 942885655078759721116423 1414328482618139581674635)
      ·
        refine ⟨2121492723927209372511953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1414328482618139581674635 2121492723927209372511953)
        ·
          refine ⟨1591119542945407029383965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2121492723927209372511953 1591119542945407029383965)
          ·
            refine ⟨596669828604527636018987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1591119542945407029383965 596669828604527636018987)
            ·
              refine ⟨895004742906791454028481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 596669828604527636018987 895004742906791454028481)
              ·
                refine ⟨671253557180093590521361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 895004742906791454028481 671253557180093590521361)
                ·
                  refine ⟨503440167885070192891021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 671253557180093590521361 503440167885070192891021)
                  ·
                    refine ⟨188790062956901322334133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 503440167885070192891021 188790062956901322334133)
                    ·
                      rfl

theorem cell22_551501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_551501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551501 prefixEnd_551501 := by exact prefixLift 551501
  have htrace : WordTrace (prefixWord ++ tailWord_551501) baseStart_551501 baseEnd_551501 := by
    simpa [prefixWord, tailWord_551501, baseEnd_551501] using wordTrace_append hprefix tailTrace_551501
  have hstable : (prefixWord ++ tailWord_551501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551501).length < 2 ^ (prefixWord ++ tailWord_551501).sum := by decide
  have hdescent : baseEnd_551501 < baseStart_551501 := by decide
  rcases family_descends (prefixWord ++ tailWord_551501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551518 : List Nat := [4, 4, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_551518 : Nat := 118140960795 + 551518 * 2 ^ 59
def prefixEnd_551518 : Nat := 4983230072969 + 3 ^ 40 * 551518 * 2
def baseEnd_551518 : Nat := 188795882404318944659081

theorem tailTrace_551518 : CollatzResearch.WordTrace tailWord_551518 prefixEnd_551518 188795882404318944659081 := by
  unfold tailWord_551518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2514439251993994077564901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13410342677301301747012805 2514439251993994077564901)
  ·
    refine ⟨471457359748873889543419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2514439251993994077564901 471457359748873889543419)
    ·
      refine ⟨707186039623310834315129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 471457359748873889543419 707186039623310834315129)
      ·
        refine ⟨530389529717483125736347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 707186039623310834315129 530389529717483125736347)
        ·
          refine ⟨795584294576224688604521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 530389529717483125736347 795584294576224688604521)
          ·
            refine ⟨596688220932168516453391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 795584294576224688604521 596688220932168516453391)
            ·
              refine ⟨895032331398252774680087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 596688220932168516453391 895032331398252774680087)
              ·
                refine ⟨1342548497097379162020131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 895032331398252774680087 1342548497097379162020131)
                ·
                  refine ⟨2013822745646068743030197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1342548497097379162020131 2013822745646068743030197)
                  ·
                    refine ⟨188795882404318944659081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2013822745646068743030197 188795882404318944659081)
                    ·
                      rfl

theorem cell22_551518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_551518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551518 prefixEnd_551518 := by exact prefixLift 551518
  have htrace : WordTrace (prefixWord ++ tailWord_551518) baseStart_551518 baseEnd_551518 := by
    simpa [prefixWord, tailWord_551518, baseEnd_551518] using wordTrace_append hprefix tailTrace_551518
  have hstable : (prefixWord ++ tailWord_551518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551518).length < 2 ^ (prefixWord ++ tailWord_551518).sum := by decide
  have hdescent : baseEnd_551518 < baseStart_551518 := by decide
  rcases family_descends (prefixWord ++ tailWord_551518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551647 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 5, 3]
def baseStart_551647 : Nat := 118140960795 + 551647 * 2 ^ 59
def prefixEnd_551647 : Nat := 4983230072969 + 3 ^ 40 * 551647 * 2
def baseEnd_551647 : Nat := 188840041740605608183685

theorem tailTrace_551647 : CollatzResearch.WordTrace tailWord_551647 prefixEnd_551647 188840041740605608183685 := by
  unfold tailWord_551647
  simp only [CollatzResearch.WordTrace]
  refine ⟨20120219032484607651965195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13413479354989738434643463 20120219032484607651965195)
  ·
    refine ⟨30180328548726911477947793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20120219032484607651965195 30180328548726911477947793)
    ·
      refine ⟨22635246411545183608460845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30180328548726911477947793 22635246411545183608460845)
      ·
        refine ⟨8488217404329443853172817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22635246411545183608460845 8488217404329443853172817)
        ·
          refine ⟨6366163053247082889879613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8488217404329443853172817 6366163053247082889879613)
          ·
            refine ⟨2387311144967656083704855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6366163053247082889879613 2387311144967656083704855)
            ·
              refine ⟨3580966717451484125557283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2387311144967656083704855 3580966717451484125557283)
              ·
                refine ⟨5371450076177226188335925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3580966717451484125557283 5371450076177226188335925)
                ·
                  refine ⟨503573444641614955156493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5371450076177226188335925 503573444641614955156493)
                  ·
                    refine ⟨188840041740605608183685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 503573444641614955156493 188840041740605608183685)
                    ·
                      rfl

theorem cell22_551647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 5, 3].length) (baseStart_551647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551647 prefixEnd_551647 := by exact prefixLift 551647
  have htrace : WordTrace (prefixWord ++ tailWord_551647) baseStart_551647 baseEnd_551647 := by
    simpa [prefixWord, tailWord_551647, baseEnd_551647] using wordTrace_append hprefix tailTrace_551647
  have hstable : (prefixWord ++ tailWord_551647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551647).length < 2 ^ (prefixWord ++ tailWord_551647).sum := by decide
  have hdescent : baseEnd_551647 < baseStart_551647 := by decide
  rcases family_descends (prefixWord ++ tailWord_551647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551660 : List Nat := [2, 2, 1, 1, 2, 2, 1, 4, 7]
def baseStart_551660 : Nat := 118140960795 + 551660 * 2 ^ 59
def prefixEnd_551660 : Nat := 4983230072969 + 3 ^ 40 * 551660 * 2
def baseEnd_551660 : Nat := 62948163968759302536215

theorem tailTrace_551660 : CollatzResearch.WordTrace tailWord_551660 prefixEnd_551660 62948163968759302536215 := by
  unfold tailWord_551660
  simp only [CollatzResearch.WordTrace]
  refine ⟨10060346590718755436094217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13413795454291673914792289 10060346590718755436094217)
  ·
    refine ⟨7545259943039066577070663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10060346590718755436094217 7545259943039066577070663)
    ·
      refine ⟨11317889914558599865605995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7545259943039066577070663 11317889914558599865605995)
      ·
        refine ⟨16976834871837899798408993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11317889914558599865605995 16976834871837899798408993)
        ·
          refine ⟨12732626153878424848806745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16976834871837899798408993 12732626153878424848806745)
          ·
            refine ⟨9549469615408818636605059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12732626153878424848806745 9549469615408818636605059)
            ·
              refine ⟨14324204423113227954907589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9549469615408818636605059 14324204423113227954907589)
              ·
                refine ⟨2685788329333730241545173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14324204423113227954907589 2685788329333730241545173)
                ·
                  refine ⟨62948163968759302536215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2685788329333730241545173 62948163968759302536215)
                  ·
                    rfl

theorem cell22_551660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 7].length) (baseStart_551660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551660 prefixEnd_551660 := by exact prefixLift 551660
  have htrace : WordTrace (prefixWord ++ tailWord_551660) baseStart_551660 baseEnd_551660 := by
    simpa [prefixWord, tailWord_551660, baseEnd_551660] using wordTrace_append hprefix tailTrace_551660
  have hstable : (prefixWord ++ tailWord_551660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551660).length < 2 ^ (prefixWord ++ tailWord_551660).sum := by decide
  have hdescent : baseEnd_551660 < baseStart_551660 := by decide
  rcases family_descends (prefixWord ++ tailWord_551660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551705 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 8]
def baseStart_551705 : Nat := 118140960795 + 551705 * 2 ^ 59
def prefixEnd_551705 : Nat := 4983230072969 + 3 ^ 40 * 551705 * 2
def baseEnd_551705 : Nat := 62953298775304263411169

theorem tailTrace_551705 : CollatzResearch.WordTrace tailWord_551705 prefixEnd_551705 62953298775304263411169 := by
  unfold tailWord_551705
  simp only [CollatzResearch.WordTrace]
  refine ⟨20122334466274483557576569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13414889644182989038384379 20122334466274483557576569)
  ·
    refine ⟨15091750849705862668182427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20122334466274483557576569 15091750849705862668182427)
    ·
      refine ⟨22637626274558794002273641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15091750849705862668182427 22637626274558794002273641)
      ·
        refine ⟨16978219705919095501705231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22637626274558794002273641 16978219705919095501705231)
        ·
          refine ⟨25467329558878643252557847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16978219705919095501705231 25467329558878643252557847)
          ·
            refine ⟨38200994338317964878836771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25467329558878643252557847 38200994338317964878836771)
            ·
              refine ⟨57301491507476947318255157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38200994338317964878836771 57301491507476947318255157)
              ·
                refine ⟨5372014828825963811086421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57301491507476947318255157 5372014828825963811086421)
                ·
                  refine ⟨62953298775304263411169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5372014828825963811086421 62953298775304263411169)
                  ·
                    rfl

theorem cell22_551705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 8].length) (baseStart_551705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551705 prefixEnd_551705 := by exact prefixLift 551705
  have htrace : WordTrace (prefixWord ++ tailWord_551705) baseStart_551705 baseEnd_551705 := by
    simpa [prefixWord, tailWord_551705, baseEnd_551705] using wordTrace_append hprefix tailTrace_551705
  have hstable : (prefixWord ++ tailWord_551705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551705).length < 2 ^ (prefixWord ++ tailWord_551705).sum := by decide
  have hdescent : baseEnd_551705 < baseStart_551705 := by decide
  rcases family_descends (prefixWord ++ tailWord_551705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551745 : List Nat := [1, 2, 5, 3, 2, 1, 2, 1, 5]
def baseStart_551745 : Nat := 118140960795 + 551745 * 2 ^ 59
def prefixEnd_551745 : Nat := 4983230072969 + 3 ^ 40 * 551745 * 2
def baseEnd_551745 : Nat := 62957863047788673077795

theorem tailTrace_551745 : CollatzResearch.WordTrace tailWord_551745 prefixEnd_551745 62957863047788673077795 := by
  unfold tailWord_551745
  simp only [CollatzResearch.WordTrace]
  refine ⟨20123793386129570389032689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13415862257419713592688459 20123793386129570389032689)
  ·
    refine ⟨15092845039597177791774517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20123793386129570389032689 15092845039597177791774517)
    ·
      refine ⟨1414954222462235417978861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15092845039597177791774517 1414954222462235417978861)
      ·
        refine ⟨530607833423338281742073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1414954222462235417978861 530607833423338281742073)
        ·
          refine ⟨397955875067503711306555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 530607833423338281742073 397955875067503711306555)
          ·
            refine ⟨596933812601255566959833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397955875067503711306555 596933812601255566959833)
            ·
              refine ⟨447700359450941675219875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 596933812601255566959833 447700359450941675219875)
              ·
                refine ⟨671550539176412512829813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 447700359450941675219875 671550539176412512829813)
                ·
                  refine ⟨62957863047788673077795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 671550539176412512829813 62957863047788673077795)
                  ·
                    rfl

theorem cell22_551745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 5].length) (baseStart_551745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551745 prefixEnd_551745 := by exact prefixLift 551745
  have htrace : WordTrace (prefixWord ++ tailWord_551745) baseStart_551745 baseEnd_551745 := by
    simpa [prefixWord, tailWord_551745, baseEnd_551745] using wordTrace_append hprefix tailTrace_551745
  have hstable : (prefixWord ++ tailWord_551745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551745).length < 2 ^ (prefixWord ++ tailWord_551745).sum := by decide
  have hdescent : baseEnd_551745 < baseStart_551745 := by decide
  rcases family_descends (prefixWord ++ tailWord_551745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551752 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 4, 4]
def baseStart_551752 : Nat := 118140960795 + 551752 * 2 ^ 59
def prefixEnd_551752 : Nat := 4983230072969 + 3 ^ 40 * 551752 * 2
def baseEnd_551752 : Nat := 188875985386420334308363

theorem tailTrace_551752 : CollatzResearch.WordTrace tailWord_551752 prefixEnd_551752 188875985386420334308363 := by
  unfold tailWord_551752
  simp only [CollatzResearch.WordTrace]
  refine ⟨10062024348552105292268755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13416032464736140389691673 10062024348552105292268755)
  ·
    refine ⟨15093036522828157938403133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10062024348552105292268755 15093036522828157938403133)
    ·
      refine ⟨5659888696060559226901175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15093036522828157938403133 5659888696060559226901175)
      ·
        refine ⟨8489833044090838840351763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5659888696060559226901175 8489833044090838840351763)
        ·
          refine ⟨12734749566136258260527645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8489833044090838840351763 12734749566136258260527645)
          ·
            refine ⟨4775531087301096847697867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12734749566136258260527645 4775531087301096847697867)
            ·
              refine ⟨7163296630951645271546801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4775531087301096847697867 7163296630951645271546801)
              ·
                refine ⟨5372472473213733953660101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7163296630951645271546801 5372472473213733953660101)
                ·
                  refine ⟨1007338588727575116311269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5372472473213733953660101 1007338588727575116311269)
                  ·
                    refine ⟨188875985386420334308363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1007338588727575116311269 188875985386420334308363)
                    ·
                      rfl

theorem cell22_551752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_551752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551752 prefixEnd_551752 := by exact prefixLift 551752
  have htrace : WordTrace (prefixWord ++ tailWord_551752) baseStart_551752 baseEnd_551752 := by
    simpa [prefixWord, tailWord_551752, baseEnd_551752] using wordTrace_append hprefix tailTrace_551752
  have hstable : (prefixWord ++ tailWord_551752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551752).length < 2 ^ (prefixWord ++ tailWord_551752).sum := by decide
  have hdescent : baseEnd_551752 < baseStart_551752 := by decide
  rcases family_descends (prefixWord ++ tailWord_551752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551767 : List Nat := [1, 1, 3, 2, 4, 1, 2, 8]
def baseStart_551767 : Nat := 118140960795 + 551767 * 2 ^ 59
def prefixEnd_551767 : Nat := 4983230072969 + 3 ^ 40 * 551767 * 2
def baseEnd_551767 : Nat := 20986791132551699464813

theorem tailTrace_551767 : CollatzResearch.WordTrace tailWord_551767 prefixEnd_551767 20986791132551699464813 := by
  unfold tailWord_551767
  simp only [CollatzResearch.WordTrace]
  refine ⟨20124595792049868146333555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13416397194699912097555703 20124595792049868146333555)
  ·
    refine ⟨30186893688074802219500333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20124595792049868146333555 30186893688074802219500333)
    ·
      refine ⟨11320085133028050832312625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30186893688074802219500333 11320085133028050832312625)
      ·
        refine ⟨8490063849771038124234469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11320085133028050832312625 8490063849771038124234469)
        ·
          refine ⟨1591886971832069648293963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8490063849771038124234469 1591886971832069648293963)
          ·
            refine ⟨2387830457748104472440945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1591886971832069648293963 2387830457748104472440945)
            ·
              refine ⟨1790872843311078354330709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2387830457748104472440945 1790872843311078354330709)
              ·
                refine ⟨20986791132551699464813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1790872843311078354330709 20986791132551699464813)
                ·
                  rfl

theorem cell22_551767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 8].length) (baseStart_551767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551767 prefixEnd_551767 := by exact prefixLift 551767
  have htrace : WordTrace (prefixWord ++ tailWord_551767) baseStart_551767 baseEnd_551767 := by
    simpa [prefixWord, tailWord_551767, baseEnd_551767] using wordTrace_append hprefix tailTrace_551767
  have hstable : (prefixWord ++ tailWord_551767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551767).length < 2 ^ (prefixWord ++ tailWord_551767).sum := by decide
  have hdescent : baseEnd_551767 < baseStart_551767 := by decide
  rcases family_descends (prefixWord ++ tailWord_551767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551769 : List Nat := [1, 2, 1, 2, 2, 5, 2, 1, 2, 4]
def baseStart_551769 : Nat := 118140960795 + 551769 * 2 ^ 59
def prefixEnd_551769 : Nat := 4983230072969 + 3 ^ 40 * 551769 * 2
def baseEnd_551769 : Nat := 188881804833837956633311

theorem tailTrace_551769 : CollatzResearch.WordTrace tailWord_551769 prefixEnd_551769 188881804833837956633311 := by
  unfold tailWord_551769
  simp only [CollatzResearch.WordTrace]
  refine ⟨20124668738042622487906361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13416445825361748325270907 20124668738042622487906361)
  ·
    refine ⟨15093501553531966865929771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20124668738042622487906361 15093501553531966865929771)
    ·
      refine ⟨22640252330297950298894657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15093501553531966865929771 22640252330297950298894657)
      ·
        refine ⟨16980189247723462724170993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22640252330297950298894657 16980189247723462724170993)
        ·
          refine ⟨12735141935792597043128245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16980189247723462724170993 12735141935792597043128245)
          ·
            refine ⟨1193919556480555972793273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12735141935792597043128245 1193919556480555972793273)
            ·
              refine ⟨895439667360416979594955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1193919556480555972793273 895439667360416979594955)
              ·
                refine ⟨1343159501040625469392433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 895439667360416979594955 1343159501040625469392433)
                ·
                  refine ⟨1007369625780469102044325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1343159501040625469392433 1007369625780469102044325)
                  ·
                    refine ⟨188881804833837956633311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1007369625780469102044325 188881804833837956633311)
                    ·
                      rfl

theorem cell22_551769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 4].length) (baseStart_551769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551769 prefixEnd_551769 := by exact prefixLift 551769
  have htrace : WordTrace (prefixWord ++ tailWord_551769) baseStart_551769 baseEnd_551769 := by
    simpa [prefixWord, tailWord_551769, baseEnd_551769] using wordTrace_append hprefix tailTrace_551769
  have hstable : (prefixWord ++ tailWord_551769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551769).length < 2 ^ (prefixWord ++ tailWord_551769).sum := by decide
  have hdescent : baseEnd_551769 < baseStart_551769 := by decide
  rcases family_descends (prefixWord ++ tailWord_551769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551790 : List Nat := [4, 1, 2, 3, 2, 2, 2, 2, 4]
def baseStart_551790 : Nat := 118140960795 + 551790 * 2 ^ 59
def prefixEnd_551790 : Nat := 4983230072969 + 3 ^ 40 * 551790 * 2
def baseEnd_551790 : Nat := 62962997854333633952749

theorem tailTrace_551790 : CollatzResearch.WordTrace tailWord_551790 prefixEnd_551790 62962997854333633952749 := by
  unfold tailWord_551790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2515679333870817884302603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13416956447311028716280549 2515679333870817884302603)
  ·
    refine ⟨3773519000806226826453905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2515679333870817884302603 3773519000806226826453905)
    ·
      refine ⟨2830139250604670119840429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3773519000806226826453905 2830139250604670119840429)
      ·
        refine ⟨1061302218976751294940161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2830139250604670119840429 1061302218976751294940161)
        ·
          refine ⟨795976664232563471205121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1061302218976751294940161 795976664232563471205121)
          ·
            refine ⟨596982498174422603403841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 795976664232563471205121 596982498174422603403841)
            ·
              refine ⟨447736873630816952552881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 596982498174422603403841 447736873630816952552881)
              ·
                refine ⟨335802655223112714414661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 447736873630816952552881 335802655223112714414661)
                ·
                  refine ⟨62962997854333633952749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 335802655223112714414661 62962997854333633952749)
                  ·
                    rfl

theorem cell22_551790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_551790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551790 prefixEnd_551790 := by exact prefixLift 551790
  have htrace : WordTrace (prefixWord ++ tailWord_551790) baseStart_551790 baseEnd_551790 := by
    simpa [prefixWord, tailWord_551790, baseEnd_551790] using wordTrace_append hprefix tailTrace_551790
  have hstable : (prefixWord ++ tailWord_551790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551790).length < 2 ^ (prefixWord ++ tailWord_551790).sum := by decide
  have hdescent : baseEnd_551790 < baseStart_551790 := by decide
  rcases family_descends (prefixWord ++ tailWord_551790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551812 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 9]
def baseStart_551812 : Nat := 118140960795 + 551812 * 2 ^ 59
def prefixEnd_551812 : Nat := 4983230072969 + 3 ^ 40 * 551812 * 2
def baseEnd_551812 : Nat := 62965508204200059269393

theorem tailTrace_551812 : CollatzResearch.WordTrace tailWord_551812 prefixEnd_551812 62965508204200059269393 := by
  unfold tailWord_551812
  simp only [CollatzResearch.WordTrace]
  refine ⟨10063118538443420415860845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13417491384591227221147793 10063118538443420415860845)
  ·
    refine ⟨3773669451916282655947817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10063118538443420415860845 3773669451916282655947817)
    ·
      refine ⟨2830252088937211991960863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3773669451916282655947817 2830252088937211991960863)
      ·
        refine ⟨4245378133405817987941295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2830252088937211991960863 4245378133405817987941295)
        ·
          refine ⟨6368067200108726981911943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4245378133405817987941295 6368067200108726981911943)
          ·
            refine ⟨9552100800163090472867915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6368067200108726981911943 9552100800163090472867915)
            ·
              refine ⟨14328151200244635709301873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9552100800163090472867915 14328151200244635709301873)
              ·
                refine ⟨10746113400183476781976405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14328151200244635709301873 10746113400183476781976405)
                ·
                  refine ⟨62965508204200059269393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10746113400183476781976405 62965508204200059269393)
                  ·
                    rfl

theorem cell22_551812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_551812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551812 prefixEnd_551812 := by exact prefixLift 551812
  have htrace : WordTrace (prefixWord ++ tailWord_551812) baseStart_551812 baseEnd_551812 := by
    simpa [prefixWord, tailWord_551812, baseEnd_551812] using wordTrace_append hprefix tailTrace_551812
  have hstable : (prefixWord ++ tailWord_551812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551812).length < 2 ^ (prefixWord ++ tailWord_551812).sum := by decide
  have hdescent : baseEnd_551812 < baseStart_551812 := by decide
  rcases family_descends (prefixWord ++ tailWord_551812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551816 : List Nat := [2, 1, 3, 3, 2, 2, 1, 2, 3, 3]
def baseStart_551816 : Nat := 118140960795 + 551816 * 2 ^ 59
def prefixEnd_551816 : Nat := 4983230072969 + 3 ^ 40 * 551816 * 2
def baseEnd_551816 : Nat := 188897893894345500708167

theorem tailTrace_551816 : CollatzResearch.WordTrace tailWord_551816 prefixEnd_551816 188897893894345500708167 := by
  unfold tailWord_551816
  simp only [CollatzResearch.WordTrace]
  refine ⟨10063191484436174757433651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13417588645914899676578201 10063191484436174757433651)
  ·
    refine ⟨15094787226654262136150477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10063191484436174757433651 15094787226654262136150477)
    ·
      refine ⟨5660545209995348301056429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15094787226654262136150477 5660545209995348301056429)
      ·
        refine ⟨2122704453748255612896161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5660545209995348301056429 2122704453748255612896161)
        ·
          refine ⟨1592028340311191709672121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2122704453748255612896161 1592028340311191709672121)
          ·
            refine ⟨1194021255233393782254091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1592028340311191709672121 1194021255233393782254091)
            ·
              refine ⟨1791031882850090673381137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1194021255233393782254091 1791031882850090673381137)
              ·
                refine ⟨1343273912137568005035853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1791031882850090673381137 1343273912137568005035853)
                ·
                  refine ⟨503727717051588001888445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1343273912137568005035853 503727717051588001888445)
                  ·
                    refine ⟨188897893894345500708167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 503727717051588001888445 188897893894345500708167)
                    ·
                      rfl

theorem cell22_551816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_551816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551816 prefixEnd_551816 := by exact prefixLift 551816
  have htrace : WordTrace (prefixWord ++ tailWord_551816) baseStart_551816 baseEnd_551816 := by
    simpa [prefixWord, tailWord_551816, baseEnd_551816] using wordTrace_append hprefix tailTrace_551816
  have hstable : (prefixWord ++ tailWord_551816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551816).length < 2 ^ (prefixWord ++ tailWord_551816).sum := by decide
  have hdescent : baseEnd_551816 < baseStart_551816 := by decide
  rcases family_descends (prefixWord ++ tailWord_551816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551889 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 6, 3]
def baseStart_551889 : Nat := 118140960795 + 551889 * 2 ^ 59
def prefixEnd_551889 : Nat := 4983230072969 + 3 ^ 40 * 551889 * 2
def baseEnd_551889 : Nat := 188922883286197643632943

theorem tailTrace_551889 : CollatzResearch.WordTrace tailWord_551889 prefixEnd_551889 188922883286197643632943 := by
  unfold tailWord_551889
  simp only [CollatzResearch.WordTrace]
  refine ⟨20129045497607882982274721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13419363665071921988183147 20129045497607882982274721)
  ·
    refine ⟨15096784123205912236706041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20129045497607882982274721 15096784123205912236706041)
    ·
      refine ⟨11322588092404434177529531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15096784123205912236706041 11322588092404434177529531)
      ·
        refine ⟨16983882138606651266294297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11322588092404434177529531 16983882138606651266294297)
        ·
          refine ⟨12737911603954988449720723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16983882138606651266294297 12737911603954988449720723)
          ·
            refine ⟨19106867405932482674581085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12737911603954988449720723 19106867405932482674581085)
            ·
              refine ⟨7165075277224681002967907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19106867405932482674581085 7165075277224681002967907)
              ·
                refine ⟨10747612915837021504451861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7165075277224681002967907 10747612915837021504451861)
                ·
                  refine ⟨503794355429860383021181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10747612915837021504451861 503794355429860383021181)
                  ·
                    refine ⟨188922883286197643632943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 503794355429860383021181 188922883286197643632943)
                    ·
                      rfl

theorem cell22_551889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 6, 3].length) (baseStart_551889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551889 prefixEnd_551889 := by exact prefixLift 551889
  have htrace : WordTrace (prefixWord ++ tailWord_551889) baseStart_551889 baseEnd_551889 := by
    simpa [prefixWord, tailWord_551889, baseEnd_551889] using wordTrace_append hprefix tailTrace_551889
  have hstable : (prefixWord ++ tailWord_551889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551889).length < 2 ^ (prefixWord ++ tailWord_551889).sum := by decide
  have hdescent : baseEnd_551889 < baseStart_551889 := by decide
  rcases family_descends (prefixWord ++ tailWord_551889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551919 : List Nat := [1, 1, 2, 1, 4, 4, 2, 7]
def baseStart_551919 : Nat := 118140960795 + 551919 * 2 ^ 59
def prefixEnd_551919 : Nat := 4983230072969 + 3 ^ 40 * 551919 * 2
def baseEnd_551919 : Nat := 20992572544365285042539

theorem tailTrace_551919 : CollatzResearch.WordTrace tailWord_551919 prefixEnd_551919 20992572544365285042539 := by
  unfold tailWord_551919
  simp only [CollatzResearch.WordTrace]
  refine ⟨20130139687499198105866811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13420093124999465403911207 20130139687499198105866811)
  ·
    refine ⟨30195209531248797158800217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20130139687499198105866811 30195209531248797158800217)
    ·
      refine ⟨22646407148436597869100163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30195209531248797158800217 22646407148436597869100163)
      ·
        refine ⟨33969610722654896803650245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22646407148436597869100163 33969610722654896803650245)
        ·
          refine ⟨6369302010497793150684421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33969610722654896803650245 6369302010497793150684421)
          ·
            refine ⟨1194244126968336215753329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6369302010497793150684421 1194244126968336215753329)
            ·
              refine ⟨895683095226252161814997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1194244126968336215753329 895683095226252161814997)
              ·
                refine ⟨20992572544365285042539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 895683095226252161814997 20992572544365285042539)
                ·
                  rfl

theorem cell22_551919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 7].length) (baseStart_551919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551919 prefixEnd_551919 := by exact prefixLift 551919
  have htrace : WordTrace (prefixWord ++ tailWord_551919) baseStart_551919 baseEnd_551919 := by
    simpa [prefixWord, tailWord_551919, baseEnd_551919] using wordTrace_append hprefix tailTrace_551919
  have hstable : (prefixWord ++ tailWord_551919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551919).length < 2 ^ (prefixWord ++ tailWord_551919).sum := by decide
  have hdescent : baseEnd_551919 < baseStart_551919 := by decide
  rcases family_descends (prefixWord ++ tailWord_551919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551979 : List Nat := [1, 1, 1, 1, 2, 1, 7, 1, 2, 5]
def baseStart_551979 : Nat := 118140960795 + 551979 * 2 ^ 59
def prefixEnd_551979 : Nat := 4983230072969 + 3 ^ 40 * 551979 * 2
def baseEnd_551979 : Nat := 188953692125467408882667

theorem tailTrace_551979 : CollatzResearch.WordTrace tailWord_551979 prefixEnd_551979 188953692125467408882667 := by
  unfold tailWord_551979
  simp only [CollatzResearch.WordTrace]
  refine ⟨20132328067281828353050991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13421552044854552235367327 20132328067281828353050991)
  ·
    refine ⟨30198492100922742529576487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20132328067281828353050991 30198492100922742529576487)
    ·
      refine ⟨45297738151384113794364731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30198492100922742529576487 45297738151384113794364731)
      ·
        refine ⟨67946607227076170691547097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45297738151384113794364731 67946607227076170691547097)
        ·
          refine ⟨50959955420307128018660323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67946607227076170691547097 50959955420307128018660323)
          ·
            refine ⟨76439933130460692027990485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50959955420307128018660323 76439933130460692027990485)
            ·
              refine ⟨1791560932745172469406027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 76439933130460692027990485 1791560932745172469406027)
              ·
                refine ⟨2687341399117758704109041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1791560932745172469406027 2687341399117758704109041)
                ·
                  refine ⟨2015506049338319028081781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2687341399117758704109041 2015506049338319028081781)
                  ·
                    refine ⟨188953692125467408882667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2015506049338319028081781 188953692125467408882667)
                    ·
                      rfl

theorem cell22_551979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 5].length) (baseStart_551979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_551979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_551979 prefixEnd_551979 := by exact prefixLift 551979
  have htrace : WordTrace (prefixWord ++ tailWord_551979) baseStart_551979 baseEnd_551979 := by
    simpa [prefixWord, tailWord_551979, baseEnd_551979] using wordTrace_append hprefix tailTrace_551979
  have hstable : (prefixWord ++ tailWord_551979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551979).length < 2 ^ (prefixWord ++ tailWord_551979).sum := by decide
  have hdescent : baseEnd_551979 < baseStart_551979 := by decide
  rcases family_descends (prefixWord ++ tailWord_551979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552030 : List Nat := [4, 4, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_552030 : Nat := 118140960795 + 552030 * 2 ^ 59
def prefixEnd_552030 : Nat := 4983230072969 + 3 ^ 40 * 552030 * 2
def baseEnd_552030 : Nat := 188971150467720275857511

theorem tailTrace_552030 : CollatzResearch.WordTrace tailWord_552030 prefixEnd_552030 188971150467720275857511 := by
  unfold tailWord_552030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2516773523762133007894693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13422792126731376042105029 2516773523762133007894693)
  ·
    refine ⟨471895035705399938980255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2516773523762133007894693 471895035705399938980255)
    ·
      refine ⟨707842553558099908470383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 471895035705399938980255 707842553558099908470383)
      ·
        refine ⟨1061763830337149862705575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 707842553558099908470383 1061763830337149862705575)
        ·
          refine ⟨1592645745505724794058363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1061763830337149862705575 1592645745505724794058363)
          ·
            refine ⟨2388968618258587191087545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1592645745505724794058363 2388968618258587191087545)
            ·
              refine ⟨1791726463693940393315659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2388968618258587191087545 1791726463693940393315659)
              ·
                refine ⟨2687589695540910589973489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1791726463693940393315659 2687589695540910589973489)
                ·
                  refine ⟨2015692271655682942480117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2687589695540910589973489 2015692271655682942480117)
                  ·
                    refine ⟨188971150467720275857511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2015692271655682942480117 188971150467720275857511)
                    ·
                      rfl

theorem cell22_552030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_552030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_552030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_552030 prefixEnd_552030 := by exact prefixLift 552030
  have htrace : WordTrace (prefixWord ++ tailWord_552030) baseStart_552030 baseEnd_552030 := by
    simpa [prefixWord, tailWord_552030, baseEnd_552030] using wordTrace_append hprefix tailTrace_552030
  have hstable : (prefixWord ++ tailWord_552030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552030).length < 2 ^ (prefixWord ++ tailWord_552030).sum := by decide
  have hdescent : baseEnd_552030 < baseStart_552030 := by decide
  rcases family_descends (prefixWord ++ tailWord_552030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552041 : List Nat := [1, 2, 1, 1, 1, 6, 3, 1, 1, 5]
def baseStart_552041 : Nat := 118140960795 + 552041 * 2 ^ 59
def prefixEnd_552041 : Nat := 4983230072969 + 3 ^ 40 * 552041 * 2
def baseEnd_552041 : Nat := 188974915992519913832477

theorem tailTrace_552041 : CollatzResearch.WordTrace tailWord_552041 prefixEnd_552041 188974915992519913832477 := by
  unfold tailWord_552041
  simp only [CollatzResearch.WordTrace]
  refine ⟨20134589393057212941807977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13423059595371475294538651 20134589393057212941807977)
  ·
    refine ⟨15100942044792909706355983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20134589393057212941807977 15100942044792909706355983)
    ·
      refine ⟨22651413067189364559533975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15100942044792909706355983 22651413067189364559533975)
      ·
        refine ⟨33977119600784046839300963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22651413067189364559533975 33977119600784046839300963)
        ·
          refine ⟨50965679401176070258951445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33977119600784046839300963 50965679401176070258951445)
          ·
            refine ⟨2389016221930128293388349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 50965679401176070258951445 2389016221930128293388349)
            ·
              refine ⟨895881083223798110020631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2389016221930128293388349 895881083223798110020631)
              ·
                refine ⟨1343821624835697165030947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 895881083223798110020631 1343821624835697165030947)
                ·
                  refine ⟨2015732437253545747546421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1343821624835697165030947 2015732437253545747546421)
                  ·
                    refine ⟨188974915992519913832477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2015732437253545747546421 188974915992519913832477)
                    ·
                      rfl

theorem cell22_552041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 5].length) (baseStart_552041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_552041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_552041 prefixEnd_552041 := by exact prefixLift 552041
  have htrace : WordTrace (prefixWord ++ tailWord_552041) baseStart_552041 baseEnd_552041 := by
    simpa [prefixWord, tailWord_552041, baseEnd_552041] using wordTrace_append hprefix tailTrace_552041
  have hstable : (prefixWord ++ tailWord_552041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552041).length < 2 ^ (prefixWord ++ tailWord_552041).sum := by decide
  have hdescent : baseEnd_552041 < baseStart_552041 := by decide
  rcases family_descends (prefixWord ++ tailWord_552041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552092 : List Nat := [2, 2, 3, 2, 1, 4, 2, 1, 2, 3]
def baseStart_552092 : Nat := 118140960795 + 552092 * 2 ^ 59
def prefixEnd_552092 : Nat := 4983230072969 + 3 ^ 40 * 552092 * 2
def baseEnd_552092 : Nat := 188992374334772780807321

theorem tailTrace_552092 : CollatzResearch.WordTrace tailWord_552092 prefixEnd_552092 188992374334772780807321 := by
  unfold tailWord_552092
  simp only [CollatzResearch.WordTrace]
  refine ⟨10068224757936224325957265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13424299677248299101276353 10068224757936224325957265)
  ·
    refine ⟨7551168568452168244467949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10068224757936224325957265 7551168568452168244467949)
    ·
      refine ⟨2831688213169563091675481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7551168568452168244467949 2831688213169563091675481)
      ·
        refine ⟨2123766159877172318756611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2831688213169563091675481 2123766159877172318756611)
        ·
          refine ⟨3185649239815758478134917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2123766159877172318756611 3185649239815758478134917)
          ·
            refine ⟨597309232465454714650297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3185649239815758478134917 597309232465454714650297)
            ·
              refine ⟨447981924349091035987723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 597309232465454714650297 447981924349091035987723)
              ·
                refine ⟨671972886523636553981585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 447981924349091035987723 671972886523636553981585)
                ·
                  refine ⟨503979664892727415486189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 671972886523636553981585 503979664892727415486189)
                  ·
                    refine ⟨188992374334772780807321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 503979664892727415486189 188992374334772780807321)
                    ·
                      rfl

theorem cell22_552092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_552092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_552092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_552092 prefixEnd_552092 := by exact prefixLift 552092
  have htrace : WordTrace (prefixWord ++ tailWord_552092) baseStart_552092 baseEnd_552092 := by
    simpa [prefixWord, tailWord_552092, baseEnd_552092] using wordTrace_append hprefix tailTrace_552092
  have hstable : (prefixWord ++ tailWord_552092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552092).length < 2 ^ (prefixWord ++ tailWord_552092).sum := by decide
  have hdescent : baseEnd_552092 < baseStart_552092 := by decide
  rcases family_descends (prefixWord ++ tailWord_552092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552161 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 8]
def baseStart_552161 : Nat := 118140960795 + 552161 * 2 ^ 59
def prefixEnd_552161 : Nat := 4983230072969 + 3 ^ 40 * 552161 * 2
def baseEnd_552161 : Nat := 63005331481626533610703

theorem tailTrace_552161 : CollatzResearch.WordTrace tailWord_552161 prefixEnd_552161 63005331481626533610703 := by
  unfold tailWord_552161
  simp only [CollatzResearch.WordTrace]
  refine ⟨20138966152622473436176337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13425977435081648957450891 20138966152622473436176337)
  ·
    refine ⟨15104224614466855077132253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20138966152622473436176337 15104224614466855077132253)
    ·
      refine ⟨5664084230425070653924595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15104224614466855077132253 5664084230425070653924595)
      ·
        refine ⟨8496126345637605980886893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5664084230425070653924595 8496126345637605980886893)
        ·
          refine ⟨3186047379614102242832585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8496126345637605980886893 3186047379614102242832585)
          ·
            refine ⟨2389535534710576682124439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3186047379614102242832585 2389535534710576682124439)
            ·
              refine ⟨3584303302065865023186659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2389535534710576682124439 3584303302065865023186659)
              ·
                refine ⟨5376454953098797534779989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3584303302065865023186659 5376454953098797534779989)
                ·
                  refine ⟨63005331481626533610703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5376454953098797534779989 63005331481626533610703)
                  ·
                    rfl

theorem cell22_552161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 8].length) (baseStart_552161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_552161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_552161 prefixEnd_552161 := by exact prefixLift 552161
  have htrace : WordTrace (prefixWord ++ tailWord_552161) baseStart_552161 baseEnd_552161 := by
    simpa [prefixWord, tailWord_552161, baseEnd_552161] using wordTrace_append hprefix tailTrace_552161
  have hstable : (prefixWord ++ tailWord_552161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552161).length < 2 ^ (prefixWord ++ tailWord_552161).sum := by decide
  have hdescent : baseEnd_552161 < baseStart_552161 := by decide
  rcases family_descends (prefixWord ++ tailWord_552161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552223 : List Nat := [1, 1, 2, 4, 4, 1, 1, 8]
def baseStart_552223 : Nat := 118140960795 + 552223 * 2 ^ 59
def prefixEnd_552223 : Nat := 4983230072969 + 3 ^ 40 * 552223 * 2
def baseEnd_552223 : Nat := 21004135367992456197991

theorem tailTrace_552223 : CollatzResearch.WordTrace tailWord_552223 prefixEnd_552223 21004135367992456197991 := by
  unfold tailWord_552223
  simp only [CollatzResearch.WordTrace]
  refine ⟨20141227478397858024933323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13427484985598572016622215 20141227478397858024933323)
  ·
    refine ⟨30211841217596787037399985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20141227478397858024933323 30211841217596787037399985)
    ·
      refine ⟨22658880913197590278049989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30211841217596787037399985 22658880913197590278049989)
      ·
        refine ⟨4248540171224548177134373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22658880913197590278049989 4248540171224548177134373)
        ·
          refine ⟨796601282104602783212695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4248540171224548177134373 796601282104602783212695)
          ·
            refine ⟨1194901923156904174819043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 796601282104602783212695 1194901923156904174819043)
            ·
              refine ⟨1792352884735356262228565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1194901923156904174819043 1792352884735356262228565)
              ·
                refine ⟨21004135367992456197991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1792352884735356262228565 21004135367992456197991)
                ·
                  rfl

theorem cell22_552223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 8].length) (baseStart_552223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_552223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_552223 prefixEnd_552223 := by exact prefixLift 552223
  have htrace : WordTrace (prefixWord ++ tailWord_552223) baseStart_552223 baseEnd_552223 := by
    simpa [prefixWord, tailWord_552223, baseEnd_552223] using wordTrace_append hprefix tailTrace_552223
  have hstable : (prefixWord ++ tailWord_552223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552223).length < 2 ^ (prefixWord ++ tailWord_552223).sum := by decide
  have hdescent : baseEnd_552223 < baseStart_552223 := by decide
  rcases family_descends (prefixWord ++ tailWord_552223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552236 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 1, 8]
def baseStart_552236 : Nat := 118140960795 + 552236 * 2 ^ 59
def prefixEnd_552236 : Nat := 4983230072969 + 3 ^ 40 * 552236 * 2
def baseEnd_552236 : Nat := 189041668477604405206879

theorem tailTrace_552236 : CollatzResearch.WordTrace tailWord_552236 prefixEnd_552236 189041668477604405206879 := by
  unfold tailWord_552236
  simp only [CollatzResearch.WordTrace]
  refine ⟨10070850813675380622578281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13427801084900507496771041 10070850813675380622578281)
  ·
    refine ⟨7553138110256535466933711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10070850813675380622578281 7553138110256535466933711)
    ·
      refine ⟨11329707165384803200400567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7553138110256535466933711 11329707165384803200400567)
      ·
        refine ⟨16994560748077204800600851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11329707165384803200400567 16994560748077204800600851)
        ·
          refine ⟨25491841122115807200901277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16994560748077204800600851 25491841122115807200901277)
          ·
            refine ⟨9559440420793427700337979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25491841122115807200901277 9559440420793427700337979)
            ·
              refine ⟨14339160631190141550506969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9559440420793427700337979 14339160631190141550506969)
              ·
                refine ⟨10754370473392606162880227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14339160631190141550506969 10754370473392606162880227)
                ·
                  refine ⟨16131555710088909244320341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10754370473392606162880227 16131555710088909244320341)
                  ·
                    refine ⟨189041668477604405206879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 16131555710088909244320341 189041668477604405206879)
                    ·
                      rfl

theorem cell22_552236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_552236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_552236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_552236 prefixEnd_552236 := by exact prefixLift 552236
  have htrace : WordTrace (prefixWord ++ tailWord_552236) baseStart_552236 baseEnd_552236 := by
    simpa [prefixWord, tailWord_552236, baseEnd_552236] using wordTrace_append hprefix tailTrace_552236
  have hstable : (prefixWord ++ tailWord_552236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552236).length < 2 ^ (prefixWord ++ tailWord_552236).sum := by decide
  have hdescent : baseEnd_552236 < baseStart_552236 := by decide
  rcases family_descends (prefixWord ++ tailWord_552236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552246 : List Nat := [5, 1, 2, 3, 1, 1, 3, 2, 4]
def baseStart_552246 : Nat := 118140960795 + 552246 * 2 ^ 59
def prefixEnd_552246 : Nat := 4983230072969 + 3 ^ 40 * 552246 * 2
def baseEnd_552246 : Nat := 63015030560655904152283

theorem tailTrace_552246 : CollatzResearch.WordTrace tailWord_552246 prefixEnd_552246 63015030560655904152283 := by
  unfold tailWord_552246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1258879147332158309563787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13428044238209688635347061 1258879147332158309563787)
  ·
    refine ⟨1888318720998237464345681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1258879147332158309563787 1888318720998237464345681)
    ·
      refine ⟨1416239040748678098259261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1888318720998237464345681 1416239040748678098259261)
      ·
        refine ⟨531089640280754286847223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1416239040748678098259261 531089640280754286847223)
        ·
          refine ⟨796634460421131430270835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 531089640280754286847223 796634460421131430270835)
          ·
            refine ⟨1194951690631697145406253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 796634460421131430270835 1194951690631697145406253)
            ·
              refine ⟨448106883986886429527345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1194951690631697145406253 448106883986886429527345)
              ·
                refine ⟨336080162990164822145509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 448106883986886429527345 336080162990164822145509)
                ·
                  refine ⟨63015030560655904152283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 336080162990164822145509 63015030560655904152283)
                  ·
                    rfl

theorem cell22_552246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_552246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_552246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_552246 prefixEnd_552246 := by exact prefixLift 552246
  have htrace : WordTrace (prefixWord ++ tailWord_552246) baseStart_552246 baseEnd_552246 := by
    simpa [prefixWord, tailWord_552246, baseEnd_552246] using wordTrace_append hprefix tailTrace_552246
  have hstable : (prefixWord ++ tailWord_552246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552246).length < 2 ^ (prefixWord ++ tailWord_552246).sum := by decide
  have hdescent : baseEnd_552246 < baseStart_552246 := by decide
  rcases family_descends (prefixWord ++ tailWord_552246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552255 : List Nat := [1, 1, 2, 2, 4, 2, 3, 1, 3, 3]
def baseStart_552255 : Nat := 118140960795 + 552255 * 2 ^ 59
def prefixEnd_552255 : Nat := 4983230072969 + 3 ^ 40 * 552255 * 2
def baseEnd_552255 : Nat := 189048172565894688981821

theorem tailTrace_552255 : CollatzResearch.WordTrace tailWord_552255 prefixEnd_552255 189048172565894688981821 := by
  unfold tailWord_552255
  simp only [CollatzResearch.WordTrace]
  refine ⟨20142394614281927490098219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13428263076187951660065479 20142394614281927490098219)
  ·
    refine ⟨30213591921422891235147329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20142394614281927490098219 30213591921422891235147329)
    ·
      refine ⟨22660193941067168426360497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30213591921422891235147329 22660193941067168426360497)
      ·
        refine ⟨16995145455800376319770373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22660193941067168426360497 16995145455800376319770373)
        ·
          refine ⟨3186589772962570559956945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16995145455800376319770373 3186589772962570559956945)
          ·
            refine ⟨2389942329721927919967709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3186589772962570559956945 2389942329721927919967709)
            ·
              refine ⟨896228373645722969987891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2389942329721927919967709 896228373645722969987891)
              ·
                refine ⟨1344342560468584454981837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 896228373645722969987891 1344342560468584454981837)
                ·
                  refine ⟨504128460175719170618189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1344342560468584454981837 504128460175719170618189)
                  ·
                    refine ⟨189048172565894688981821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 504128460175719170618189 189048172565894688981821)
                    ·
                      rfl

theorem cell22_552255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 3, 3].length) (baseStart_552255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_552255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_552255 prefixEnd_552255 := by exact prefixLift 552255
  have htrace : WordTrace (prefixWord ++ tailWord_552255) baseStart_552255 baseEnd_552255 := by
    simpa [prefixWord, tailWord_552255, baseEnd_552255] using wordTrace_append hprefix tailTrace_552255
  have hstable : (prefixWord ++ tailWord_552255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552255).length < 2 ^ (prefixWord ++ tailWord_552255).sum := by decide
  have hdescent : baseEnd_552255 < baseStart_552255 := by decide
  rcases family_descends (prefixWord ++ tailWord_552255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552349 : List Nat := [1, 4, 2, 1, 3, 3, 2, 1, 1, 4]
def baseStart_552349 : Nat := 118140960795 + 552349 * 2 ^ 59
def prefixEnd_552349 : Nat := 4983230072969 + 3 ^ 40 * 552349 * 2
def baseEnd_552349 : Nat := 189080350686909777131533

theorem tailTrace_552349 : CollatzResearch.WordTrace tailWord_552349 prefixEnd_552349 189080350686909777131533 := by
  unfold tailWord_552349
  simp only [CollatzResearch.WordTrace]
  refine ⟨20145823075941381544020101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13430548717294254362680067 20145823075941381544020101)
  ·
    refine ⟨3777341826739009039503769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20145823075941381544020101 3777341826739009039503769)
    ·
      refine ⟨2833006370054256779627827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3777341826739009039503769 2833006370054256779627827)
      ·
        refine ⟨4249509555081385169441741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2833006370054256779627827 4249509555081385169441741)
        ·
          refine ⟨1593566083155519438540653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4249509555081385169441741 1593566083155519438540653)
          ·
            refine ⟨597587281183319789452745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1593566083155519438540653 597587281183319789452745)
            ·
              refine ⟨448190460887489842089559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 597587281183319789452745 448190460887489842089559)
              ·
                refine ⟨672285691331234763134339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 448190460887489842089559 672285691331234763134339)
                ·
                  refine ⟨1008428536996852144701509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 672285691331234763134339 1008428536996852144701509)
                  ·
                    refine ⟨189080350686909777131533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1008428536996852144701509 189080350686909777131533)
                    ·
                      rfl

theorem cell22_552349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_552349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_552349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_552349 prefixEnd_552349 := by exact prefixLift 552349
  have htrace : WordTrace (prefixWord ++ tailWord_552349) baseStart_552349 baseEnd_552349 := by
    simpa [prefixWord, tailWord_552349, baseEnd_552349] using wordTrace_append hprefix tailTrace_552349
  have hstable : (prefixWord ++ tailWord_552349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552349).length < 2 ^ (prefixWord ++ tailWord_552349).sum := by decide
  have hdescent : baseEnd_552349 < baseStart_552349 := by decide
  rcases family_descends (prefixWord ++ tailWord_552349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552463 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 2, 9]
def baseStart_552463 : Nat := 118140960795 + 552463 * 2 ^ 59
def prefixEnd_552463 : Nat := 4983230072969 + 3 ^ 40 * 552463 * 2
def baseEnd_552463 : Nat := 189119375216651479781183

theorem tailTrace_552463 : CollatzResearch.WordTrace tailWord_552463 prefixEnd_552463 189119375216651479781183 := by
  unfold tailWord_552463
  simp only [CollatzResearch.WordTrace]
  refine ⟨20149980997528379013670043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13433320665018919342446695 20149980997528379013670043)
  ·
    refine ⟨30224971496292568520505065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20149980997528379013670043 30224971496292568520505065)
    ·
      refine ⟨22668728622219426390378799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30224971496292568520505065 22668728622219426390378799)
      ·
        refine ⟨34003092933329139585568199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22668728622219426390378799 34003092933329139585568199)
        ·
          refine ⟨51004639399993709378352299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34003092933329139585568199 51004639399993709378352299)
          ·
            refine ⟨76506959099990564067528449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51004639399993709378352299 76506959099990564067528449)
            ·
              refine ⟨57380219324992923050646337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76506959099990564067528449 57380219324992923050646337)
              ·
                refine ⟨43035164493744692287984753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57380219324992923050646337 43035164493744692287984753)
                ·
                  refine ⟨32276373370308519215988565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43035164493744692287984753 32276373370308519215988565)
                  ·
                    refine ⟨189119375216651479781183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 32276373370308519215988565 189119375216651479781183)
                    ·
                      rfl

theorem cell22_552463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 9].length) (baseStart_552463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_552463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_552463 prefixEnd_552463 := by exact prefixLift 552463
  have htrace : WordTrace (prefixWord ++ tailWord_552463) baseStart_552463 baseEnd_552463 := by
    simpa [prefixWord, tailWord_552463, baseEnd_552463] using wordTrace_append hprefix tailTrace_552463
  have hstable : (prefixWord ++ tailWord_552463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552463).length < 2 ^ (prefixWord ++ tailWord_552463).sum := by decide
  have hdescent : baseEnd_552463 < baseStart_552463 := by decide
  rcases family_descends (prefixWord ++ tailWord_552463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552570 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 4, 5]
def baseStart_552570 : Nat := 118140960795 + 552570 * 2 ^ 59
def prefixEnd_552570 : Nat := 4983230072969 + 3 ^ 40 * 552570 * 2
def baseEnd_552570 : Nat := 189156003503338867355855

theorem tailTrace_552570 : CollatzResearch.WordTrace tailWord_552570 prefixEnd_552570 189156003503338867355855 := by
  unfold tailWord_552570
  simp only [CollatzResearch.WordTrace]
  refine ⟨5038470902035184071953791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13435922405427157525210109 5038470902035184071953791)
  ·
    refine ⟨7557706353052776107930687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5038470902035184071953791 7557706353052776107930687)
    ·
      refine ⟨11336559529579164161896031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7557706353052776107930687 11336559529579164161896031)
      ·
        refine ⟨17004839294368746242844047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11336559529579164161896031 17004839294368746242844047)
        ·
          refine ⟨25507258941553119364266071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17004839294368746242844047 25507258941553119364266071)
          ·
            refine ⟨38260888412329679046399107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25507258941553119364266071 38260888412329679046399107)
            ·
              refine ⟨57391332618494518569598661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38260888412329679046399107 57391332618494518569598661)
              ·
                refine ⟨10760874865967722231799749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57391332618494518569598661 10760874865967722231799749)
                ·
                  refine ⟨2017664037368947918462453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10760874865967722231799749 2017664037368947918462453)
                  ·
                    refine ⟨189156003503338867355855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2017664037368947918462453 189156003503338867355855)
                    ·
                      rfl

theorem cell22_552570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_552570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_552570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_552570 prefixEnd_552570 := by exact prefixLift 552570
  have htrace : WordTrace (prefixWord ++ tailWord_552570) baseStart_552570 baseEnd_552570 := by
    simpa [prefixWord, tailWord_552570, baseEnd_552570] using wordTrace_append hprefix tailTrace_552570
  have hstable : (prefixWord ++ tailWord_552570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552570).length < 2 ^ (prefixWord ++ tailWord_552570).sum := by decide
  have hdescent : baseEnd_552570 < baseStart_552570 := by decide
  rcases family_descends (prefixWord ++ tailWord_552570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552606 : List Nat := [4, 3, 1, 1, 1, 2, 4, 1, 5]
def baseStart_552606 : Nat := 118140960795 + 552606 * 2 ^ 59
def prefixEnd_552606 : Nat := 4983230072969 + 3 ^ 40 * 552606 * 2
def baseEnd_552606 : Nat := 63056109013015591151915

theorem tailTrace_552606 : CollatzResearch.WordTrace tailWord_552606 prefixEnd_552606 63056109013015591151915 := by
  unfold tailWord_552606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2519399579501289304515709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13436797757340209624083781 2519399579501289304515709)
  ·
    refine ⟨944774842312983489193391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2519399579501289304515709 944774842312983489193391)
    ·
      refine ⟨1417162263469475233790087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 944774842312983489193391 1417162263469475233790087)
      ·
        refine ⟨2125743395204212850685131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1417162263469475233790087 2125743395204212850685131)
        ·
          refine ⟨3188615092806319276027697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2125743395204212850685131 3188615092806319276027697)
          ·
            refine ⟨2391461319604739457020773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3188615092806319276027697 2391461319604739457020773)
            ·
              refine ⟨448398997425888648191395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2391461319604739457020773 448398997425888648191395)
              ·
                refine ⟨672598496138832972287093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 448398997425888648191395 672598496138832972287093)
                ·
                  refine ⟨63056109013015591151915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 672598496138832972287093 63056109013015591151915)
                  ·
                    rfl

theorem cell22_552606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_552606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_552606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_552606 prefixEnd_552606 := by exact prefixLift 552606
  have htrace : WordTrace (prefixWord ++ tailWord_552606) baseStart_552606 baseEnd_552606 := by
    simpa [prefixWord, tailWord_552606, baseEnd_552606] using wordTrace_append hprefix tailTrace_552606
  have hstable : (prefixWord ++ tailWord_552606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552606).length < 2 ^ (prefixWord ++ tailWord_552606).sum := by decide
  have hdescent : baseEnd_552606 < baseStart_552606 := by decide
  rcases family_descends (prefixWord ++ tailWord_552606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552632 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 6, 3]
def baseStart_552632 : Nat := 118140960795 + 552632 * 2 ^ 59
def prefixEnd_552632 : Nat := 4983230072969 + 3 ^ 40 * 552632 * 2
def baseEnd_552632 : Nat := 189177227370391372305665

theorem tailTrace_552632 : CollatzResearch.WordTrace tailWord_552632 prefixEnd_552632 189177227370391372305665 := by
  unfold tailWord_552632
  simp only [CollatzResearch.WordTrace]
  refine ⟨10078072466958060438286075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13437429955944080584381433 10078072466958060438286075)
  ·
    refine ⟨15117108700437090657429113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10078072466958060438286075 15117108700437090657429113)
    ·
      refine ⟨11337831525327817993071835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15117108700437090657429113 11337831525327817993071835)
      ·
        refine ⟨17006747287991726989607753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11337831525327817993071835 17006747287991726989607753)
        ·
          refine ⟨12755060465993795242205815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17006747287991726989607753 12755060465993795242205815)
          ·
            refine ⟨19132590698990692863308723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12755060465993795242205815 19132590698990692863308723)
            ·
              refine ⟨28698886048486039294963085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19132590698990692863308723 28698886048486039294963085)
              ·
                refine ⟨10762082268182264735611157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28698886048486039294963085 10762082268182264735611157)
                ·
                  refine ⟨504472606321043659481773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10762082268182264735611157 504472606321043659481773)
                  ·
                    refine ⟨189177227370391372305665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 504472606321043659481773 189177227370391372305665)
                    ·
                      rfl

theorem cell22_552632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 6, 3].length) (baseStart_552632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_552632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_552632 prefixEnd_552632 := by exact prefixLift 552632
  have htrace : WordTrace (prefixWord ++ tailWord_552632) baseStart_552632 baseEnd_552632 := by
    simpa [prefixWord, tailWord_552632, baseEnd_552632] using wordTrace_append hprefix tailTrace_552632
  have hstable : (prefixWord ++ tailWord_552632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552632).length < 2 ^ (prefixWord ++ tailWord_552632).sum := by decide
  have hdescent : baseEnd_552632 < baseStart_552632 := by decide
  rcases family_descends (prefixWord ++ tailWord_552632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552636 : List Nat := [2, 2, 2, 3, 1, 3, 3, 1, 1, 4]
def baseStart_552636 : Nat := 118140960795 + 552636 * 2 ^ 59
def prefixEnd_552636 : Nat := 4983230072969 + 3 ^ 40 * 552636 * 2
def baseEnd_552636 : Nat := 189178596652136695205653

theorem tailTrace_552636 : CollatzResearch.WordTrace tailWord_552636 prefixEnd_552636 189178596652136695205653 := by
  unfold tailWord_552636
  simp only [CollatzResearch.WordTrace]
  refine ⟨10078145412950814779858881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13437527217267753039811841 10078145412950814779858881)
  ·
    refine ⟨7558609059713111084894161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10078145412950814779858881 7558609059713111084894161)
    ·
      refine ⟨5668956794784833313670621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7558609059713111084894161 5668956794784833313670621)
      ·
        refine ⟨2125858798044312492626483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5668956794784833313670621 2125858798044312492626483)
        ·
          refine ⟨3188788197066468738939725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2125858798044312492626483 3188788197066468738939725)
          ·
            refine ⟨1195795573899925777102397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3188788197066468738939725 1195795573899925777102397)
            ·
              refine ⟨448423340212472166413399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1195795573899925777102397 448423340212472166413399)
              ·
                refine ⟨672635010318708249620099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 448423340212472166413399 672635010318708249620099)
                ·
                  refine ⟨1008952515478062374430149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 672635010318708249620099 1008952515478062374430149)
                  ·
                    refine ⟨189178596652136695205653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1008952515478062374430149 189178596652136695205653)
                    ·
                      rfl

theorem cell22_552636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_552636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_552636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_552636 prefixEnd_552636 := by exact prefixLift 552636
  have htrace : WordTrace (prefixWord ++ tailWord_552636) baseStart_552636 baseEnd_552636 := by
    simpa [prefixWord, tailWord_552636, baseEnd_552636] using wordTrace_append hprefix tailTrace_552636
  have hstable : (prefixWord ++ tailWord_552636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552636).length < 2 ^ (prefixWord ++ tailWord_552636).sum := by decide
  have hdescent : baseEnd_552636 < baseStart_552636 := by decide
  rcases family_descends (prefixWord ++ tailWord_552636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552647 : List Nat := [1, 1, 4, 1, 1, 1, 3, 4, 2, 4]
def baseStart_552647 : Nat := 118140960795 + 552647 * 2 ^ 59
def prefixEnd_552647 : Nat := 4983230072969 + 3 ^ 40 * 552647 * 2
def baseEnd_552647 : Nat := 189182362176936333180619

theorem tailTrace_552647 : CollatzResearch.WordTrace tailWord_552647 prefixEnd_552647 189182362176936333180619 := by
  unfold tailWord_552647
  simp only [CollatzResearch.WordTrace]
  refine ⟨20156692028861778438368195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13437794685907852292245463 20156692028861778438368195)
  ·
    refine ⟨30235038043292667657552293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20156692028861778438368195 30235038043292667657552293)
    ·
      refine ⟨5669069633117375185791055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30235038043292667657552293 5669069633117375185791055)
      ·
        refine ⟨8503604449676062778686583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5669069633117375185791055 8503604449676062778686583)
        ·
          refine ⟨12755406674514094168029875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8503604449676062778686583 12755406674514094168029875)
          ·
            refine ⟨19133110011771141252044813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12755406674514094168029875 19133110011771141252044813)
            ·
              refine ⟨7174916254414177969516805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19133110011771141252044813 7174916254414177969516805)
              ·
                refine ⟨1345296797702658369284401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7174916254414177969516805 1345296797702658369284401)
                ·
                  refine ⟨1008972598276993776963301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1345296797702658369284401 1008972598276993776963301)
                  ·
                    refine ⟨189182362176936333180619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1008972598276993776963301 189182362176936333180619)
                    ·
                      rfl

theorem cell22_552647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_552647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_552647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_552647 prefixEnd_552647 := by exact prefixLift 552647
  have htrace : WordTrace (prefixWord ++ tailWord_552647) baseStart_552647 baseEnd_552647 := by
    simpa [prefixWord, tailWord_552647, baseEnd_552647] using wordTrace_append hprefix tailTrace_552647
  have hstable : (prefixWord ++ tailWord_552647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552647).length < 2 ^ (prefixWord ++ tailWord_552647).sum := by decide
  have hdescent : baseEnd_552647 < baseStart_552647 := by decide
  rcases family_descends (prefixWord ++ tailWord_552647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552717 : List Nat := [1, 7, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_552717 : Nat := 118140960795 + 552717 * 2 ^ 59
def prefixEnd_552717 : Nat := 4983230072969 + 3 ^ 40 * 552717 * 2
def baseEnd_552717 : Nat := 189206324607479483930405

theorem tailTrace_552717 : CollatzResearch.WordTrace tailWord_552717 prefixEnd_552717 189206324607479483930405 := by
  unfold tailWord_552717
  simp only [CollatzResearch.WordTrace]
  refine ⟨20159245138608180393416405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13439496759072120262277603 20159245138608180393416405)
  ·
    refine ⟨472482307936129227970697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 20159245138608180393416405 472482307936129227970697)
    ·
      refine ⟨354361730952096920978023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 472482307936129227970697 354361730952096920978023)
      ·
        refine ⟨531542596428145381467035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354361730952096920978023 531542596428145381467035)
        ·
          refine ⟨797313894642218072200553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 531542596428145381467035 797313894642218072200553)
          ·
            refine ⟨597985420981663554150415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 797313894642218072200553 597985420981663554150415)
            ·
              refine ⟨896978131472495331225623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 597985420981663554150415 896978131472495331225623)
              ·
                refine ⟨1345467197208742996838435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 896978131472495331225623 1345467197208742996838435)
                ·
                  refine ⟨2018200795813114495257653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1345467197208742996838435 2018200795813114495257653)
                  ·
                    refine ⟨189206324607479483930405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2018200795813114495257653 189206324607479483930405)
                    ·
                      rfl

theorem cell22_552717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_552717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_552717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_552717 prefixEnd_552717 := by exact prefixLift 552717
  have htrace : WordTrace (prefixWord ++ tailWord_552717) baseStart_552717 baseEnd_552717 := by
    simpa [prefixWord, tailWord_552717, baseEnd_552717] using wordTrace_append hprefix tailTrace_552717
  have hstable : (prefixWord ++ tailWord_552717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552717).length < 2 ^ (prefixWord ++ tailWord_552717).sum := by decide
  have hdescent : baseEnd_552717 < baseStart_552717 := by decide
  rcases family_descends (prefixWord ++ tailWord_552717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552788 : List Nat := [2, 4, 1, 1, 3, 3, 1, 2, 1, 4]
def baseStart_552788 : Nat := 118140960795 + 552788 * 2 ^ 59
def prefixEnd_552788 : Nat := 4983230072969 + 3 ^ 40 * 552788 * 2
def baseEnd_552788 : Nat := 189230629358458965405187

theorem tailTrace_552788 : CollatzResearch.WordTrace tailWord_552788 prefixEnd_552788 189230629358458965405187 := by
  unfold tailWord_552788
  simp only [CollatzResearch.WordTrace]
  refine ⟨10080917360675479759625509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13441223147567306346167345 10080917360675479759625509)
  ·
    refine ⟨1890172005126652454929783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10080917360675479759625509 1890172005126652454929783)
    ·
      refine ⟨2835258007689978682394675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1890172005126652454929783 2835258007689978682394675)
      ·
        refine ⟨4252887011534968023592013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2835258007689978682394675 4252887011534968023592013)
        ·
          refine ⟨1594832629325613008847005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4252887011534968023592013 1594832629325613008847005)
          ·
            refine ⟨598062235997104878317627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1594832629325613008847005 598062235997104878317627)
            ·
              refine ⟨897093353995657317476441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 598062235997104878317627 897093353995657317476441)
              ·
                refine ⟨672820015496742988107331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 897093353995657317476441 672820015496742988107331)
                ·
                  refine ⟨1009230023245114482160997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 672820015496742988107331 1009230023245114482160997)
                  ·
                    refine ⟨189230629358458965405187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1009230023245114482160997 189230629358458965405187)
                    ·
                      rfl

theorem cell22_552788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_552788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_552788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_552788 prefixEnd_552788 := by exact prefixLift 552788
  have htrace : WordTrace (prefixWord ++ tailWord_552788) baseStart_552788 baseEnd_552788 := by
    simpa [prefixWord, tailWord_552788, baseEnd_552788] using wordTrace_append hprefix tailTrace_552788
  have hstable : (prefixWord ++ tailWord_552788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552788).length < 2 ^ (prefixWord ++ tailWord_552788).sum := by decide
  have hdescent : baseEnd_552788 < baseStart_552788 := by decide
  rcases family_descends (prefixWord ++ tailWord_552788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552799 : List Nat := [1, 1, 2, 3, 1, 4, 1, 3, 2, 4]
def baseStart_552799 : Nat := 118140960795 + 552799 * 2 ^ 59
def prefixEnd_552799 : Nat := 4983230072969 + 3 ^ 40 * 552799 * 2
def baseEnd_552799 : Nat := 189234394883258603380153

theorem tailTrace_552799 : CollatzResearch.WordTrace tailWord_552799 prefixEnd_552799 189234394883258603380153 := by
  unfold tailWord_552799
  simp only [CollatzResearch.WordTrace]
  refine ⟨20162235924311108397901451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13441490616207405598600967 20162235924311108397901451)
  ·
    refine ⟨30243353886466662596852177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20162235924311108397901451 30243353886466662596852177)
    ·
      refine ⟨22682515414849996947639133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30243353886466662596852177 22682515414849996947639133)
      ·
        refine ⟨8505943280568748855364675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22682515414849996947639133 8505943280568748855364675)
        ·
          refine ⟨12758914920853123283047013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8505943280568748855364675 12758914920853123283047013)
          ·
            refine ⟨2392296547659960615571315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12758914920853123283047013 2392296547659960615571315)
            ·
              refine ⟨3588444821489940923356973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2392296547659960615571315 3588444821489940923356973)
              ·
                refine ⟨1345666808058727846258865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3588444821489940923356973 1345666808058727846258865)
                ·
                  refine ⟨1009250106044045884694149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1345666808058727846258865 1009250106044045884694149)
                  ·
                    refine ⟨189234394883258603380153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1009250106044045884694149 189234394883258603380153)
                    ·
                      rfl

theorem cell22_552799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 4].length) (baseStart_552799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_552799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_552799 prefixEnd_552799 := by exact prefixLift 552799
  have htrace : WordTrace (prefixWord ++ tailWord_552799) baseStart_552799 baseEnd_552799 := by
    simpa [prefixWord, tailWord_552799, baseEnd_552799] using wordTrace_append hprefix tailTrace_552799
  have hstable : (prefixWord ++ tailWord_552799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552799).length < 2 ^ (prefixWord ++ tailWord_552799).sum := by decide
  have hdescent : baseEnd_552799 < baseStart_552799 := by decide
  rcases family_descends (prefixWord ++ tailWord_552799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552814 : List Nat := [4, 1, 2, 3, 1, 11]
def baseStart_552814 : Nat := 118140960795 + 552814 * 2 ^ 59
def prefixEnd_552814 : Nat := 4983230072969 + 3 ^ 40 * 552814 * 2
def baseEnd_552814 : Nat := 2336290489997574867347

theorem tailTrace_552814 : CollatzResearch.WordTrace tailWord_552814 prefixEnd_552814 2336290489997574867347 := by
  unfold tailWord_552814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2520347877407095744962187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13441855346171177306464997 2520347877407095744962187)
  ·
    refine ⟨3780521816110643617443281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2520347877407095744962187 3780521816110643617443281)
    ·
      refine ⟨2835391362082982713082461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3780521816110643617443281 2835391362082982713082461)
      ·
        refine ⟨1063271760781118517405923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2835391362082982713082461 1063271760781118517405923)
        ·
          refine ⟨1594907641171677776108885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1063271760781118517405923 1594907641171677776108885)
          ·
            refine ⟨2336290489997574867347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1594907641171677776108885 2336290489997574867347)
            ·
              rfl

theorem cell22_552814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 11].length) (baseStart_552814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_552814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_552814 prefixEnd_552814 := by exact prefixLift 552814
  have htrace : WordTrace (prefixWord ++ tailWord_552814) baseStart_552814 baseEnd_552814 := by
    simpa [prefixWord, tailWord_552814, baseEnd_552814] using wordTrace_append hprefix tailTrace_552814
  have hstable : (prefixWord ++ tailWord_552814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552814).length < 2 ^ (prefixWord ++ tailWord_552814).sum := by decide
  have hdescent : baseEnd_552814 < baseStart_552814 := by decide
  rcases family_descends (prefixWord ++ tailWord_552814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552893 : List Nat := [1, 4, 1, 2, 3, 2, 3, 1, 5]
def baseStart_552893 : Nat := 118140960795 + 552893 * 2 ^ 59
def prefixEnd_552893 : Nat := 4983230072969 + 3 ^ 40 * 552893 * 2
def baseEnd_552893 : Nat := 63088857668091230509955

theorem tailTrace_552893 : CollatzResearch.WordTrace tailWord_552893 prefixEnd_552893 63088857668091230509955 := by
  unfold tailWord_552893
  simp only [CollatzResearch.WordTrace]
  refine ⟨20165664385970562451823333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13443776257313708301215555 20165664385970562451823333)
  ·
    refine ⟨3781062072369480459716875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20165664385970562451823333 3781062072369480459716875)
    ·
      refine ⟨5671593108554220689575313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3781062072369480459716875 5671593108554220689575313)
      ·
        refine ⟨4253694831415665517181485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5671593108554220689575313 4253694831415665517181485)
        ·
          refine ⟨1595135561780874568943057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4253694831415665517181485 1595135561780874568943057)
          ·
            refine ⟨1196351671335655926707293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1595135561780874568943057 1196351671335655926707293)
            ·
              refine ⟨448631876750870972515235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1196351671335655926707293 448631876750870972515235)
              ·
                refine ⟨672947815126306458772853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 448631876750870972515235 672947815126306458772853)
                ·
                  refine ⟨63088857668091230509955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 672947815126306458772853 63088857668091230509955)
                  ·
                    rfl

theorem cell22_552893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_552893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_552893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_552893 prefixEnd_552893 := by exact prefixLift 552893
  have htrace : WordTrace (prefixWord ++ tailWord_552893) baseStart_552893 baseEnd_552893 := by
    simpa [prefixWord, tailWord_552893, baseEnd_552893] using wordTrace_append hprefix tailTrace_552893
  have hstable : (prefixWord ++ tailWord_552893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552893).length < 2 ^ (prefixWord ++ tailWord_552893).sum := by decide
  have hdescent : baseEnd_552893 < baseStart_552893 := by decide
  rcases family_descends (prefixWord ++ tailWord_552893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552906 : List Nat := [3, 1, 2, 1, 2, 1, 3, 4, 1, 4]
def baseStart_552906 : Nat := 118140960795 + 552906 * 2 ^ 59
def prefixEnd_552906 : Nat := 4983230072969 + 3 ^ 40 * 552906 * 2
def baseEnd_552906 : Nat := 189271023169945990954825

theorem tailTrace_552906 : CollatzResearch.WordTrace tailWord_552906 prefixEnd_552906 189271023169945990954825 := by
  unfold tailWord_552906
  simp only [CollatzResearch.WordTrace]
  refine ⟨5041534633730866418011643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13444092356615643781364381 5041534633730866418011643)
  ·
    refine ⟨7562301950596299627017465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5041534633730866418011643 7562301950596299627017465)
    ·
      refine ⟨5671726462947224720263099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7562301950596299627017465 5671726462947224720263099)
      ·
        refine ⟨8507589694420837080394649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5671726462947224720263099 8507589694420837080394649)
        ·
          refine ⟨6380692270815627810295987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8507589694420837080394649 6380692270815627810295987)
          ·
            refine ⟨9571038406223441715443981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6380692270815627810295987 9571038406223441715443981)
            ·
              refine ⟨3589139402333790643291493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9571038406223441715443981 3589139402333790643291493)
              ·
                refine ⟨672963637937585745617155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3589139402333790643291493 672963637937585745617155)
                ·
                  refine ⟨1009445456906378618425733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 672963637937585745617155 1009445456906378618425733)
                  ·
                    refine ⟨189271023169945990954825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1009445456906378618425733 189271023169945990954825)
                    ·
                      rfl

theorem cell22_552906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_552906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_552906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_552906 prefixEnd_552906 := by exact prefixLift 552906
  have htrace : WordTrace (prefixWord ++ tailWord_552906) baseStart_552906 baseEnd_552906 := by
    simpa [prefixWord, tailWord_552906, baseEnd_552906] using wordTrace_append hprefix tailTrace_552906
  have hstable : (prefixWord ++ tailWord_552906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552906).length < 2 ^ (prefixWord ++ tailWord_552906).sum := by decide
  have hdescent : baseEnd_552906 < baseStart_552906 := by decide
  rcases family_descends (prefixWord ++ tailWord_552906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552914 : List Nat := [3, 2, 2, 3, 3, 1, 1, 3, 1, 3]
def baseStart_552914 : Nat := 118140960795 + 552914 * 2 ^ 59
def prefixEnd_552914 : Nat := 4983230072969 + 3 ^ 40 * 552914 * 2
def baseEnd_552914 : Nat := 189273761733436636754801

theorem tailTrace_552914 : CollatzResearch.WordTrace tailWord_552914 prefixEnd_552914 189273761733436636754801 := by
  unfold tailWord_552914
  simp only [CollatzResearch.WordTrace]
  refine ⟨5041607579723620759584449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13444286879262988692225197 5041607579723620759584449)
  ·
    refine ⟨3781205684792715569688337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5041607579723620759584449 3781205684792715569688337)
    ·
      refine ⟨2835904263594536677266253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3781205684792715569688337 2835904263594536677266253)
      ·
        refine ⟨1063464098847951253974845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2835904263594536677266253 1063464098847951253974845)
        ·
          refine ⟨398799037067981720240567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1063464098847951253974845 398799037067981720240567)
          ·
            refine ⟨598198555601972580360851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 398799037067981720240567 598198555601972580360851)
            ·
              refine ⟨897297833402958870541277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 598198555601972580360851 897297833402958870541277)
              ·
                refine ⟨336486687526109576452979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 897297833402958870541277 336486687526109576452979)
                ·
                  refine ⟨504730031289164364679469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 336486687526109576452979 504730031289164364679469)
                  ·
                    refine ⟨189273761733436636754801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 504730031289164364679469 189273761733436636754801)
                    ·
                      rfl

theorem cell22_552914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_552914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_552914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_552914 prefixEnd_552914 := by exact prefixLift 552914
  have htrace : WordTrace (prefixWord ++ tailWord_552914) baseStart_552914 baseEnd_552914 := by
    simpa [prefixWord, tailWord_552914, baseEnd_552914] using wordTrace_append hprefix tailTrace_552914
  have hstable : (prefixWord ++ tailWord_552914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552914).length < 2 ^ (prefixWord ++ tailWord_552914).sum := by decide
  have hdescent : baseEnd_552914 < baseStart_552914 := by decide
  rcases family_descends (prefixWord ++ tailWord_552914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552919 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 3, 5]
def baseStart_552919 : Nat := 118140960795 + 552919 * 2 ^ 59
def prefixEnd_552919 : Nat := 4983230072969 + 3 ^ 40 * 552919 * 2
def baseEnd_552919 : Nat := 189275473335618290379785

theorem tailTrace_552919 : CollatzResearch.WordTrace tailWord_552919 prefixEnd_552919 189275473335618290379785 := by
  unfold tailWord_552919
  simp only [CollatzResearch.WordTrace]
  refine ⟨20166612683876368892269811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13444408455917579261513207 20166612683876368892269811)
  ·
    refine ⟨30249919025814553338404717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20166612683876368892269811 30249919025814553338404717)
    ·
      refine ⟨11343719634680457501901769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30249919025814553338404717 11343719634680457501901769)
      ·
        refine ⟨8507789726010343126426327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11343719634680457501901769 8507789726010343126426327)
        ·
          refine ⟨12761684589015514689639491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8507789726010343126426327 12761684589015514689639491)
          ·
            refine ⟨19142526883523272034459237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12761684589015514689639491 19142526883523272034459237)
            ·
              refine ⟨3589223790660613506461107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19142526883523272034459237 3589223790660613506461107)
              ·
                refine ⟨5383835685990920259691661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3589223790660613506461107 5383835685990920259691661)
                ·
                  refine ⟨2018938382246595097384373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5383835685990920259691661 2018938382246595097384373)
                  ·
                    refine ⟨189275473335618290379785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2018938382246595097384373 189275473335618290379785)
                    ·
                      rfl

theorem cell22_552919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_552919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_552919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_552919 prefixEnd_552919 := by exact prefixLift 552919
  have htrace : WordTrace (prefixWord ++ tailWord_552919) baseStart_552919 baseEnd_552919 := by
    simpa [prefixWord, tailWord_552919, baseEnd_552919] using wordTrace_append hprefix tailTrace_552919
  have hstable : (prefixWord ++ tailWord_552919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552919).length < 2 ^ (prefixWord ++ tailWord_552919).sum := by decide
  have hdescent : baseEnd_552919 < baseStart_552919 := by decide
  rcases family_descends (prefixWord ++ tailWord_552919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552953 : List Nat := [1, 2, 1, 3, 1, 5, 1, 3, 2, 3]
def baseStart_552953 : Nat := 118140960795 + 552953 * 2 ^ 59
def prefixEnd_552953 : Nat := 4983230072969 + 3 ^ 40 * 552953 * 2
def baseEnd_552953 : Nat := 189287112230453535029681

theorem tailTrace_552953 : CollatzResearch.WordTrace tailWord_552953 prefixEnd_552953 189287112230453535029681 := by
  unfold tailWord_552953
  simp only [CollatzResearch.WordTrace]
  refine ⟨20167852765753192699007513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13445235177168795132671675 20167852765753192699007513)
  ·
    refine ⟨15125889574314894524255635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20167852765753192699007513 15125889574314894524255635)
    ·
      refine ⟨22688834361472341786383453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15125889574314894524255635 22688834361472341786383453)
      ·
        refine ⟨8508312885552128169893795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22688834361472341786383453 8508312885552128169893795)
        ·
          refine ⟨12762469328328192254840693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8508312885552128169893795 12762469328328192254840693)
          ·
            refine ⟨1196481499530768023891315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12762469328328192254840693 1196481499530768023891315)
            ·
              refine ⟨1794722249296152035836973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1196481499530768023891315 1794722249296152035836973)
              ·
                refine ⟨673020843486057013438865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1794722249296152035836973 673020843486057013438865)
                ·
                  refine ⟨504765632614542760079149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 673020843486057013438865 504765632614542760079149)
                  ·
                    refine ⟨189287112230453535029681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 504765632614542760079149 189287112230453535029681)
                    ·
                      rfl

theorem cell22_552953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 2, 3].length) (baseStart_552953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_552953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_552953 prefixEnd_552953 := by exact prefixLift 552953
  have htrace : WordTrace (prefixWord ++ tailWord_552953) baseStart_552953 baseEnd_552953 := by
    simpa [prefixWord, tailWord_552953, baseEnd_552953] using wordTrace_append hprefix tailTrace_552953
  have hstable : (prefixWord ++ tailWord_552953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552953).length < 2 ^ (prefixWord ++ tailWord_552953).sum := by decide
  have hdescent : baseEnd_552953 < baseStart_552953 := by decide
  rcases family_descends (prefixWord ++ tailWord_552953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553000 : List Nat := [2, 1, 5, 3, 1, 2, 1, 7]
def baseStart_553000 : Nat := 118140960795 + 553000 * 2 ^ 59
def prefixEnd_553000 : Nat := 4983230072969 + 3 ^ 40 * 553000 * 2
def baseEnd_553000 : Nat := 21033689032329008789393

theorem tailTrace_553000 : CollatzResearch.WordTrace tailWord_553000 prefixEnd_553000 21033689032329008789393 := by
  unfold tailWord_553000
  simp only [CollatzResearch.WordTrace]
  refine ⟨10084783498291459862984227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13446377997721946483978969 10084783498291459862984227)
  ·
    refine ⟨15127175247437189794476341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10084783498291459862984227 15127175247437189794476341)
    ·
      refine ⟨1418172679447236543232157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15127175247437189794476341 1418172679447236543232157)
      ·
        refine ⟨531814754792713703712059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1418172679447236543232157 531814754792713703712059)
        ·
          refine ⟨797722132189070555568089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 531814754792713703712059 797722132189070555568089)
          ·
            refine ⟨598291599141802916676067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 797722132189070555568089 598291599141802916676067)
            ·
              refine ⟨897437398712704375014101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 598291599141802916676067 897437398712704375014101)
              ·
                refine ⟨21033689032329008789393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 897437398712704375014101 21033689032329008789393)
                ·
                  rfl

theorem cell22_553000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 7].length) (baseStart_553000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_553000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_553000 prefixEnd_553000 := by exact prefixLift 553000
  have htrace : WordTrace (prefixWord ++ tailWord_553000) baseStart_553000 baseEnd_553000 := by
    simpa [prefixWord, tailWord_553000, baseEnd_553000] using wordTrace_append hprefix tailTrace_553000
  have hstable : (prefixWord ++ tailWord_553000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553000).length < 2 ^ (prefixWord ++ tailWord_553000).sum := by decide
  have hdescent : baseEnd_553000 < baseStart_553000 := by decide
  rcases family_descends (prefixWord ++ tailWord_553000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553011 : List Nat := [1, 1, 1, 2, 4, 1, 4, 3, 5]
def baseStart_553011 : Nat := 118140960795 + 553011 * 2 ^ 59
def prefixEnd_553011 : Nat := 4983230072969 + 3 ^ 40 * 553011 * 2
def baseEnd_553011 : Nat := 63102322271920239026501

theorem tailTrace_553011 : CollatzResearch.WordTrace tailWord_553011 prefixEnd_553011 63102322271920239026501 := by
  unfold tailWord_553011
  simp only [CollatzResearch.WordTrace]
  refine ⟨20169968199543068604618887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13446645466362045736412591 20169968199543068604618887)
  ·
    refine ⟨30254952299314602906928331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20169968199543068604618887 30254952299314602906928331)
    ·
      refine ⟨45382428448971904360392497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30254952299314602906928331 45382428448971904360392497)
      ·
        refine ⟨34036821336728928270294373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45382428448971904360392497 34036821336728928270294373)
        ·
          refine ⟨6381904000636674050680195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34036821336728928270294373 6381904000636674050680195)
          ·
            refine ⟨9572856000955011076020293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6381904000636674050680195 9572856000955011076020293)
            ·
              refine ⟨1794910500179064576753805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9572856000955011076020293 1794910500179064576753805)
              ·
                refine ⟨673091437567149216282677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1794910500179064576753805 673091437567149216282677)
                ·
                  refine ⟨63102322271920239026501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 673091437567149216282677 63102322271920239026501)
                  ·
                    rfl

theorem cell22_553011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 5].length) (baseStart_553011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_553011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_553011 prefixEnd_553011 := by exact prefixLift 553011
  have htrace : WordTrace (prefixWord ++ tailWord_553011) baseStart_553011 baseEnd_553011 := by
    simpa [prefixWord, tailWord_553011, baseEnd_553011] using wordTrace_append hprefix tailTrace_553011
  have hstable : (prefixWord ++ tailWord_553011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553011).length < 2 ^ (prefixWord ++ tailWord_553011).sum := by decide
  have hdescent : baseEnd_553011 < baseStart_553011 := by decide
  rcases family_descends (prefixWord ++ tailWord_553011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553056 : List Nat := [2, 1, 1, 3, 2, 3, 1, 3, 6]
def baseStart_553056 : Nat := 118140960795 + 553056 * 2 ^ 59
def prefixEnd_553056 : Nat := 4983230072969 + 3 ^ 40 * 553056 * 2
def baseEnd_553056 : Nat := 63107457078465199901455

theorem tailTrace_553056 : CollatzResearch.WordTrace tailWord_553056 prefixEnd_553056 63107457078465199901455 := by
  unfold tailWord_553056
  simp only [CollatzResearch.WordTrace]
  refine ⟨10085804742190020645003511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13447739656253360860004681 10085804742190020645003511)
  ·
    refine ⟨15128707113285030967505267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10085804742190020645003511 15128707113285030967505267)
    ·
      refine ⟨22693060669927546451257901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15128707113285030967505267 22693060669927546451257901)
      ·
        refine ⟨8509897751222829919221713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22693060669927546451257901 8509897751222829919221713)
        ·
          refine ⟨6382423313417122439416285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8509897751222829919221713 6382423313417122439416285)
          ·
            refine ⟨2393408742531420914781107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6382423313417122439416285 2393408742531420914781107)
            ·
              refine ⟨3590113113797131372171661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2393408742531420914781107 3590113113797131372171661)
              ·
                refine ⟨1346292417673924264564373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3590113113797131372171661 1346292417673924264564373)
                ·
                  refine ⟨63107457078465199901455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1346292417673924264564373 63107457078465199901455)
                  ·
                    rfl

theorem cell22_553056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 6].length) (baseStart_553056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_553056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_553056 prefixEnd_553056 := by exact prefixLift 553056
  have htrace : WordTrace (prefixWord ++ tailWord_553056) baseStart_553056 baseEnd_553056 := by
    simpa [prefixWord, tailWord_553056, baseEnd_553056] using wordTrace_append hprefix tailTrace_553056
  have hstable : (prefixWord ++ tailWord_553056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553056).length < 2 ^ (prefixWord ++ tailWord_553056).sum := by decide
  have hdescent : baseEnd_553056 < baseStart_553056 := by decide
  rcases family_descends (prefixWord ++ tailWord_553056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553122 : List Nat := [3, 3, 1, 3, 1, 2, 1, 3, 2, 3]
def baseStart_553122 : Nat := 118140960795 + 553122 * 2 ^ 59
def prefixEnd_553122 : Nat := 4983230072969 + 3 ^ 40 * 553122 * 2
def baseEnd_553122 : Nat := 189344964384193427554163

theorem tailTrace_553122 : CollatzResearch.WordTrace tailWord_553122 prefixEnd_553122 189344964384193427554163 := by
  unfold tailWord_553122
  simp only [CollatzResearch.WordTrace]
  refine ⟨5043504175535233640477405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13449344468093956374606413 5043504175535233640477405)
  ·
    refine ⟨1891314065825712615179027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5043504175535233640477405 1891314065825712615179027)
    ·
      refine ⟨2836971098738568922768541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1891314065825712615179027 2836971098738568922768541)
      ·
        refine ⟨1063864162026963346038203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2836971098738568922768541 1063864162026963346038203)
        ·
          refine ⟨1595796243040445019057305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1063864162026963346038203 1595796243040445019057305)
          ·
            refine ⟨1196847182280333764292979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1595796243040445019057305 1196847182280333764292979)
            ·
              refine ⟨1795270773420500646439469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1196847182280333764292979 1795270773420500646439469)
              ·
                refine ⟨673226540032687742414801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1795270773420500646439469 673226540032687742414801)
                ·
                  refine ⟨504919905024515806811101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 673226540032687742414801 504919905024515806811101)
                  ·
                    refine ⟨189344964384193427554163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 504919905024515806811101 189344964384193427554163)
                    ·
                      rfl

theorem cell22_553122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_553122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_553122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_553122 prefixEnd_553122 := by exact prefixLift 553122
  have htrace : WordTrace (prefixWord ++ tailWord_553122) baseStart_553122 baseEnd_553122 := by
    simpa [prefixWord, tailWord_553122, baseEnd_553122] using wordTrace_append hprefix tailTrace_553122
  have hstable : (prefixWord ++ tailWord_553122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553122).length < 2 ^ (prefixWord ++ tailWord_553122).sum := by decide
  have hdescent : baseEnd_553122 < baseStart_553122 := by decide
  rcases family_descends (prefixWord ++ tailWord_553122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553146 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 9]
def baseStart_553146 : Nat := 118140960795 + 553146 * 2 ^ 59
def prefixEnd_553146 : Nat := 4983230072969 + 3 ^ 40 * 553146 * 2
def baseEnd_553146 : Nat := 63117726691555121651363

theorem tailTrace_553146 : CollatzResearch.WordTrace tailWord_553146 prefixEnd_553146 63117726691555121651363 := by
  unfold tailWord_553146
  simp only [CollatzResearch.WordTrace]
  refine ⟨5043723013513496665195823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13449928036035991107188861 5043723013513496665195823)
  ·
    refine ⟨7565584520270244997793735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5043723013513496665195823 7565584520270244997793735)
    ·
      refine ⟨11348376780405367496690603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7565584520270244997793735 11348376780405367496690603)
      ·
        refine ⟨17022565170608051245035905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11348376780405367496690603 17022565170608051245035905)
        ·
          refine ⟨12766923877956038433776929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17022565170608051245035905 12766923877956038433776929)
          ·
            refine ⟨9575192908467028825332697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12766923877956038433776929 9575192908467028825332697)
            ·
              refine ⟨7181394681350271618999523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9575192908467028825332697 7181394681350271618999523)
              ·
                refine ⟨10772092022025407428499285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7181394681350271618999523 10772092022025407428499285)
                ·
                  refine ⟨63117726691555121651363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10772092022025407428499285 63117726691555121651363)
                  ·
                    rfl

theorem cell22_553146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 9].length) (baseStart_553146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_553146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_553146 prefixEnd_553146 := by exact prefixLift 553146
  have htrace : WordTrace (prefixWord ++ tailWord_553146) baseStart_553146 baseEnd_553146 := by
    simpa [prefixWord, tailWord_553146, baseEnd_553146] using wordTrace_append hprefix tailTrace_553146
  have hstable : (prefixWord ++ tailWord_553146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553146).length < 2 ^ (prefixWord ++ tailWord_553146).sum := by decide
  have hdescent : baseEnd_553146 < baseStart_553146 := by decide
  rcases family_descends (prefixWord ++ tailWord_553146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553163 : List Nat := [1, 1, 1, 1, 3, 2, 6, 2, 5]
def baseStart_553163 : Nat := 118140960795 + 553163 * 2 ^ 59
def prefixEnd_553163 : Nat := 4983230072969 + 3 ^ 40 * 553163 * 2
def baseEnd_553163 : Nat := 63119666507360995759679

theorem tailTrace_553163 : CollatzResearch.WordTrace tailWord_553163 prefixEnd_553163 63119666507360995759679 := by
  unfold tailWord_553163
  simp only [CollatzResearch.WordTrace]
  refine ⟨20175512094992398564152143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13450341396661599042768095 20175512094992398564152143)
  ·
    refine ⟨30263268142488597846228215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20175512094992398564152143 30263268142488597846228215)
    ·
      refine ⟨45394902213732896769342323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30263268142488597846228215 45394902213732896769342323)
      ·
        refine ⟨68092353320599345154013485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45394902213732896769342323 68092353320599345154013485)
        ·
          refine ⟨25534632495224754432755057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68092353320599345154013485 25534632495224754432755057)
          ·
            refine ⟨19150974371418565824566293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25534632495224754432755057 19150974371418565824566293)
            ·
              refine ⟨897701923660245273026545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19150974371418565824566293 897701923660245273026545)
              ·
                refine ⟨673276442745183954769909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 897701923660245273026545 673276442745183954769909)
                ·
                  refine ⟨63119666507360995759679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 673276442745183954769909 63119666507360995759679)
                  ·
                    rfl

theorem cell22_553163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 5].length) (baseStart_553163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_553163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_553163 prefixEnd_553163 := by exact prefixLift 553163
  have htrace : WordTrace (prefixWord ++ tailWord_553163) baseStart_553163 baseEnd_553163 := by
    simpa [prefixWord, tailWord_553163, baseEnd_553163] using wordTrace_append hprefix tailTrace_553163
  have hstable : (prefixWord ++ tailWord_553163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553163).length < 2 ^ (prefixWord ++ tailWord_553163).sum := by decide
  have hdescent : baseEnd_553163 < baseStart_553163 := by decide
  rcases family_descends (prefixWord ++ tailWord_553163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553210 : List Nat := [3, 1, 1, 1, 1, 6, 1, 3, 1, 4]
def baseStart_553210 : Nat := 118140960795 + 553210 * 2 ^ 59
def prefixEnd_553210 : Nat := 4983230072969 + 3 ^ 40 * 553210 * 2
def baseEnd_553210 : Nat := 189375088582590531353893

theorem tailTrace_553210 : CollatzResearch.WordTrace tailWord_553210 prefixEnd_553210 189375088582590531353893 := by
  unfold tailWord_553210
  simp only [CollatzResearch.WordTrace]
  refine ⟨5044306581455531397778271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13451484217214750394075389 5044306581455531397778271)
  ·
    refine ⟨7566459872183297096667407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5044306581455531397778271 7566459872183297096667407)
    ·
      refine ⟨11349689808274945645001111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7566459872183297096667407 11349689808274945645001111)
      ·
        refine ⟨17024534712412418467501667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11349689808274945645001111 17024534712412418467501667)
        ·
          refine ⟨25536802068618627701252501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17024534712412418467501667 25536802068618627701252501)
          ·
            refine ⟨1197037596966498173496211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25536802068618627701252501 1197037596966498173496211)
            ·
              refine ⟨1795556395449747260244317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1197037596966498173496211 1795556395449747260244317)
              ·
                refine ⟨673333648293655222591619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1795556395449747260244317 673333648293655222591619)
                ·
                  refine ⟨1010000472440482833887429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 673333648293655222591619 1010000472440482833887429)
                  ·
                    refine ⟨189375088582590531353893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1010000472440482833887429 189375088582590531353893)
                    ·
                      rfl

theorem cell22_553210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_553210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_553210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_553210 prefixEnd_553210 := by exact prefixLift 553210
  have htrace : WordTrace (prefixWord ++ tailWord_553210) baseStart_553210 baseEnd_553210 := by
    simpa [prefixWord, tailWord_553210, baseEnd_553210] using wordTrace_append hprefix tailTrace_553210
  have hstable : (prefixWord ++ tailWord_553210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553210).length < 2 ^ (prefixWord ++ tailWord_553210).sum := by decide
  have hdescent : baseEnd_553210 < baseStart_553210 := by decide
  rcases family_descends (prefixWord ++ tailWord_553210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553225 : List Nat := [1, 2, 1, 1, 3, 4, 2, 4, 4]
def baseStart_553225 : Nat := 118140960795 + 553225 * 2 ^ 59
def prefixEnd_553225 : Nat := 4983230072969 + 3 ^ 40 * 553225 * 2
def baseEnd_553225 : Nat := 63126741129711830742949

theorem tailTrace_553225 : CollatzResearch.WordTrace tailWord_553225 prefixEnd_553225 63126741129711830742949 := by
  unfold tailWord_553225
  simp only [CollatzResearch.WordTrace]
  refine ⟨20177773420767783152909129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13451848947178522101939419 20177773420767783152909129)
  ·
    refine ⟨15133330065575837364681847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20177773420767783152909129 15133330065575837364681847)
    ·
      refine ⟨22699995098363756047022771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15133330065575837364681847 22699995098363756047022771)
      ·
        refine ⟨34049992647545634070534157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22699995098363756047022771 34049992647545634070534157)
        ·
          refine ⟨12768747242829612776450309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34049992647545634070534157 12768747242829612776450309)
          ·
            refine ⟨2394140108030552395584433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12768747242829612776450309 2394140108030552395584433)
            ·
              refine ⟨1795605081022914296688325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2394140108030552395584433 1795605081022914296688325)
              ·
                refine ⟨336675952691796430629061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1795605081022914296688325 336675952691796430629061)
                ·
                  refine ⟨63126741129711830742949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 336675952691796430629061 63126741129711830742949)
                  ·
                    rfl

theorem cell22_553225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 4, 4].length) (baseStart_553225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_553225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_553225 prefixEnd_553225 := by exact prefixLift 553225
  have htrace : WordTrace (prefixWord ++ tailWord_553225) baseStart_553225 baseEnd_553225 := by
    simpa [prefixWord, tailWord_553225, baseEnd_553225] using wordTrace_append hprefix tailTrace_553225
  have hstable : (prefixWord ++ tailWord_553225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553225).length < 2 ^ (prefixWord ++ tailWord_553225).sum := by decide
  have hdescent : baseEnd_553225 < baseStart_553225 := by decide
  rcases family_descends (prefixWord ++ tailWord_553225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553313 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 6, 5]
def baseStart_553313 : Nat := 118140960795 + 553313 * 2 ^ 59
def prefixEnd_553313 : Nat := 4983230072969 + 3 ^ 40 * 553313 * 2
def baseEnd_553313 : Nat := 189410347587532596028577

theorem tailTrace_553313 : CollatzResearch.WordTrace tailWord_553313 prefixEnd_553313 189410347587532596028577 := by
  unfold tailWord_553313
  simp only [CollatzResearch.WordTrace]
  refine ⟨20180983044448974182112593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13453988696299316121408395 20180983044448974182112593)
  ·
    refine ⟨15135737283336730636584445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20180983044448974182112593 15135737283336730636584445)
    ·
      refine ⟨5675901481251273988719167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15135737283336730636584445 5675901481251273988719167)
      ·
        refine ⟨8513852221876910983078751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5675901481251273988719167 8513852221876910983078751)
        ·
          refine ⟨12770778332815366474618127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8513852221876910983078751 12770778332815366474618127)
          ·
            refine ⟨19156167499223049711927191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12770778332815366474618127 19156167499223049711927191)
            ·
              refine ⟨28734251248834574567890787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19156167499223049711927191 28734251248834574567890787)
              ·
                refine ⟨43101376873251861851836181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28734251248834574567890787 43101376873251861851836181)
                ·
                  refine ⟨2020377040933681024304821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 43101376873251861851836181 2020377040933681024304821)
                  ·
                    refine ⟨189410347587532596028577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2020377040933681024304821 189410347587532596028577)
                    ·
                      rfl

theorem cell22_553313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_553313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_553313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_553313 prefixEnd_553313 := by exact prefixLift 553313
  have htrace : WordTrace (prefixWord ++ tailWord_553313) baseStart_553313 baseEnd_553313 := by
    simpa [prefixWord, tailWord_553313, baseEnd_553313] using wordTrace_append hprefix tailTrace_553313
  have hstable : (prefixWord ++ tailWord_553313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553313).length < 2 ^ (prefixWord ++ tailWord_553313).sum := by decide
  have hdescent : baseEnd_553313 < baseStart_553313 := by decide
  rcases family_descends (prefixWord ++ tailWord_553313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553375 : List Nat := [1, 1, 2, 5, 1, 1, 1, 4, 1, 5]
def baseStart_553375 : Nat := 118140960795 + 553375 * 2 ^ 59
def prefixEnd_553375 : Nat := 4983230072969 + 3 ^ 40 * 553375 * 2
def baseEnd_553375 : Nat := 189431571454585100978387

theorem tailTrace_553375 : CollatzResearch.WordTrace tailWord_553375 prefixEnd_553375 189431571454585100978387 := by
  unfold tailWord_553375
  simp only [CollatzResearch.WordTrace]
  refine ⟨20183244370224358770869579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13455496246816239180579719 20183244370224358770869579)
  ·
    refine ⟨30274866555336538156304369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20183244370224358770869579 30274866555336538156304369)
    ·
      refine ⟨22706149916502403617228277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30274866555336538156304369 22706149916502403617228277)
      ·
        refine ⟨2128701554672100339115151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22706149916502403617228277 2128701554672100339115151)
        ·
          refine ⟨3193052332008150508672727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2128701554672100339115151 3193052332008150508672727)
          ·
            refine ⟨4789578498012225763009091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3193052332008150508672727 4789578498012225763009091)
            ·
              refine ⟨7184367747018338644513637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4789578498012225763009091 7184367747018338644513637)
              ·
                refine ⟨1347068952565938495846307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7184367747018338644513637 1347068952565938495846307)
                ·
                  refine ⟨2020603428848907743769461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1347068952565938495846307 2020603428848907743769461)
                  ·
                    refine ⟨189431571454585100978387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2020603428848907743769461 189431571454585100978387)
                    ·
                      rfl

theorem cell22_553375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 5].length) (baseStart_553375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_553375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_553375 prefixEnd_553375 := by exact prefixLift 553375
  have htrace : WordTrace (prefixWord ++ tailWord_553375) baseStart_553375 baseEnd_553375 := by
    simpa [prefixWord, tailWord_553375, baseEnd_553375] using wordTrace_append hprefix tailTrace_553375
  have hstable : (prefixWord ++ tailWord_553375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553375).length < 2 ^ (prefixWord ++ tailWord_553375).sum := by decide
  have hdescent : baseEnd_553375 < baseStart_553375 := by decide
  rcases family_descends (prefixWord ++ tailWord_553375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553379 : List Nat := [1, 1, 1, 4, 1, 6, 2, 1, 1, 4]
def baseStart_553379 : Nat := 118140960795 + 553379 * 2 ^ 59
def prefixEnd_553379 : Nat := 4983230072969 + 3 ^ 40 * 553379 * 2
def baseEnd_553379 : Nat := 189432940736330423878375

theorem tailTrace_553379 : CollatzResearch.WordTrace tailWord_553379 prefixEnd_553379 189432940736330423878375 := by
  unfold tailWord_553379
  simp only [CollatzResearch.WordTrace]
  refine ⟨20183390262209867454015191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13455593508139911636010127 20183390262209867454015191)
  ·
    refine ⟨30275085393314801181022787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20183390262209867454015191 30275085393314801181022787)
    ·
      refine ⟨45412628089972201771534181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30275085393314801181022787 45412628089972201771534181)
      ·
        refine ⟨8514867766869787832162659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45412628089972201771534181 8514867766869787832162659)
        ·
          refine ⟨12772301650304681748243989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8514867766869787832162659 12772301650304681748243989)
          ·
            refine ⟨598701639858031956948937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12772301650304681748243989 598701639858031956948937)
            ·
              refine ⟨449026229893523967711703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 598701639858031956948937 449026229893523967711703)
              ·
                refine ⟨673539344840285951567555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 449026229893523967711703 673539344840285951567555)
                ·
                  refine ⟨1010309017260428927351333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 673539344840285951567555 1010309017260428927351333)
                  ·
                    refine ⟨189432940736330423878375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1010309017260428927351333 189432940736330423878375)
                    ·
                      rfl

theorem cell22_553379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 1, 4].length) (baseStart_553379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_553379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_553379 prefixEnd_553379 := by exact prefixLift 553379
  have htrace : WordTrace (prefixWord ++ tailWord_553379) baseStart_553379 baseEnd_553379 := by
    simpa [prefixWord, tailWord_553379, baseEnd_553379] using wordTrace_append hprefix tailTrace_553379
  have hstable : (prefixWord ++ tailWord_553379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553379).length < 2 ^ (prefixWord ++ tailWord_553379).sum := by decide
  have hdescent : baseEnd_553379 < baseStart_553379 := by decide
  rcases family_descends (prefixWord ++ tailWord_553379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553454 : List Nat := [4, 1, 2, 1, 2, 2, 3, 1, 3, 3]
def baseStart_553454 : Nat := 118140960795 + 553454 * 2 ^ 59
def prefixEnd_553454 : Nat := 4983230072969 + 3 ^ 40 * 553454 * 2
def baseEnd_553454 : Nat := 189458614769055228253145

theorem tailTrace_553454 : CollatzResearch.WordTrace tailWord_553454 prefixEnd_553454 189458614769055228253145 := by
  unfold tailWord_553454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2523265717117269407874427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13457417157958770175330277 2523265717117269407874427)
  ·
    refine ⟨3784898575675904111811641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2523265717117269407874427 3784898575675904111811641)
    ·
      refine ⟨2838673931756928083858731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3784898575675904111811641 2838673931756928083858731)
      ·
        refine ⟨4258010897635392125788097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2838673931756928083858731 4258010897635392125788097)
        ·
          refine ⟨3193508173226544094341073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4258010897635392125788097 3193508173226544094341073)
          ·
            refine ⟨2395131129919908070755805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3193508173226544094341073 2395131129919908070755805)
            ·
              refine ⟨898174173719965526533427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2395131129919908070755805 898174173719965526533427)
              ·
                refine ⟨1347261260579948289800141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 898174173719965526533427 1347261260579948289800141)
                ·
                  refine ⟨505222972717480608675053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1347261260579948289800141 505222972717480608675053)
                  ·
                    refine ⟨189458614769055228253145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 505222972717480608675053 189458614769055228253145)
                    ·
                      rfl

theorem cell22_553454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_553454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_553454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_553454 prefixEnd_553454 := by exact prefixLift 553454
  have htrace : WordTrace (prefixWord ++ tailWord_553454) baseStart_553454 baseEnd_553454 := by
    simpa [prefixWord, tailWord_553454, baseEnd_553454] using wordTrace_append hprefix tailTrace_553454
  have hstable : (prefixWord ++ tailWord_553454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553454).length < 2 ^ (prefixWord ++ tailWord_553454).sum := by decide
  have hdescent : baseEnd_553454 < baseStart_553454 := by decide
  rcases family_descends (prefixWord ++ tailWord_553454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553465 : List Nat := [1, 2, 1, 3, 1, 2, 2, 3, 2, 5]
def baseStart_553465 : Nat := 118140960795 + 553465 * 2 ^ 59
def prefixEnd_553465 : Nat := 4983230072969 + 3 ^ 40 * 553465 * 2
def baseEnd_553465 : Nat := 189462380293854866228111

theorem tailTrace_553465 : CollatzResearch.WordTrace tailWord_553465 prefixEnd_553465 189462380293854866228111 := by
  unfold tailWord_553465
  simp only [CollatzResearch.WordTrace]
  refine ⟨20186526939898304141645849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13457684626598869427763899 20186526939898304141645849)
  ·
    refine ⟨15139895204923728106234387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20186526939898304141645849 15139895204923728106234387)
    ·
      refine ⟨22709842807385592159351581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15139895204923728106234387 22709842807385592159351581)
      ·
        refine ⟨8516191052769597059756843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22709842807385592159351581 8516191052769597059756843)
        ·
          refine ⟨12774286579154395589635265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8516191052769597059756843 12774286579154395589635265)
          ·
            refine ⟨9580714934365796692226449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12774286579154395589635265 9580714934365796692226449)
            ·
              refine ⟨7185536200774347519169837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9580714934365796692226449 7185536200774347519169837)
              ·
                refine ⟨2694576075290380319688689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7185536200774347519169837 2694576075290380319688689)
                ·
                  refine ⟨2020932056467785239766517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2694576075290380319688689 2020932056467785239766517)
                  ·
                    refine ⟨189462380293854866228111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2020932056467785239766517 189462380293854866228111)
                    ·
                      rfl

theorem cell22_553465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 5].length) (baseStart_553465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_553465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_553465 prefixEnd_553465 := by exact prefixLift 553465
  have htrace : WordTrace (prefixWord ++ tailWord_553465) baseStart_553465 baseEnd_553465 := by
    simpa [prefixWord, tailWord_553465, baseEnd_553465] using wordTrace_append hprefix tailTrace_553465
  have hstable : (prefixWord ++ tailWord_553465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553465).length < 2 ^ (prefixWord ++ tailWord_553465).sum := by decide
  have hdescent : baseEnd_553465 < baseStart_553465 := by decide
  rcases family_descends (prefixWord ++ tailWord_553465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553527 : List Nat := [1, 1, 3, 1, 2, 3, 4, 1, 1, 5]
def baseStart_553527 : Nat := 118140960795 + 553527 * 2 ^ 59
def prefixEnd_553527 : Nat := 4983230072969 + 3 ^ 40 * 553527 * 2
def baseEnd_553527 : Nat := 189483604160907371177921

theorem tailTrace_553527 : CollatzResearch.WordTrace tailWord_553527 prefixEnd_553527 189483604160907371177921 := by
  unfold tailWord_553527
  simp only [CollatzResearch.WordTrace]
  refine ⟨20188788265673688730402835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13459192177115792486935223 20188788265673688730402835)
  ·
    refine ⟨30283182398510533095604253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20188788265673688730402835 30283182398510533095604253)
    ·
      refine ⟨11356193399441449910851595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30283182398510533095604253 11356193399441449910851595)
      ·
        refine ⟨17034290099162174866277393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11356193399441449910851595 17034290099162174866277393)
        ·
          refine ⟨12775717574371631149708045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17034290099162174866277393 12775717574371631149708045)
          ·
            refine ⟨4790894090389361681140517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12775717574371631149708045 4790894090389361681140517)
            ·
              refine ⟨898292641948005315213847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4790894090389361681140517 898292641948005315213847)
              ·
                refine ⟨1347438962922007972820771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 898292641948005315213847 1347438962922007972820771)
                ·
                  refine ⟨2021158444383011959231157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1347438962922007972820771 2021158444383011959231157)
                  ·
                    refine ⟨189483604160907371177921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2021158444383011959231157 189483604160907371177921)
                    ·
                      rfl

theorem cell22_553527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_553527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_553527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_553527 prefixEnd_553527 := by exact prefixLift 553527
  have htrace : WordTrace (prefixWord ++ tailWord_553527) baseStart_553527 baseEnd_553527 := by
    simpa [prefixWord, tailWord_553527, baseEnd_553527] using wordTrace_append hprefix tailTrace_553527
  have hstable : (prefixWord ++ tailWord_553527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553527).length < 2 ^ (prefixWord ++ tailWord_553527).sum := by decide
  have hdescent : baseEnd_553527 < baseStart_553527 := by decide
  rcases family_descends (prefixWord ++ tailWord_553527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553623 : List Nat := [1, 1, 3, 3, 2, 1, 5, 2, 1, 3]
def baseStart_553623 : Nat := 118140960795 + 553623 * 2 ^ 59
def prefixEnd_553623 : Nat := 4983230072969 + 3 ^ 40 * 553623 * 2
def baseEnd_553623 : Nat := 189516466922795120777627

theorem tailTrace_553623 : CollatzResearch.WordTrace tailWord_553623 prefixEnd_553623 189516466922795120777627 := by
  unfold tailWord_553623
  simp only [CollatzResearch.WordTrace]
  refine ⟨20192289673325897125897523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13461526448883931417265015 20192289673325897125897523)
  ·
    refine ⟨30288434509988845688846285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20192289673325897125897523 30288434509988845688846285)
    ·
      refine ⟨11358162941245817133317357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30288434509988845688846285 11358162941245817133317357)
      ·
        refine ⟨4259311102967181424994009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11358162941245817133317357 4259311102967181424994009)
        ·
          refine ⟨3194483327225386068745507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4259311102967181424994009 3194483327225386068745507)
          ·
            refine ⟨4791724990838079103118261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3194483327225386068745507 4791724990838079103118261)
            ·
              refine ⟨449224217891069915917337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4791724990838079103118261 449224217891069915917337)
              ·
                refine ⟨336918163418302436938003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 449224217891069915917337 336918163418302436938003)
                ·
                  refine ⟨505377245127453655407005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 336918163418302436938003 505377245127453655407005)
                  ·
                    refine ⟨189516466922795120777627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 505377245127453655407005 189516466922795120777627)
                    ·
                      rfl

theorem cell22_553623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 2, 1, 3].length) (baseStart_553623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_553623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_553623 prefixEnd_553623 := by exact prefixLift 553623
  have htrace : WordTrace (prefixWord ++ tailWord_553623) baseStart_553623 baseEnd_553623 := by
    simpa [prefixWord, tailWord_553623, baseEnd_553623] using wordTrace_append hprefix tailTrace_553623
  have hstable : (prefixWord ++ tailWord_553623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553623).length < 2 ^ (prefixWord ++ tailWord_553623).sum := by decide
  have hdescent : baseEnd_553623 < baseStart_553623 := by decide
  rcases family_descends (prefixWord ++ tailWord_553623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553670 : List Nat := [6, 1, 2, 1, 2, 1, 2, 2, 5]
def baseStart_553670 : Nat := 118140960795 + 553670 * 2 ^ 59
def prefixEnd_553670 : Nat := 4983230072969 + 3 ^ 40 * 553670 * 2
def baseEnd_553670 : Nat := 63177518661100888284161

theorem tailTrace_553670 : CollatzResearch.WordTrace tailWord_553670 prefixEnd_553670 63177518661100888284161 := by
  unfold tailWord_553670
  simp only [CollatzResearch.WordTrace]
  refine ⟨631062622004863254776827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13462669269437082768572309 631062622004863254776827)
  ·
    refine ⟨946593933007294882165241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 631062622004863254776827 946593933007294882165241)
    ·
      refine ⟨709945449755471161623931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 946593933007294882165241 709945449755471161623931)
      ·
        refine ⟨1064918174633206742435897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 709945449755471161623931 1064918174633206742435897)
        ·
          refine ⟨798688630974905056826923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1064918174633206742435897 798688630974905056826923)
          ·
            refine ⟨1198032946462357585240385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 798688630974905056826923 1198032946462357585240385)
            ·
              refine ⟨898524709846768188930289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1198032946462357585240385 898524709846768188930289)
              ·
                refine ⟨673893532385076141697717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 898524709846768188930289 673893532385076141697717)
                ·
                  refine ⟨63177518661100888284161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 673893532385076141697717 63177518661100888284161)
                  ·
                    rfl

theorem cell22_553670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_553670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_553670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_553670 prefixEnd_553670 := by exact prefixLift 553670
  have htrace : WordTrace (prefixWord ++ tailWord_553670) baseStart_553670 baseEnd_553670 := by
    simpa [prefixWord, tailWord_553670, baseEnd_553670] using wordTrace_append hprefix tailTrace_553670
  have hstable : (prefixWord ++ tailWord_553670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553670).length < 2 ^ (prefixWord ++ tailWord_553670).sum := by decide
  have hdescent : baseEnd_553670 < baseStart_553670 := by decide
  rcases family_descends (prefixWord ++ tailWord_553670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553711 : List Nat := [1, 1, 2, 1, 5, 4, 1, 1, 2, 4]
def baseStart_553711 : Nat := 118140960795 + 553711 * 2 ^ 59
def prefixEnd_553711 : Nat := 4983230072969 + 3 ^ 40 * 553711 * 2
def baseEnd_553711 : Nat := 189546591121192224577357

theorem tailTrace_553711 : CollatzResearch.WordTrace tailWord_553711 prefixEnd_553711 189546591121192224577357 := by
  unfold tailWord_553711
  simp only [CollatzResearch.WordTrace]
  refine ⟨20195499297007088155100987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13463666198004725436733991 20195499297007088155100987)
  ·
    refine ⟨30293248945510632232651481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20195499297007088155100987 30293248945510632232651481)
    ·
      refine ⟨22719936709132974174488611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30293248945510632232651481 22719936709132974174488611)
      ·
        refine ⟨34079905063699461261732917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22719936709132974174488611 34079905063699461261732917)
        ·
          refine ⟨3194991099721824493287461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34079905063699461261732917 3194991099721824493287461)
          ·
            refine ⟨599060831197842092491399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3194991099721824493287461 599060831197842092491399)
            ·
              refine ⟨898591246796763138737099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 599060831197842092491399 898591246796763138737099)
              ·
                refine ⟨1347886870195144708105649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 898591246796763138737099 1347886870195144708105649)
                ·
                  refine ⟨1010915152646358531079237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1347886870195144708105649 1010915152646358531079237)
                  ·
                    refine ⟨189546591121192224577357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1010915152646358531079237 189546591121192224577357)
                    ·
                      rfl

theorem cell22_553711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 4].length) (baseStart_553711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_553711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_553711 prefixEnd_553711 := by exact prefixLift 553711
  have htrace : WordTrace (prefixWord ++ tailWord_553711) baseStart_553711 baseEnd_553711 := by
    simpa [prefixWord, tailWord_553711, baseEnd_553711] using wordTrace_append hprefix tailTrace_553711
  have hstable : (prefixWord ++ tailWord_553711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553711).length < 2 ^ (prefixWord ++ tailWord_553711).sum := by decide
  have hdescent : baseEnd_553711 < baseStart_553711 := by decide
  rcases family_descends (prefixWord ++ tailWord_553711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553730 : List Nat := [3, 4, 1, 1, 1, 4, 1, 2, 2, 3]
def baseStart_553730 : Nat := 118140960795 + 553730 * 2 ^ 59
def prefixEnd_553730 : Nat := 4983230072969 + 3 ^ 40 * 553730 * 2
def baseEnd_553730 : Nat := 189553095209482508352299

theorem tailTrace_553730 : CollatzResearch.WordTrace tailWord_553730 prefixEnd_553730 189553095209482508352299 := by
  unfold tailWord_553730
  simp only [CollatzResearch.WordTrace]
  refine ⟨5049048070984563600010661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13464128189292169600028429 5049048070984563600010661)
  ·
    refine ⟨946696513309605675001999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5049048070984563600010661 946696513309605675001999)
    ·
      refine ⟨1420044769964408512502999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 946696513309605675001999 1420044769964408512502999)
      ·
        refine ⟨2130067154946612768754499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1420044769964408512502999 2130067154946612768754499)
        ·
          refine ⟨3195100732419919153131749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2130067154946612768754499 3195100732419919153131749)
          ·
            refine ⟨599081387328734841212203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3195100732419919153131749 599081387328734841212203)
            ·
              refine ⟨898622080993102261818305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 599081387328734841212203 898622080993102261818305)
              ·
                refine ⟨673966560744826696363729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 898622080993102261818305 673966560744826696363729)
                ·
                  refine ⟨505474920558620022272797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 673966560744826696363729 505474920558620022272797)
                  ·
                    refine ⟨189553095209482508352299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 505474920558620022272797 189553095209482508352299)
                    ·
                      rfl

theorem cell22_553730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_553730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_553730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_553730 prefixEnd_553730 := by exact prefixLift 553730
  have htrace : WordTrace (prefixWord ++ tailWord_553730) baseStart_553730 baseEnd_553730 := by
    simpa [prefixWord, tailWord_553730, baseEnd_553730] using wordTrace_append hprefix tailTrace_553730
  have hstable : (prefixWord ++ tailWord_553730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553730).length < 2 ^ (prefixWord ++ tailWord_553730).sum := by decide
  have hdescent : baseEnd_553730 < baseStart_553730 := by decide
  rcases family_descends (prefixWord ++ tailWord_553730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553818 : List Nat := [3, 1, 1, 2, 1, 6, 1, 2, 1, 4]
def baseStart_553818 : Nat := 118140960795 + 553818 * 2 ^ 59
def prefixEnd_553818 : Nat := 4983230072969 + 3 ^ 40 * 553818 * 2
def baseEnd_553818 : Nat := 189583219407879612152029

theorem tailTrace_553818 : CollatzResearch.WordTrace tailWord_553818 prefixEnd_553818 189583219407879612152029 := by
  unfold tailWord_553818
  simp only [CollatzResearch.WordTrace]
  refine ⟨5049850476904861357311527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13466267938412963619497405 5049850476904861357311527)
  ·
    refine ⟨7574775715357292035967291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5049850476904861357311527 7574775715357292035967291)
    ·
      refine ⟨11362163573035938053950937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7574775715357292035967291 11362163573035938053950937)
      ·
        refine ⟨8521622679776953540463203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11362163573035938053950937 8521622679776953540463203)
        ·
          refine ⟨12782434019665430310694805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8521622679776953540463203 12782434019665430310694805)
          ·
            refine ⟨599176594671817045813819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12782434019665430310694805 599176594671817045813819)
            ·
              refine ⟨898764892007725568720729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 599176594671817045813819 898764892007725568720729)
              ·
                refine ⟨674073669005794176540547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 898764892007725568720729 674073669005794176540547)
                ·
                  refine ⟨1011110503508691264810821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 674073669005794176540547 1011110503508691264810821)
                  ·
                    refine ⟨189583219407879612152029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1011110503508691264810821 189583219407879612152029)
                    ·
                      rfl

theorem cell22_553818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 1, 4].length) (baseStart_553818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_553818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_553818 prefixEnd_553818 := by exact prefixLift 553818
  have htrace : WordTrace (prefixWord ++ tailWord_553818) baseStart_553818 baseEnd_553818 := by
    simpa [prefixWord, tailWord_553818, baseEnd_553818] using wordTrace_append hprefix tailTrace_553818
  have hstable : (prefixWord ++ tailWord_553818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553818).length < 2 ^ (prefixWord ++ tailWord_553818).sum := by decide
  have hdescent : baseEnd_553818 < baseStart_553818 := by decide
  rcases family_descends (prefixWord ++ tailWord_553818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553829 : List Nat := [1, 3, 1, 3, 1, 1, 2, 3, 1, 6]
def baseStart_553829 : Nat := 118140960795 + 553829 * 2 ^ 59
def prefixEnd_553829 : Nat := 4983230072969 + 3 ^ 40 * 553829 * 2
def baseEnd_553829 : Nat := 189586984932679250126995

theorem tailTrace_553829 : CollatzResearch.WordTrace tailWord_553829 prefixEnd_553829 189586984932679250126995 := by
  unfold tailWord_553829
  simp only [CollatzResearch.WordTrace]
  refine ⟨20199803110579594307896541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13466535407053062871931027 20199803110579594307896541)
  ·
    refine ⟨7574926166467347865461203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20199803110579594307896541 7574926166467347865461203)
    ·
      refine ⟨11362389249701021798191805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7574926166467347865461203 11362389249701021798191805)
      ·
        refine ⟨4260895968637883174321927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11362389249701021798191805 4260895968637883174321927)
        ·
          refine ⟨6391343952956824761482891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4260895968637883174321927 6391343952956824761482891)
          ·
            refine ⟨9587015929435237142224337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6391343952956824761482891 9587015929435237142224337)
            ·
              refine ⟨7190261947076427856668253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9587015929435237142224337 7190261947076427856668253)
              ·
                refine ⟨2696348230153660446250595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7190261947076427856668253 2696348230153660446250595)
                ·
                  refine ⟨4044522345230490669375893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2696348230153660446250595 4044522345230490669375893)
                  ·
                    refine ⟨189586984932679250126995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4044522345230490669375893 189586984932679250126995)
                    ·
                      rfl

theorem cell22_553829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_553829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_553829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_553829 prefixEnd_553829 := by exact prefixLift 553829
  have htrace : WordTrace (prefixWord ++ tailWord_553829) baseStart_553829 baseEnd_553829 := by
    simpa [prefixWord, tailWord_553829, baseEnd_553829] using wordTrace_append hprefix tailTrace_553829
  have hstable : (prefixWord ++ tailWord_553829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553829).length < 2 ^ (prefixWord ++ tailWord_553829).sum := by decide
  have hdescent : baseEnd_553829 < baseStart_553829 := by decide
  rcases family_descends (prefixWord ++ tailWord_553829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553831 : List Nat := [1, 1, 5, 1, 2, 3, 1, 2, 1, 5]
def baseStart_553831 : Nat := 118140960795 + 553831 * 2 ^ 59
def prefixEnd_553831 : Nat := 4983230072969 + 3 ^ 40 * 553831 * 2
def baseEnd_553831 : Nat := 189587669573551911576989

theorem tailTrace_553831 : CollatzResearch.WordTrace tailWord_553831 prefixEnd_553831 189587669573551911576989 := by
  unfold tailWord_553831
  simp only [CollatzResearch.WordTrace]
  refine ⟨20199876056572348649469347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13466584037714899099646231 20199876056572348649469347)
  ·
    refine ⟨30299814084858522974204021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20199876056572348649469347 30299814084858522974204021)
    ·
      refine ⟨2840607570455486528831627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30299814084858522974204021 2840607570455486528831627)
      ·
        refine ⟨4260911355683229793247441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2840607570455486528831627 4260911355683229793247441)
        ·
          refine ⟨3195683516762422344935581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4260911355683229793247441 3195683516762422344935581)
          ·
            refine ⟨1198381318785908379350843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3195683516762422344935581 1198381318785908379350843)
            ·
              refine ⟨1797571978178862569026265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1198381318785908379350843 1797571978178862569026265)
              ·
                refine ⟨1348178983634146926769699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1797571978178862569026265 1348178983634146926769699)
                ·
                  refine ⟨2022268475451220390154549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1348178983634146926769699 2022268475451220390154549)
                  ·
                    refine ⟨189587669573551911576989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2022268475451220390154549 189587669573551911576989)
                    ·
                      rfl

theorem cell22_553831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_553831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_553831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_553831 prefixEnd_553831 := by exact prefixLift 553831
  have htrace : WordTrace (prefixWord ++ tailWord_553831) baseStart_553831 baseEnd_553831 := by
    simpa [prefixWord, tailWord_553831, baseEnd_553831] using wordTrace_append hprefix tailTrace_553831
  have hstable : (prefixWord ++ tailWord_553831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553831).length < 2 ^ (prefixWord ++ tailWord_553831).sum := by decide
  have hdescent : baseEnd_553831 < baseStart_553831 := by decide
  rcases family_descends (prefixWord ++ tailWord_553831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553861 : List Nat := [1, 3, 1, 1, 3, 5, 1, 7]
def baseStart_553861 : Nat := 118140960795 + 553861 * 2 ^ 59
def prefixEnd_553861 : Nat := 4983230072969 + 3 ^ 40 * 553861 * 2
def baseEnd_553861 : Nat := 21066437687404648147433

theorem tailTrace_553861 : CollatzResearch.WordTrace tailWord_553861 prefixEnd_553861 21066437687404648147433 := by
  unfold tailWord_553861
  simp only [CollatzResearch.WordTrace]
  refine ⟨20200970246463663773061437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13467313497642442515374291 20200970246463663773061437)
  ·
    refine ⟨7575363842423873914898039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20200970246463663773061437 7575363842423873914898039)
    ·
      refine ⟨11363045763635810872347059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7575363842423873914898039 11363045763635810872347059)
      ·
        refine ⟨17044568645453716308520589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11363045763635810872347059 17044568645453716308520589)
        ·
          refine ⟨6391713242045143615695221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17044568645453716308520589 6391713242045143615695221)
          ·
            refine ⟨599223116441732213971427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6391713242045143615695221 599223116441732213971427)
            ·
              refine ⟨898834674662598320957141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 599223116441732213971427 898834674662598320957141)
              ·
                refine ⟨21066437687404648147433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 898834674662598320957141 21066437687404648147433)
                ·
                  rfl

theorem cell22_553861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 7].length) (baseStart_553861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_553861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_553861 prefixEnd_553861 := by exact prefixLift 553861
  have htrace : WordTrace (prefixWord ++ tailWord_553861) baseStart_553861 baseEnd_553861 := by
    simpa [prefixWord, tailWord_553861, baseEnd_553861] using wordTrace_append hprefix tailTrace_553861
  have hstable : (prefixWord ++ tailWord_553861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553861).length < 2 ^ (prefixWord ++ tailWord_553861).sum := by decide
  have hdescent : baseEnd_553861 < baseStart_553861 := by decide
  rcases family_descends (prefixWord ++ tailWord_553861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553919 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 2, 8]
def baseStart_553919 : Nat := 118140960795 + 553919 * 2 ^ 59
def prefixEnd_553919 : Nat := 4983230072969 + 3 ^ 40 * 553919 * 2
def baseEnd_553919 : Nat := 189617793771949015376719

theorem tailTrace_553919 : CollatzResearch.WordTrace tailWord_553919 prefixEnd_553919 189617793771949015376719 := by
  unfold tailWord_553919
  simp only [CollatzResearch.WordTrace]
  refine ⟨20203085680253539678672811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13468723786835693119115207 20203085680253539678672811)
  ·
    refine ⟨30304628520380309518009217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20203085680253539678672811 30304628520380309518009217)
    ·
      refine ⟨22728471390285232138506913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30304628520380309518009217 22728471390285232138506913)
      ·
        refine ⟨17046353542713924103880185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22728471390285232138506913 17046353542713924103880185)
        ·
          refine ⟨12784765157035443077910139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17046353542713924103880185 12784765157035443077910139)
          ·
            refine ⟨19177147735553164616865209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12784765157035443077910139 19177147735553164616865209)
            ·
              refine ⟨14382860801664873462648907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19177147735553164616865209 14382860801664873462648907)
              ·
                refine ⟨21574291202497310193973361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14382860801664873462648907 21574291202497310193973361)
                ·
                  refine ⟨16180718401872982645480021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21574291202497310193973361 16180718401872982645480021)
                  ·
                    refine ⟨189617793771949015376719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 16180718401872982645480021 189617793771949015376719)
                    ·
                      rfl

theorem cell22_553919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 8].length) (baseStart_553919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_553919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_553919 prefixEnd_553919 := by exact prefixLift 553919
  have htrace : WordTrace (prefixWord ++ tailWord_553919) baseStart_553919 baseEnd_553919 := by
    simpa [prefixWord, tailWord_553919, baseEnd_553919] using wordTrace_append hprefix tailTrace_553919
  have hstable : (prefixWord ++ tailWord_553919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553919).length < 2 ^ (prefixWord ++ tailWord_553919).sum := by decide
  have hdescent : baseEnd_553919 < baseStart_553919 := by decide
  rcases family_descends (prefixWord ++ tailWord_553919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553981 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 6, 4]
def baseStart_553981 : Nat := 118140960795 + 553981 * 2 ^ 59
def prefixEnd_553981 : Nat := 4983230072969 + 3 ^ 40 * 553981 * 2
def baseEnd_553981 : Nat := 189639017639001520326529

theorem tailTrace_553981 : CollatzResearch.WordTrace tailWord_553981 prefixEnd_553981 189639017639001520326529 := by
  unfold tailWord_553981
  simp only [CollatzResearch.WordTrace]
  refine ⟨20205347006028924267429797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13470231337352616178286531 20205347006028924267429797)
  ·
    refine ⟨3788502563630423300143087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20205347006028924267429797 3788502563630423300143087)
    ·
      refine ⟨5682753845445634950214631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3788502563630423300143087 5682753845445634950214631)
      ·
        refine ⟨8524130768168452425321947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5682753845445634950214631 8524130768168452425321947)
        ·
          refine ⟨12786196152252678637982921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8524130768168452425321947 12786196152252678637982921)
          ·
            refine ⟨9589647114189508978487191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12786196152252678637982921 9589647114189508978487191)
            ·
              refine ⟨14384470671284263467730787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9589647114189508978487191 14384470671284263467730787)
              ·
                refine ⟨21576706006926395201596181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14384470671284263467730787 21576706006926395201596181)
                ·
                  refine ⟨1011408094074674775074821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21576706006926395201596181 1011408094074674775074821)
                  ·
                    refine ⟨189639017639001520326529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1011408094074674775074821 189639017639001520326529)
                    ·
                      rfl

theorem cell22_553981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_553981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_553981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_553981 prefixEnd_553981 := by exact prefixLift 553981
  have htrace : WordTrace (prefixWord ++ tailWord_553981) baseStart_553981 baseEnd_553981 := by
    simpa [prefixWord, tailWord_553981, baseEnd_553981] using wordTrace_append hprefix tailTrace_553981
  have hstable : (prefixWord ++ tailWord_553981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553981).length < 2 ^ (prefixWord ++ tailWord_553981).sum := by decide
  have hdescent : baseEnd_553981 < baseStart_553981 := by decide
  rcases family_descends (prefixWord ++ tailWord_553981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553996 : List Nat := [2, 2, 1, 2, 3, 2, 2, 8]
def baseStart_553996 : Nat := 118140960795 + 553996 * 2 ^ 59
def prefixEnd_553996 : Nat := 4983230072969 + 3 ^ 40 * 553996 * 2
def baseEnd_553996 : Nat := 21071572493949609022387

theorem tailTrace_553996 : CollatzResearch.WordTrace tailWord_553996 prefixEnd_553996 21071572493949609022387 := by
  unfold tailWord_553996
  simp only [CollatzResearch.WordTrace]
  refine ⟨10102947050487290914612921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13470596067316387886150561 10102947050487290914612921)
  ·
    refine ⟨7577210287865468185959691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10102947050487290914612921 7577210287865468185959691)
    ·
      refine ⟨11365815431798202278939537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7577210287865468185959691 11365815431798202278939537)
      ·
        refine ⟨8524361573848651709204653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11365815431798202278939537 8524361573848651709204653)
        ·
          refine ⟨3196635590193244390951745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8524361573848651709204653 3196635590193244390951745)
          ·
            refine ⟨2397476692644933293213809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3196635590193244390951745 2397476692644933293213809)
            ·
              refine ⟨1798107519483699969910357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2397476692644933293213809 1798107519483699969910357)
              ·
                refine ⟨21071572493949609022387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1798107519483699969910357 21071572493949609022387)
                ·
                  rfl

theorem cell22_553996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 8].length) (baseStart_553996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_553996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_553996 prefixEnd_553996 := by exact prefixLift 553996
  have htrace : WordTrace (prefixWord ++ tailWord_553996) baseStart_553996 baseEnd_553996 := by
    simpa [prefixWord, tailWord_553996, baseEnd_553996] using wordTrace_append hprefix tailTrace_553996
  have hstable : (prefixWord ++ tailWord_553996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553996).length < 2 ^ (prefixWord ++ tailWord_553996).sum := by decide
  have hdescent : baseEnd_553996 < baseStart_553996 := by decide
  rcases family_descends (prefixWord ++ tailWord_553996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553998 : List Nat := [4, 1, 1, 2, 2, 2, 1, 3, 2, 4]
def baseStart_553998 : Nat := 118140960795 + 553998 * 2 ^ 59
def prefixEnd_553998 : Nat := 4983230072969 + 3 ^ 40 * 553998 * 2
def baseEnd_553998 : Nat := 189644837086419142651477

theorem tailTrace_553998 : CollatzResearch.WordTrace tailWord_553998 prefixEnd_553998 189644837086419142651477 := by
  unfold tailWord_553998
  simp only [CollatzResearch.WordTrace]
  refine ⟨2525745880870917021349831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13470644697978224113865765 2525745880870917021349831)
  ·
    refine ⟨3788618821306375532024747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2525745880870917021349831 3788618821306375532024747)
    ·
      refine ⟨5682928231959563298037121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3788618821306375532024747 5682928231959563298037121)
      ·
        refine ⟨4262196173969672473527841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5682928231959563298037121 4262196173969672473527841)
        ·
          refine ⟨3196647130477254355145881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4262196173969672473527841 3196647130477254355145881)
          ·
            refine ⟨2397485347857940766359411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3196647130477254355145881 2397485347857940766359411)
            ·
              refine ⟨3596228021786911149539117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2397485347857940766359411 3596228021786911149539117)
              ·
                refine ⟨1348585508170091681077169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3596228021786911149539117 1348585508170091681077169)
                ·
                  refine ⟨1011439131127568760807877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1348585508170091681077169 1011439131127568760807877)
                  ·
                    refine ⟨189644837086419142651477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1011439131127568760807877 189644837086419142651477)
                    ·
                      rfl

theorem cell22_553998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_553998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_553998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_553998 prefixEnd_553998 := by exact prefixLift 553998
  have htrace : WordTrace (prefixWord ++ tailWord_553998) baseStart_553998 baseEnd_553998 := by
    simpa [prefixWord, tailWord_553998, baseEnd_553998] using wordTrace_append hprefix tailTrace_553998
  have hstable : (prefixWord ++ tailWord_553998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553998).length < 2 ^ (prefixWord ++ tailWord_553998).sum := by decide
  have hdescent : baseEnd_553998 < baseStart_553998 := by decide
  rcases family_descends (prefixWord ++ tailWord_553998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554013 : List Nat := [1, 4, 2, 2, 4, 9]
def baseStart_554013 : Nat := 118140960795 + 554013 * 2 ^ 59
def prefixEnd_554013 : Nat := 4983230072969 + 3 ^ 40 * 554013 * 2
def baseEnd_554013 : Nat := 2341357677690914858351

theorem tailTrace_554013 : CollatzResearch.WordTrace tailWord_554013 prefixEnd_554013 2341357677690914858351 := by
  unfold tailWord_554013
  simp only [CollatzResearch.WordTrace]
  refine ⟨20206514141912993732594693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13471009427941995821729795 20206514141912993732594693)
  ·
    refine ⟨3788721401608686324861505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20206514141912993732594693 3788721401608686324861505)
    ·
      refine ⟨2841541051206514743646129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3788721401608686324861505 2841541051206514743646129)
      ·
        refine ⟨2131155788404886057734597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2841541051206514743646129 2131155788404886057734597)
        ·
          refine ⟨399591710325916135825237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2131155788404886057734597 399591710325916135825237)
          ·
            refine ⟨2341357677690914858351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 399591710325916135825237 2341357677690914858351)
            ·
              rfl

theorem cell22_554013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 9].length) (baseStart_554013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554013 prefixEnd_554013 := by exact prefixLift 554013
  have htrace : WordTrace (prefixWord ++ tailWord_554013) baseStart_554013 baseEnd_554013 := by
    simpa [prefixWord, tailWord_554013, baseEnd_554013] using wordTrace_append hprefix tailTrace_554013
  have hstable : (prefixWord ++ tailWord_554013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554013).length < 2 ^ (prefixWord ++ tailWord_554013).sum := by decide
  have hdescent : baseEnd_554013 < baseStart_554013 := by decide
  rcases family_descends (prefixWord ++ tailWord_554013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554028 : List Nat := [2, 2, 1, 1, 1, 2, 4, 3, 3, 3]
def baseStart_554028 : Nat := 118140960795 + 554028 * 2 ^ 59
def prefixEnd_554028 : Nat := 4983230072969 + 3 ^ 40 * 554028 * 2
def baseEnd_554028 : Nat := 189655106699509064401385

theorem tailTrace_554028 : CollatzResearch.WordTrace tailWord_554028 prefixEnd_554028 189655106699509064401385 := by
  unfold tailWord_554028
  simp only [CollatzResearch.WordTrace]
  refine ⟨10103530618429325647195369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13471374157905767529593825 10103530618429325647195369)
  ·
    refine ⟨7577647963821994235396527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10103530618429325647195369 7577647963821994235396527)
    ·
      refine ⟨11366471945732991353094791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7577647963821994235396527 11366471945732991353094791)
      ·
        refine ⟨17049707918599487029642187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11366471945732991353094791 17049707918599487029642187)
        ·
          refine ⟨25574561877899230544463281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17049707918599487029642187 25574561877899230544463281)
          ·
            refine ⟨19180921408424422908347461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25574561877899230544463281 19180921408424422908347461)
            ·
              refine ⟨3596422764079579295315149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19180921408424422908347461 3596422764079579295315149)
              ·
                refine ⟨1348658536529842235743181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3596422764079579295315149 1348658536529842235743181)
                ·
                  refine ⟨505746951198690838403693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1348658536529842235743181 505746951198690838403693)
                  ·
                    refine ⟨189655106699509064401385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 505746951198690838403693 189655106699509064401385)
                    ·
                      rfl

theorem cell22_554028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 3].length) (baseStart_554028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554028 prefixEnd_554028 := by exact prefixLift 554028
  have htrace : WordTrace (prefixWord ++ tailWord_554028) baseStart_554028 baseEnd_554028 := by
    simpa [prefixWord, tailWord_554028, baseEnd_554028] using wordTrace_append hprefix tailTrace_554028
  have hstable : (prefixWord ++ tailWord_554028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554028).length < 2 ^ (prefixWord ++ tailWord_554028).sum := by decide
  have hdescent : baseEnd_554028 < baseStart_554028 := by decide
  rcases family_descends (prefixWord ++ tailWord_554028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554045 : List Nat := [1, 4, 1, 3, 1, 3, 1, 2, 3, 3]
def baseStart_554045 : Nat := 118140960795 + 554045 * 2 ^ 59
def prefixEnd_554045 : Nat := 4983230072969 + 3 ^ 40 * 554045 * 2
def baseEnd_554045 : Nat := 189660926146926686726333

theorem tailTrace_554045 : CollatzResearch.WordTrace tailWord_554045 prefixEnd_554045 189660926146926686726333 := by
  unfold tailWord_554045
  simp only [CollatzResearch.WordTrace]
  refine ⟨20207681277797063197759589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13471787518531375465173059 20207681277797063197759589)
  ·
    refine ⟨3788940239586949349579923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20207681277797063197759589 3788940239586949349579923)
    ·
      refine ⟨5683410359380424024369885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3788940239586949349579923 5683410359380424024369885)
      ·
        refine ⟨2131278884767659009138707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5683410359380424024369885 2131278884767659009138707)
        ·
          refine ⟨3196918327151488513708061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2131278884767659009138707 3196918327151488513708061)
          ·
            refine ⟨1198844372681808192640523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3196918327151488513708061 1198844372681808192640523)
            ·
              refine ⟨1798266559022712288960785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1198844372681808192640523 1798266559022712288960785)
              ·
                refine ⟨1348699919267034216720589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1798266559022712288960785 1348699919267034216720589)
                ·
                  refine ⟨505762469725137831270221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1348699919267034216720589 505762469725137831270221)
                  ·
                    refine ⟨189660926146926686726333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 505762469725137831270221 189660926146926686726333)
                    ·
                      rfl

theorem cell22_554045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_554045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554045 prefixEnd_554045 := by exact prefixLift 554045
  have htrace : WordTrace (prefixWord ++ tailWord_554045) baseStart_554045 baseEnd_554045 := by
    simpa [prefixWord, tailWord_554045, baseEnd_554045] using wordTrace_append hprefix tailTrace_554045
  have hstable : (prefixWord ++ tailWord_554045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554045).length < 2 ^ (prefixWord ++ tailWord_554045).sum := by decide
  have hdescent : baseEnd_554045 < baseStart_554045 := by decide
  rcases family_descends (prefixWord ++ tailWord_554045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554056 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 1, 7]
def baseStart_554056 : Nat := 118140960795 + 554056 * 2 ^ 59
def prefixEnd_554056 : Nat := 4983230072969 + 3 ^ 40 * 554056 * 2
def baseEnd_554056 : Nat := 189664691671726324701299

theorem tailTrace_554056 : CollatzResearch.WordTrace tailWord_554056 prefixEnd_554056 189664691671726324701299 := by
  unfold tailWord_554056
  simp only [CollatzResearch.WordTrace]
  refine ⟨10104041240378606038205011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13472054987171474717606681 10104041240378606038205011)
  ·
    refine ⟨15156061860567909057307517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10104041240378606038205011 15156061860567909057307517)
    ·
      refine ⟨5683523197712965896490319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15156061860567909057307517 5683523197712965896490319)
      ·
        refine ⟨8525284796569448844735479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5683523197712965896490319 8525284796569448844735479)
        ·
          refine ⟨12787927194854173267103219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8525284796569448844735479 12787927194854173267103219)
          ·
            refine ⟨19181890792281259900654829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12787927194854173267103219 19181890792281259900654829)
            ·
              refine ⟨7193209047105472462745561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19181890792281259900654829 7193209047105472462745561)
              ·
                refine ⟨5394906785329104347059171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7193209047105472462745561 5394906785329104347059171)
                ·
                  refine ⟨8092360177993656520588757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5394906785329104347059171 8092360177993656520588757)
                  ·
                    refine ⟨189664691671726324701299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8092360177993656520588757 189664691671726324701299)
                    ·
                      rfl

theorem cell22_554056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_554056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554056 prefixEnd_554056 := by exact prefixLift 554056
  have htrace : WordTrace (prefixWord ++ tailWord_554056) baseStart_554056 baseEnd_554056 := by
    simpa [prefixWord, tailWord_554056, baseEnd_554056] using wordTrace_append hprefix tailTrace_554056
  have hstable : (prefixWord ++ tailWord_554056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554056).length < 2 ^ (prefixWord ++ tailWord_554056).sum := by decide
  have hdescent : baseEnd_554056 < baseStart_554056 := by decide
  rcases family_descends (prefixWord ++ tailWord_554056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554062 : List Nat := [4, 1, 1, 1, 1, 3, 4, 3, 1, 3]
def baseStart_554062 : Nat := 118140960795 + 554062 * 2 ^ 59
def prefixEnd_554062 : Nat := 4983230072969 + 3 ^ 40 * 554062 * 2
def baseEnd_554062 : Nat := 189666745594344309051281

theorem tailTrace_554062 : CollatzResearch.WordTrace tailWord_554062 prefixEnd_554062 189666745594344309051281 := by
  unfold tailWord_554062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2526037664841934387641055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13472200879156983400752293 2526037664841934387641055)
  ·
    refine ⟨3789056497262901581461583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2526037664841934387641055 3789056497262901581461583)
    ·
      refine ⟨5683584745894352372192375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3789056497262901581461583 5683584745894352372192375)
      ·
        refine ⟨8525377118841528558288563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5683584745894352372192375 8525377118841528558288563)
        ·
          refine ⟨12788065678262292837432845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8525377118841528558288563 12788065678262292837432845)
          ·
            refine ⟨4795524629348359814037317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12788065678262292837432845 4795524629348359814037317)
            ·
              refine ⟨899160868002817465131997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4795524629348359814037317 899160868002817465131997)
              ·
                refine ⟨337185325501056549424499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 899160868002817465131997 337185325501056549424499)
                ·
                  refine ⟨505777988251584824136749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 337185325501056549424499 505777988251584824136749)
                  ·
                    refine ⟨189666745594344309051281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 505777988251584824136749 189666745594344309051281)
                    ·
                      rfl

theorem cell22_554062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_554062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554062 prefixEnd_554062 := by exact prefixLift 554062
  have htrace : WordTrace (prefixWord ++ tailWord_554062) baseStart_554062 baseEnd_554062 := by
    simpa [prefixWord, tailWord_554062, baseEnd_554062] using wordTrace_append hprefix tailTrace_554062
  have hstable : (prefixWord ++ tailWord_554062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554062).length < 2 ^ (prefixWord ++ tailWord_554062).sum := by decide
  have hdescent : baseEnd_554062 < baseStart_554062 := by decide
  rcases family_descends (prefixWord ++ tailWord_554062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554131 : List Nat := [1, 1, 1, 2, 1, 2, 14]
def baseStart_554131 : Nat := 118140960795 + 554131 * 2 ^ 59
def prefixEnd_554131 : Nat := 4983230072969 + 3 ^ 40 * 554131 * 2
def baseEnd_554131 : Nat := 7025569100164856632447

theorem tailTrace_554131 : CollatzResearch.WordTrace tailWord_554131 prefixEnd_554131 7025569100164856632447 := by
  unfold tailWord_554131
  simp only [CollatzResearch.WordTrace]
  refine ⟨20210817955485499885390247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13473878636990333256926831 20210817955485499885390247)
  ·
    refine ⟨30316226933228249828085371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20210817955485499885390247 30316226933228249828085371)
    ·
      refine ⟨45474340399842374742128057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30316226933228249828085371 45474340399842374742128057)
      ·
        refine ⟨34105755299881781056596043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45474340399842374742128057 34105755299881781056596043)
        ·
          refine ⟨51158632949822671584894065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34105755299881781056596043 51158632949822671584894065)
          ·
            refine ⟨38368974712367003688670549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51158632949822671584894065 38368974712367003688670549)
            ·
              refine ⟨7025569100164856632447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 38368974712367003688670549 7025569100164856632447)
              ·
                rfl

theorem cell22_554131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 14].length) (baseStart_554131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554131 prefixEnd_554131 := by exact prefixLift 554131
  have htrace : WordTrace (prefixWord ++ tailWord_554131) baseStart_554131 baseEnd_554131 := by
    simpa [prefixWord, tailWord_554131, baseEnd_554131] using wordTrace_append hprefix tailTrace_554131
  have hstable : (prefixWord ++ tailWord_554131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554131).length < 2 ^ (prefixWord ++ tailWord_554131).sum := by decide
  have hdescent : baseEnd_554131 < baseStart_554131 := by decide
  rcases family_descends (prefixWord ++ tailWord_554131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554135 : List Nat := [1, 1, 3, 3, 3, 1, 2, 1, 4, 3]
def baseStart_554135 : Nat := 118140960795 + 554135 * 2 ^ 59
def prefixEnd_554135 : Nat := 4983230072969 + 3 ^ 40 * 554135 * 2
def baseEnd_554135 : Nat := 189691734986196451976057

theorem tailTrace_554135 : CollatzResearch.WordTrace tailWord_554135 prefixEnd_554135 189691734986196451976057 := by
  unfold tailWord_554135
  simp only [CollatzResearch.WordTrace]
  refine ⟨20210963847471008568535859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13473975898314005712357239 20210963847471008568535859)
  ·
    refine ⟨30316445771206512852803789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20210963847471008568535859 30316445771206512852803789)
    ·
      refine ⟨11368667164202442319801421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30316445771206512852803789 11368667164202442319801421)
      ·
        refine ⟨4263250186575915869925533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11368667164202442319801421 4263250186575915869925533)
        ·
          refine ⟨1598718819965968451222075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4263250186575915869925533 1598718819965968451222075)
          ·
            refine ⟨2398078229948952676833113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1598718819965968451222075 2398078229948952676833113)
            ·
              refine ⟨1798558672461714507624835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2398078229948952676833113 1798558672461714507624835)
              ·
                refine ⟨2697838008692571761437253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1798558672461714507624835 2697838008692571761437253)
                ·
                  refine ⟨505844626629857205269485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2697838008692571761437253 505844626629857205269485)
                  ·
                    refine ⟨189691734986196451976057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 505844626629857205269485 189691734986196451976057)
                    ·
                      rfl

theorem cell22_554135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 4, 3].length) (baseStart_554135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554135 prefixEnd_554135 := by exact prefixLift 554135
  have htrace : WordTrace (prefixWord ++ tailWord_554135) baseStart_554135 baseEnd_554135 := by
    simpa [prefixWord, tailWord_554135, baseEnd_554135] using wordTrace_append hprefix tailTrace_554135
  have hstable : (prefixWord ++ tailWord_554135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554135).length < 2 ^ (prefixWord ++ tailWord_554135).sum := by decide
  have hdescent : baseEnd_554135 < baseStart_554135 := by decide
  rcases family_descends (prefixWord ++ tailWord_554135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554148 : List Nat := [2, 3, 1, 2, 3, 1, 1, 9]
def baseStart_554148 : Nat := 118140960795 + 554148 * 2 ^ 59
def prefixEnd_554148 : Nat := 4983230072969 + 3 ^ 40 * 554148 * 2
def baseEnd_554148 : Nat := 21077353905763194600113

theorem tailTrace_554148 : CollatzResearch.WordTrace tailWord_554148 prefixEnd_554148 21077353905763194600113 := by
  unfold tailWord_554148
  simp only [CollatzResearch.WordTrace]
  refine ⟨10105718998211955894379549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13474291997615941192506065 10105718998211955894379549)
  ·
    refine ⟨3789644624329483460392331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10105718998211955894379549 3789644624329483460392331)
    ·
      refine ⟨5684466936494225190588497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3789644624329483460392331 5684466936494225190588497)
      ·
        refine ⟨4263350202370668892941373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5684466936494225190588497 4263350202370668892941373)
        ·
          refine ⟨1598756325889000834853015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4263350202370668892941373 1598756325889000834853015)
          ·
            refine ⟨2398134488833501252279523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1598756325889000834853015 2398134488833501252279523)
            ·
              refine ⟨3597201733250251878419285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2398134488833501252279523 3597201733250251878419285)
              ·
                refine ⟨21077353905763194600113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3597201733250251878419285 21077353905763194600113)
                ·
                  rfl

theorem cell22_554148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 9].length) (baseStart_554148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554148 prefixEnd_554148 := by exact prefixLift 554148
  have htrace : WordTrace (prefixWord ++ tailWord_554148) baseStart_554148 baseEnd_554148 := by
    simpa [prefixWord, tailWord_554148, baseEnd_554148] using wordTrace_append hprefix tailTrace_554148
  have hstable : (prefixWord ++ tailWord_554148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554148).length < 2 ^ (prefixWord ++ tailWord_554148).sum := by decide
  have hdescent : baseEnd_554148 < baseStart_554148 := by decide
  rcases family_descends (prefixWord ++ tailWord_554148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554182 : List Nat := [6, 1, 2, 2, 11]
def baseStart_554182 : Nat := 118140960795 + 554182 * 2 ^ 59
def prefixEnd_554182 : Nat := 4983230072969 + 3 ^ 40 * 554182 * 2
def baseEnd_554182 : Nat := 780690633937053481691

theorem tailTrace_554182 : CollatzResearch.WordTrace tailWord_554182 prefixEnd_554182 780690633937053481691 := by
  unfold tailWord_554182
  simp only [CollatzResearch.WordTrace]
  refine ⟨631646189946897987359275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13475118718867157063664533 631646189946897987359275)
  ·
    refine ⟨947469284920346981038913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 631646189946897987359275 947469284920346981038913)
    ·
      refine ⟨710601963690260235779185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 947469284920346981038913 710601963690260235779185)
      ·
        refine ⟨532951472767695176834389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 710601963690260235779185 532951472767695176834389)
        ·
          refine ⟨780690633937053481691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 532951472767695176834389 780690633937053481691)
          ·
            rfl

theorem cell22_554182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 11].length) (baseStart_554182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554182 prefixEnd_554182 := by exact prefixLift 554182
  have htrace : WordTrace (prefixWord ++ tailWord_554182) baseStart_554182 baseEnd_554182 := by
    simpa [prefixWord, tailWord_554182, baseEnd_554182] using wordTrace_append hprefix tailTrace_554182
  have hstable : (prefixWord ++ tailWord_554182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554182).length < 2 ^ (prefixWord ++ tailWord_554182).sum := by decide
  have hdescent : baseEnd_554182 < baseStart_554182 := by decide
  rcases family_descends (prefixWord ++ tailWord_554182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554208 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 1, 7]
def baseStart_554208 : Nat := 118140960795 + 554208 * 2 ^ 59
def prefixEnd_554208 : Nat := 4983230072969 + 3 ^ 40 * 554208 * 2
def baseEnd_554208 : Nat := 189716724378048594900833

theorem tailTrace_554208 : CollatzResearch.WordTrace tailWord_554208 prefixEnd_554208 189716724378048594900833 := by
  unfold tailWord_554208
  simp only [CollatzResearch.WordTrace]
  refine ⟨10106813188103271017971639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13475750917471028023962185 10106813188103271017971639)
  ·
    refine ⟨15160219782154906526957459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10106813188103271017971639 15160219782154906526957459)
    ·
      refine ⟨22740329673232359790436189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15160219782154906526957459 22740329673232359790436189)
      ·
        refine ⟨8527623627462134921413571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22740329673232359790436189 8527623627462134921413571)
        ·
          refine ⟨12791435441193202382120357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8527623627462134921413571 12791435441193202382120357)
          ·
            refine ⟨2398394145223725446647567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12791435441193202382120357 2398394145223725446647567)
            ·
              refine ⟨3597591217835588169971351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2398394145223725446647567 3597591217835588169971351)
              ·
                refine ⟨5396386826753382254957027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3597591217835588169971351 5396386826753382254957027)
                ·
                  refine ⟨8094580240130073382435541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5396386826753382254957027 8094580240130073382435541)
                  ·
                    refine ⟨189716724378048594900833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8094580240130073382435541 189716724378048594900833)
                    ·
                      rfl

theorem cell22_554208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 1, 7].length) (baseStart_554208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554208 prefixEnd_554208 := by exact prefixLift 554208
  have htrace : WordTrace (prefixWord ++ tailWord_554208) baseStart_554208 baseEnd_554208 := by
    simpa [prefixWord, tailWord_554208, baseEnd_554208] using wordTrace_append hprefix tailTrace_554208
  have hstable : (prefixWord ++ tailWord_554208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554208).length < 2 ^ (prefixWord ++ tailWord_554208).sum := by decide
  have hdescent : baseEnd_554208 < baseStart_554208 := by decide
  rcases family_descends (prefixWord ++ tailWord_554208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554274 : List Nat := [3, 3, 1, 1, 4, 1, 2, 2, 1, 4]
def baseStart_554274 : Nat := 118140960795 + 554274 * 2 ^ 59
def prefixEnd_554274 : Nat := 4983230072969 + 3 ^ 40 * 554274 * 2
def baseEnd_554274 : Nat := 189739317526846422750631

theorem tailTrace_554274 : CollatzResearch.WordTrace tailWord_554274 prefixEnd_554274 189739317526846422750631 := by
  unfold tailWord_554274
  simp only [CollatzResearch.WordTrace]
  refine ⟨5054008398491858826961469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13477355729311623538563917 5054008398491858826961469)
  ·
    refine ⟨1895253149434447060110551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5054008398491858826961469 1895253149434447060110551)
    ·
      refine ⟨2842879724151670590165827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1895253149434447060110551 2842879724151670590165827)
      ·
        refine ⟨4264319586227505885248741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2842879724151670590165827 4264319586227505885248741)
        ·
          refine ⟨799559922417657353484139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4264319586227505885248741 799559922417657353484139)
          ·
            refine ⟨1199339883626486030226209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 799559922417657353484139 1199339883626486030226209)
            ·
              refine ⟨899504912719864522669657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1199339883626486030226209 899504912719864522669657)
              ·
                refine ⟨674628684539898392002243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 899504912719864522669657 674628684539898392002243)
                ·
                  refine ⟨1011943026809847588003365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 674628684539898392002243 1011943026809847588003365)
                  ·
                    refine ⟨189739317526846422750631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1011943026809847588003365 189739317526846422750631)
                    ·
                      rfl

theorem cell22_554274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_554274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554274 prefixEnd_554274 := by exact prefixLift 554274
  have htrace : WordTrace (prefixWord ++ tailWord_554274) baseStart_554274 baseEnd_554274 := by
    simpa [prefixWord, tailWord_554274, baseEnd_554274] using wordTrace_append hprefix tailTrace_554274
  have hstable : (prefixWord ++ tailWord_554274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554274).length < 2 ^ (prefixWord ++ tailWord_554274).sum := by decide
  have hdescent : baseEnd_554274 < baseStart_554274 := by decide
  rcases family_descends (prefixWord ++ tailWord_554274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554289 : List Nat := [1, 2, 2, 3, 3, 3, 1, 3, 4]
def baseStart_554289 : Nat := 118140960795 + 554289 * 2 ^ 59
def prefixEnd_554289 : Nat := 4983230072969 + 3 ^ 40 * 554289 * 2
def baseEnd_554289 : Nat := 63248150777797127875195

theorem tailTrace_554289 : CollatzResearch.WordTrace tailWord_554289 prefixEnd_554289 63248150777797127875195 := by
  unfold tailWord_554289
  simp only [CollatzResearch.WordTrace]
  refine ⟨20216580688913092869641921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13477720459275395246427947 20216580688913092869641921)
  ·
    refine ⟨15162435516684819652231441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20216580688913092869641921 15162435516684819652231441)
    ·
      refine ⟨11371826637513614739173581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15162435516684819652231441 11371826637513614739173581)
      ·
        refine ⟨4264434989067605527190093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11371826637513614739173581 4264434989067605527190093)
        ·
          refine ⟨1599163120900352072696285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4264434989067605527190093 1599163120900352072696285)
          ·
            refine ⟨599686170337632027261107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1599163120900352072696285 599686170337632027261107)
            ·
              refine ⟨899529255506448040891661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 599686170337632027261107 899529255506448040891661)
              ·
                refine ⟨337323470814918015334373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 899529255506448040891661 337323470814918015334373)
                ·
                  refine ⟨63248150777797127875195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 337323470814918015334373 63248150777797127875195)
                  ·
                    rfl

theorem cell22_554289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 3, 4].length) (baseStart_554289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554289 prefixEnd_554289 := by exact prefixLift 554289
  have htrace : WordTrace (prefixWord ++ tailWord_554289) baseStart_554289 baseEnd_554289 := by
    simpa [prefixWord, tailWord_554289, baseEnd_554289] using wordTrace_append hprefix tailTrace_554289
  have hstable : (prefixWord ++ tailWord_554289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554289).length < 2 ^ (prefixWord ++ tailWord_554289).sum := by decide
  have hdescent : baseEnd_554289 < baseStart_554289 := by decide
  rcases family_descends (prefixWord ++ tailWord_554289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554300 : List Nat := [2, 2, 2, 2, 1, 5, 8]
def baseStart_554300 : Nat := 118140960795 + 554300 * 2 ^ 59
def prefixEnd_554300 : Nat := 4983230072969 + 3 ^ 40 * 554300 * 2
def baseEnd_554300 : Nat := 7027711772525593392613

theorem tailTrace_554300 : CollatzResearch.WordTrace tailWord_554300 prefixEnd_554300 7027711772525593392613 := by
  unfold tailWord_554300
  simp only [CollatzResearch.WordTrace]
  refine ⟨10108490945936620874146177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13477987927915494498861569 10108490945936620874146177)
  ·
    refine ⟨7581368209452465655609633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10108490945936620874146177 7581368209452465655609633)
    ·
      refine ⟨5686026157089349241707225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7581368209452465655609633 5686026157089349241707225)
      ·
        refine ⟨4264519617817011931280419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5686026157089349241707225 4264519617817011931280419)
        ·
          refine ⟨6396779426725517896920629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4264519617817011931280419 6396779426725517896920629)
          ·
            refine ⟨599698071255517302836309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6396779426725517896920629 599698071255517302836309)
            ·
              refine ⟨7027711772525593392613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 599698071255517302836309 7027711772525593392613)
              ·
                rfl

theorem cell22_554300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 8].length) (baseStart_554300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554300 prefixEnd_554300 := by exact prefixLift 554300
  have htrace : WordTrace (prefixWord ++ tailWord_554300) baseStart_554300 baseEnd_554300 := by
    simpa [prefixWord, tailWord_554300, baseEnd_554300] using wordTrace_append hprefix tailTrace_554300
  have hstable : (prefixWord ++ tailWord_554300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554300).length < 2 ^ (prefixWord ++ tailWord_554300).sum := by decide
  have hdescent : baseEnd_554300 < baseStart_554300 := by decide
  rcases family_descends (prefixWord ++ tailWord_554300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554302 : List Nat := [4, 2, 1, 2, 1, 1, 3, 2, 2, 4]
def baseStart_554302 : Nat := 118140960795 + 554302 * 2 ^ 59
def prefixEnd_554302 : Nat := 4983230072969 + 3 ^ 40 * 554302 * 2
def baseEnd_554302 : Nat := 189748902499063683050545

theorem tailTrace_554302 : CollatzResearch.WordTrace tailWord_554302 prefixEnd_554302 189748902499063683050545 := by
  unfold tailWord_554302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2527131854733249511233145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13478036558577330726576773 2527131854733249511233145)
  ·
    refine ⟨1895348891049937133424859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2527131854733249511233145 1895348891049937133424859)
    ·
      refine ⟨2843023336574905700137289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1895348891049937133424859 2843023336574905700137289)
      ·
        refine ⟨2132267502431179275102967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2843023336574905700137289 2132267502431179275102967)
        ·
          refine ⟨3198401253646768912654451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2132267502431179275102967 3198401253646768912654451)
          ·
            refine ⟨4797601880470153368981677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3198401253646768912654451 4797601880470153368981677)
            ·
              refine ⟨1799100705176307513368129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4797601880470153368981677 1799100705176307513368129)
              ·
                refine ⟨1349325528882230635026097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1799100705176307513368129 1349325528882230635026097)
                ·
                  refine ⟨1011994146661672976269573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1349325528882230635026097 1011994146661672976269573)
                  ·
                    refine ⟨189748902499063683050545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1011994146661672976269573 189748902499063683050545)
                    ·
                      rfl

theorem cell22_554302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_554302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554302 prefixEnd_554302 := by exact prefixLift 554302
  have htrace : WordTrace (prefixWord ++ tailWord_554302) baseStart_554302 baseEnd_554302 := by
    simpa [prefixWord, tailWord_554302, baseEnd_554302] using wordTrace_append hprefix tailTrace_554302
  have hstable : (prefixWord ++ tailWord_554302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554302).length < 2 ^ (prefixWord ++ tailWord_554302).sum := by decide
  have hdescent : baseEnd_554302 < baseStart_554302 := by decide
  rcases family_descends (prefixWord ++ tailWord_554302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554377 : List Nat := [1, 2, 1, 1, 7, 1, 1, 1, 2, 5]
def baseStart_554377 : Nat := 118140960795 + 554377 * 2 ^ 59
def prefixEnd_554377 : Nat := 4983230072969 + 3 ^ 40 * 554377 * 2
def baseEnd_554377 : Nat := 189774576531788487425315

theorem tailTrace_554377 : CollatzResearch.WordTrace tailWord_554377 prefixEnd_554377 189774576531788487425315 := by
  unfold tailWord_554377
  simp only [CollatzResearch.WordTrace]
  refine ⟨20219790312594283898845385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13479860208396189265896923 20219790312594283898845385)
  ·
    refine ⟨15164842734445712924134039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20219790312594283898845385 15164842734445712924134039)
    ·
      refine ⟨22747264101668569386201059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15164842734445712924134039 22747264101668569386201059)
      ·
        refine ⟨34120896152502854079301589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22747264101668569386201059 34120896152502854079301589)
        ·
          refine ⟨799708503574285642483631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 34120896152502854079301589 799708503574285642483631)
          ·
            refine ⟨1199562755361428463725447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 799708503574285642483631 1199562755361428463725447)
            ·
              refine ⟨1799344133042142695588171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1199562755361428463725447 1799344133042142695588171)
              ·
                refine ⟨2699016199563214043382257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1799344133042142695588171 2699016199563214043382257)
                ·
                  refine ⟨2024262149672410532536693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2699016199563214043382257 2024262149672410532536693)
                  ·
                    refine ⟨189774576531788487425315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2024262149672410532536693 189774576531788487425315)
                    ·
                      rfl

theorem cell22_554377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 5].length) (baseStart_554377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554377 prefixEnd_554377 := by exact prefixLift 554377
  have htrace : WordTrace (prefixWord ++ tailWord_554377) baseStart_554377 baseEnd_554377 := by
    simpa [prefixWord, tailWord_554377, baseEnd_554377] using wordTrace_append hprefix tailTrace_554377
  have hstable : (prefixWord ++ tailWord_554377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554377).length < 2 ^ (prefixWord ++ tailWord_554377).sum := by decide
  have hdescent : baseEnd_554377 < baseStart_554377 := by decide
  rcases family_descends (prefixWord ++ tailWord_554377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554405 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 3, 5]
def baseStart_554405 : Nat := 118140960795 + 554405 * 2 ^ 59
def prefixEnd_554405 : Nat := 4983230072969 + 3 ^ 40 * 554405 * 2
def baseEnd_554405 : Nat := 189784161504005747725229

theorem tailTrace_554405 : CollatzResearch.WordTrace tailWord_554405 prefixEnd_554405 189784161504005747725229 := by
  unfold tailWord_554405
  simp only [CollatzResearch.WordTrace]
  refine ⟨20220811556492844680864669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13480541037661896453909779 20220811556492844680864669)
  ·
    refine ⟨7582804333684816755324251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20220811556492844680864669 7582804333684816755324251)
    ·
      refine ⟨11374206500527225132986377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7582804333684816755324251 11374206500527225132986377)
      ·
        refine ⟨8530654875395418849739783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11374206500527225132986377 8530654875395418849739783)
        ·
          refine ⟨12795982313093128274609675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8530654875395418849739783 12795982313093128274609675)
          ·
            refine ⟨19193973469639692411914513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12795982313093128274609675 19193973469639692411914513)
            ·
              refine ⟨14395480102229769308935885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19193973469639692411914513 14395480102229769308935885)
              ·
                refine ⟨5398305038336163490850957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14395480102229769308935885 5398305038336163490850957)
                ·
                  refine ⟨2024364389376061309069109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5398305038336163490850957 2024364389376061309069109)
                  ·
                    refine ⟨189784161504005747725229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2024364389376061309069109 189784161504005747725229)
                    ·
                      rfl

theorem cell22_554405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_554405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554405 prefixEnd_554405 := by exact prefixLift 554405
  have htrace : WordTrace (prefixWord ++ tailWord_554405) baseStart_554405 baseEnd_554405 := by
    simpa [prefixWord, tailWord_554405, baseEnd_554405] using wordTrace_append hprefix tailTrace_554405
  have hstable : (prefixWord ++ tailWord_554405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554405).length < 2 ^ (prefixWord ++ tailWord_554405).sum := by decide
  have hdescent : baseEnd_554405 < baseStart_554405 := by decide
  rcases family_descends (prefixWord ++ tailWord_554405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554454 : List Nat := [5, 2, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_554454 : Nat := 118140960795 + 554454 * 2 ^ 59
def prefixEnd_554454 : Nat := 4983230072969 + 3 ^ 40 * 554454 * 2
def baseEnd_554454 : Nat := 189800935205385953250079

theorem tailTrace_554454 : CollatzResearch.WordTrace tailWord_554454 prefixEnd_554454 189800935205385953250079 := by
  unfold tailWord_554454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1263912420832207878087401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13481732488876884032932277 1263912420832207878087401)
  ·
    refine ⟨947934315624155908565551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1263912420832207878087401 947934315624155908565551)
    ·
      refine ⟨1421901473436233862848327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 947934315624155908565551 1421901473436233862848327)
      ·
        refine ⟨2132852210154350794272491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1421901473436233862848327 2132852210154350794272491)
        ·
          refine ⟨3199278315231526191408737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2132852210154350794272491 3199278315231526191408737)
          ·
            refine ⟨2399458736423644643556553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3199278315231526191408737 2399458736423644643556553)
            ·
              refine ⟨1799594052317733482667415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2399458736423644643556553 1799594052317733482667415)
              ·
                refine ⟨2699391078476600224001123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1799594052317733482667415 2699391078476600224001123)
                ·
                  refine ⟨4049086617714900336001685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2699391078476600224001123 4049086617714900336001685)
                  ·
                    refine ⟨189800935205385953250079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4049086617714900336001685 189800935205385953250079)
                    ·
                      rfl

theorem cell22_554454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_554454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554454 prefixEnd_554454 := by exact prefixLift 554454
  have htrace : WordTrace (prefixWord ++ tailWord_554454) baseStart_554454 baseEnd_554454 := by
    simpa [prefixWord, tailWord_554454, baseEnd_554454] using wordTrace_append hprefix tailTrace_554454
  have hstable : (prefixWord ++ tailWord_554454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554454).length < 2 ^ (prefixWord ++ tailWord_554454).sum := by decide
  have hdescent : baseEnd_554454 < baseStart_554454 := by decide
  rcases family_descends (prefixWord ++ tailWord_554454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554574 : List Nat := [4, 1, 1, 1, 1, 2, 1, 4, 4, 3]
def baseStart_554574 : Nat := 118140960795 + 554574 * 2 ^ 59
def prefixEnd_554574 : Nat := 4983230072969 + 3 ^ 40 * 554574 * 2
def baseEnd_554574 : Nat := 189842013657745640249711

theorem tailTrace_554574 : CollatzResearch.WordTrace tailWord_554574 prefixEnd_554574 189842013657745640249711 := by
  unfold tailWord_554574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2528371936610073317970847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13484650328587057695844517 2528371936610073317970847)
  ·
    refine ⟨3792557904915109976956271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2528371936610073317970847 3792557904915109976956271)
    ·
      refine ⟨5688836857372664965434407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3792557904915109976956271 5688836857372664965434407)
      ·
        refine ⟨8533255286058997448151611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5688836857372664965434407 8533255286058997448151611)
        ·
          refine ⟨12799882929088496172227417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8533255286058997448151611 12799882929088496172227417)
          ·
            refine ⟨9599912196816372129170563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12799882929088496172227417 9599912196816372129170563)
            ·
              refine ⟨14399868295224558193755845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9599912196816372129170563 14399868295224558193755845)
              ·
                refine ⟨2699975305354604661329221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14399868295224558193755845 2699975305354604661329221)
                ·
                  refine ⟨506245369753988373999229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2699975305354604661329221 506245369753988373999229)
                  ·
                    refine ⟨189842013657745640249711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 506245369753988373999229 189842013657745640249711)
                    ·
                      rfl

theorem cell22_554574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_554574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554574 prefixEnd_554574 := by exact prefixLift 554574
  have htrace : WordTrace (prefixWord ++ tailWord_554574) baseStart_554574 baseEnd_554574 := by
    simpa [prefixWord, tailWord_554574, baseEnd_554574] using wordTrace_append hprefix tailTrace_554574
  have hstable : (prefixWord ++ tailWord_554574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554574).length < 2 ^ (prefixWord ++ tailWord_554574).sum := by decide
  have hdescent : baseEnd_554574 < baseStart_554574 := by decide
  rcases family_descends (prefixWord ++ tailWord_554574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554578 : List Nat := [3, 2, 2, 1, 2, 4, 2, 1, 1, 4]
def baseStart_554578 : Nat := 118140960795 + 554578 * 2 ^ 59
def prefixEnd_554578 : Nat := 4983230072969 + 3 ^ 40 * 554578 * 2
def baseEnd_554578 : Nat := 189843382939490963149699

theorem tailTrace_554578 : CollatzResearch.WordTrace tailWord_554578 prefixEnd_554578 189843382939490963149699 := by
  unfold tailWord_554578
  simp only [CollatzResearch.WordTrace]
  refine ⟨5056780346216523806728097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13484747589910730151274925 5056780346216523806728097)
  ·
    refine ⟨3792585259662392855046073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5056780346216523806728097 3792585259662392855046073)
    ·
      refine ⟨2844438944746794641284555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3792585259662392855046073 2844438944746794641284555)
      ·
        refine ⟨4266658417120191961926833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2844438944746794641284555 4266658417120191961926833)
        ·
          refine ⟨3199993812840143971445125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4266658417120191961926833 3199993812840143971445125)
          ·
            refine ⟨599998839907526994645961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3199993812840143971445125 599998839907526994645961)
            ·
              refine ⟨449999129930645245984471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 599998839907526994645961 449999129930645245984471)
              ·
                refine ⟨674998694895967868976707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 449999129930645245984471 674998694895967868976707)
                ·
                  refine ⟨1012498042343951803465061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 674998694895967868976707 1012498042343951803465061)
                  ·
                    refine ⟨189843382939490963149699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1012498042343951803465061 189843382939490963149699)
                    ·
                      rfl

theorem cell22_554578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_554578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554578 prefixEnd_554578 := by exact prefixLift 554578
  have htrace : WordTrace (prefixWord ++ tailWord_554578) baseStart_554578 baseEnd_554578 := by
    simpa [prefixWord, tailWord_554578, baseEnd_554578] using wordTrace_append hprefix tailTrace_554578
  have hstable : (prefixWord ++ tailWord_554578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554578).length < 2 ^ (prefixWord ++ tailWord_554578).sum := by decide
  have hdescent : baseEnd_554578 < baseStart_554578 := by decide
  rcases family_descends (prefixWord ++ tailWord_554578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554582 : List Nat := [5, 2, 2, 2, 2, 1, 1, 2, 5]
def baseStart_554582 : Nat := 118140960795 + 554582 * 2 ^ 59
def prefixEnd_554582 : Nat := 4983230072969 + 3 ^ 40 * 554582 * 2
def baseEnd_554582 : Nat := 63281584073745428683229

theorem tailTrace_554582 : CollatzResearch.WordTrace tailWord_554582 prefixEnd_554582 63281584073745428683229 := by
  unfold tailWord_554582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1264204204803225244378625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13484844851234402606705333 1264204204803225244378625)
  ·
    refine ⟨948153153602418933283969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1264204204803225244378625 948153153602418933283969)
    ·
      refine ⟨711114865201814199962977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 948153153602418933283969 711114865201814199962977)
      ·
        refine ⟨533336148901360649972233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 711114865201814199962977 533336148901360649972233)
        ·
          refine ⟨400002111676020487479175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 533336148901360649972233 400002111676020487479175)
          ·
            refine ⟨600003167514030731218763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400002111676020487479175 600003167514030731218763)
            ·
              refine ⟨900004751271046096828145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 600003167514030731218763 900004751271046096828145)
              ·
                refine ⟨675003563453284572621109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 900004751271046096828145 675003563453284572621109)
                ·
                  refine ⟨63281584073745428683229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 675003563453284572621109 63281584073745428683229)
                  ·
                    rfl

theorem cell22_554582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_554582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554582 prefixEnd_554582 := by exact prefixLift 554582
  have htrace : WordTrace (prefixWord ++ tailWord_554582) baseStart_554582 baseEnd_554582 := by
    simpa [prefixWord, tailWord_554582, baseEnd_554582] using wordTrace_append hprefix tailTrace_554582
  have hstable : (prefixWord ++ tailWord_554582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554582).length < 2 ^ (prefixWord ++ tailWord_554582).sum := by decide
  have hdescent : baseEnd_554582 < baseStart_554582 := by decide
  rcases family_descends (prefixWord ++ tailWord_554582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554608 : List Nat := [2, 1, 1, 1, 6, 2, 3, 1, 2, 3]
def baseStart_554608 : Nat := 118140960795 + 554608 * 2 ^ 59
def prefixEnd_554608 : Nat := 4983230072969 + 3 ^ 40 * 554608 * 2
def baseEnd_554608 : Nat := 189853652552580884899607

theorem tailTrace_554608 : CollatzResearch.WordTrace tailWord_554608 prefixEnd_554608 189853652552580884899607 := by
  unfold tailWord_554608
  simp only [CollatzResearch.WordTrace]
  refine ⟨10114107787378705175252239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13485477049838273567002985 10114107787378705175252239)
  ·
    refine ⟨15171161681068057762878359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10114107787378705175252239 15171161681068057762878359)
    ·
      refine ⟨22756742521602086644317539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15171161681068057762878359 22756742521602086644317539)
      ·
        refine ⟨34135113782403129966476309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22756742521602086644317539 34135113782403129966476309)
        ·
          refine ⟨1600083458550146717178577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34135113782403129966476309 1600083458550146717178577)
          ·
            refine ⟨1200062593912610037883933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1600083458550146717178577 1200062593912610037883933)
            ·
              refine ⟨450023472717228764206475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1200062593912610037883933 450023472717228764206475)
              ·
                refine ⟨675035209075843146309713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 450023472717228764206475 675035209075843146309713)
                ·
                  refine ⟨506276406806882359732285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 675035209075843146309713 506276406806882359732285)
                  ·
                    refine ⟨189853652552580884899607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 506276406806882359732285 189853652552580884899607)
                    ·
                      rfl

theorem cell22_554608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 2, 3].length) (baseStart_554608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554608 prefixEnd_554608 := by exact prefixLift 554608
  have htrace : WordTrace (prefixWord ++ tailWord_554608) baseStart_554608 baseEnd_554608 := by
    simpa [prefixWord, tailWord_554608, baseEnd_554608] using wordTrace_append hprefix tailTrace_554608
  have hstable : (prefixWord ++ tailWord_554608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554608).length < 2 ^ (prefixWord ++ tailWord_554608).sum := by decide
  have hdescent : baseEnd_554608 < baseStart_554608 := by decide
  rcases family_descends (prefixWord ++ tailWord_554608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554619 : List Nat := [1, 1, 1, 1, 1, 4, 3, 4, 3, 3]
def baseStart_554619 : Nat := 118140960795 + 554619 * 2 ^ 59
def prefixEnd_554619 : Nat := 4983230072969 + 3 ^ 40 * 554619 * 2
def baseEnd_554619 : Nat := 189857418077380522874573

theorem tailTrace_554619 : CollatzResearch.WordTrace tailWord_554619 prefixEnd_554619 189857418077380522874573 := by
  unfold tailWord_554619
  simp only [CollatzResearch.WordTrace]
  refine ⟨20228616777717559229154911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13485744518478372819436607 20228616777717559229154911)
  ·
    refine ⟨30342925166576338843732367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20228616777717559229154911 30342925166576338843732367)
    ·
      refine ⟨45514387749864508265598551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30342925166576338843732367 45514387749864508265598551)
      ·
        refine ⟨68271581624796762398397827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45514387749864508265598551 68271581624796762398397827)
        ·
          refine ⟨102407372437195143597596741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68271581624796762398397827 102407372437195143597596741)
          ·
            refine ⟨19201382331974089424549389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 102407372437195143597596741 19201382331974089424549389)
            ·
              refine ⟨7200518374490283534206021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19201382331974089424549389 7200518374490283534206021)
              ·
                refine ⟨1350097195216928162663629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7200518374490283534206021 1350097195216928162663629)
                ·
                  refine ⟨506286448206348060998861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1350097195216928162663629 506286448206348060998861)
                  ·
                    refine ⟨189857418077380522874573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 506286448206348060998861 189857418077380522874573)
                    ·
                      rfl

theorem cell22_554619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 3, 3].length) (baseStart_554619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554619 prefixEnd_554619 := by exact prefixLift 554619
  have htrace : WordTrace (prefixWord ++ tailWord_554619) baseStart_554619 baseEnd_554619 := by
    simpa [prefixWord, tailWord_554619, baseEnd_554619] using wordTrace_append hprefix tailTrace_554619
  have hstable : (prefixWord ++ tailWord_554619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554619).length < 2 ^ (prefixWord ++ tailWord_554619).sum := by decide
  have hdescent : baseEnd_554619 < baseStart_554619 := by decide
  rcases family_descends (prefixWord ++ tailWord_554619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554621 : List Nat := [1, 4, 1, 1, 4, 3, 2, 6]
def baseStart_554621 : Nat := 118140960795 + 554621 * 2 ^ 59
def prefixEnd_554621 : Nat := 4983230072969 + 3 ^ 40 * 554621 * 2
def baseEnd_554621 : Nat := 21095344746472576036063

theorem tailTrace_554621 : CollatzResearch.WordTrace tailWord_554621 prefixEnd_554621 21095344746472576036063 := by
  unfold tailWord_554621
  simp only [CollatzResearch.WordTrace]
  refine ⟨20228689723710313570727717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13485793149140209047151811 20228689723710313570727717)
  ·
    refine ⟨3792879323195683794511447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20228689723710313570727717 3792879323195683794511447)
    ·
      refine ⟨5689318984793525691767171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3792879323195683794511447 5689318984793525691767171)
      ·
        refine ⟨8533978477190288537650757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5689318984793525691767171 8533978477190288537650757)
        ·
          refine ⟨1600120964473179100809517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8533978477190288537650757 1600120964473179100809517)
          ·
            refine ⟨600045361677442162803569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1600120964473179100809517 600045361677442162803569)
            ·
              refine ⟨450034021258081622102677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 600045361677442162803569 450034021258081622102677)
              ·
                refine ⟨21095344746472576036063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 450034021258081622102677 21095344746472576036063)
                ·
                  rfl

theorem cell22_554621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 6].length) (baseStart_554621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554621 prefixEnd_554621 := by exact prefixLift 554621
  have htrace : WordTrace (prefixWord ++ tailWord_554621) baseStart_554621 baseEnd_554621 := by
    simpa [prefixWord, tailWord_554621, baseEnd_554621] using wordTrace_append hprefix tailTrace_554621
  have hstable : (prefixWord ++ tailWord_554621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554621).length < 2 ^ (prefixWord ++ tailWord_554621).sum := by decide
  have hdescent : baseEnd_554621 < baseStart_554621 := by decide
  rcases family_descends (prefixWord ++ tailWord_554621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554711 : List Nat := [1, 1, 3, 2, 1, 3, 3, 4, 4]
def baseStart_554711 : Nat := 118140960795 + 554711 * 2 ^ 59
def prefixEnd_554711 : Nat := 4983230072969 + 3 ^ 40 * 554711 * 2
def baseEnd_554711 : Nat := 63296303852507649858097

theorem tailTrace_554711 : CollatzResearch.WordTrace tailWord_554711 prefixEnd_554711 63296303852507649858097 := by
  unfold tailWord_554711
  simp only [CollatzResearch.WordTrace]
  refine ⟨20231972293384258941503987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13487981528922839294335991 20231972293384258941503987)
  ·
    refine ⟨30347958440076388412255981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20231972293384258941503987 30347958440076388412255981)
    ·
      refine ⟨11380484415028645654595993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30347958440076388412255981 11380484415028645654595993)
      ·
        refine ⟨8535363311271484240946995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11380484415028645654595993 8535363311271484240946995)
        ·
          refine ⟨12803044966907226361420493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8535363311271484240946995 12803044966907226361420493)
          ·
            refine ⟨4801141862590209885532685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12803044966907226361420493 4801141862590209885532685)
            ·
              refine ⟨1800428198471328707074757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4801141862590209885532685 1800428198471328707074757)
              ·
                refine ⟨337580287213374132576517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1800428198471328707074757 337580287213374132576517)
                ·
                  refine ⟨63296303852507649858097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 337580287213374132576517 63296303852507649858097)
                  ·
                    rfl

theorem cell22_554711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 4, 4].length) (baseStart_554711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554711 prefixEnd_554711 := by exact prefixLift 554711
  have htrace : WordTrace (prefixWord ++ tailWord_554711) baseStart_554711 baseEnd_554711 := by
    simpa [prefixWord, tailWord_554711, baseEnd_554711] using wordTrace_append hprefix tailTrace_554711
  have hstable : (prefixWord ++ tailWord_554711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554711).length < 2 ^ (prefixWord ++ tailWord_554711).sum := by decide
  have hdescent : baseEnd_554711 < baseStart_554711 := by decide
  rcases family_descends (prefixWord ++ tailWord_554711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554724 : List Nat := [2, 3, 1, 1, 1, 3, 2, 2, 1, 6]
def baseStart_554724 : Nat := 118140960795 + 554724 * 2 ^ 59
def prefixEnd_554724 : Nat := 4983230072969 + 3 ^ 40 * 554724 * 2
def baseEnd_554724 : Nat := 189893361723195248999251

theorem tailTrace_554724 : CollatzResearch.WordTrace tailWord_554724 prefixEnd_554724 189893361723195248999251 := by
  unfold tailWord_554724
  simp only [CollatzResearch.WordTrace]
  refine ⟨10116223221168581080863613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13488297628224774774484817 10116223221168581080863613)
  ·
    refine ⟨3793583707938217905323855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10116223221168581080863613 3793583707938217905323855)
    ·
      refine ⟨5690375561907326857985783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3793583707938217905323855 5690375561907326857985783)
      ·
        refine ⟨8535563342860990286978675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5690375561907326857985783 8535563342860990286978675)
        ·
          refine ⟨12803345014291485430468013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8535563342860990286978675 12803345014291485430468013)
          ·
            refine ⟨4801254380359307036425505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12803345014291485430468013 4801254380359307036425505)
            ·
              refine ⟨3600940785269480277319129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4801254380359307036425505 3600940785269480277319129)
              ·
                refine ⟨2700705588952110207989347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3600940785269480277319129 2700705588952110207989347)
                ·
                  refine ⟨4051058383428165311984021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2700705588952110207989347 4051058383428165311984021)
                  ·
                    refine ⟨189893361723195248999251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4051058383428165311984021 189893361723195248999251)
                    ·
                      rfl

theorem cell22_554724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_554724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554724 prefixEnd_554724 := by exact prefixLift 554724
  have htrace : WordTrace (prefixWord ++ tailWord_554724) baseStart_554724 baseEnd_554724 := by
    simpa [prefixWord, tailWord_554724, baseEnd_554724] using wordTrace_append hprefix tailTrace_554724
  have hstable : (prefixWord ++ tailWord_554724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554724).length < 2 ^ (prefixWord ++ tailWord_554724).sum := by decide
  have hdescent : baseEnd_554724 < baseStart_554724 := by decide
  rcases family_descends (prefixWord ++ tailWord_554724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554788 : List Nat := [2, 3, 1, 3, 2, 1, 2, 2, 3, 3]
def baseStart_554788 : Nat := 118140960795 + 554788 * 2 ^ 59
def prefixEnd_554788 : Nat := 4983230072969 + 3 ^ 40 * 554788 * 2
def baseEnd_554788 : Nat := 189915270231120415399055

theorem tailTrace_554788 : CollatzResearch.WordTrace tailWord_554788 prefixEnd_554788 189915270231120415399055 := by
  unfold tailWord_554788
  simp only [CollatzResearch.WordTrace]
  refine ⟨10117390357052650546028509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13489853809403534061371345 10117390357052650546028509)
  ·
    refine ⟨3794021383894743954760691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10117390357052650546028509 3794021383894743954760691)
    ·
      refine ⟨5691032075842115932141037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3794021383894743954760691 5691032075842115932141037)
      ·
        refine ⟨2134137028440793474552889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5691032075842115932141037 2134137028440793474552889)
        ·
          refine ⟨1600602771330595105914667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2134137028440793474552889 1600602771330595105914667)
          ·
            refine ⟨2400904156995892658872001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1600602771330595105914667 2400904156995892658872001)
            ·
              refine ⟨1800678117746919494154001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2400904156995892658872001 1800678117746919494154001)
              ·
                refine ⟨1350508588310189620615501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1800678117746919494154001 1350508588310189620615501)
                ·
                  refine ⟨506440720616321107730813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1350508588310189620615501 506440720616321107730813)
                  ·
                    refine ⟨189915270231120415399055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 506440720616321107730813 189915270231120415399055)
                    ·
                      rfl

theorem cell22_554788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_554788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554788 prefixEnd_554788 := by exact prefixLift 554788
  have htrace : WordTrace (prefixWord ++ tailWord_554788) baseStart_554788 baseEnd_554788 := by
    simpa [prefixWord, tailWord_554788, baseEnd_554788] using wordTrace_append hprefix tailTrace_554788
  have hstable : (prefixWord ++ tailWord_554788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554788).length < 2 ^ (prefixWord ++ tailWord_554788).sum := by decide
  have hdescent : baseEnd_554788 < baseStart_554788 := by decide
  rcases family_descends (prefixWord ++ tailWord_554788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554822 : List Nat := [6, 1, 1, 2, 1, 1, 3, 1, 3, 3]
def baseStart_554822 : Nat := 118140960795 + 554822 * 2 ^ 59
def prefixEnd_554822 : Nat := 4983230072969 + 3 ^ 40 * 554822 * 2
def baseEnd_554822 : Nat := 189926909125955660048951

theorem tailTrace_554822 : CollatzResearch.WordTrace tailWord_554822 prefixEnd_554822 189926909125955660048951 := by
  unfold tailWord_554822
  simp only [CollatzResearch.WordTrace]
  refine ⟨632375649874441403087335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13490680530654749932529813 632375649874441403087335)
  ·
    refine ⟨948563474811662104631003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 632375649874441403087335 948563474811662104631003)
    ·
      refine ⟨1422845212217493156946505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 948563474811662104631003 1422845212217493156946505)
      ·
        refine ⟨1067133909163119867709879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1422845212217493156946505 1067133909163119867709879)
        ·
          refine ⟨1600700863744679801564819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1067133909163119867709879 1600700863744679801564819)
          ·
            refine ⟨2401051295617019702347229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1600700863744679801564819 2401051295617019702347229)
            ·
              refine ⟨900394235856382388380211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2401051295617019702347229 900394235856382388380211)
              ·
                refine ⟨1350591353784573582570317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 900394235856382388380211 1350591353784573582570317)
                ·
                  refine ⟨506471757669215093463869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1350591353784573582570317 506471757669215093463869)
                  ·
                    refine ⟨189926909125955660048951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 506471757669215093463869 189926909125955660048951)
                    ·
                      rfl

theorem cell22_554822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_554822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554822 prefixEnd_554822 := by exact prefixLift 554822
  have htrace : WordTrace (prefixWord ++ tailWord_554822) baseStart_554822 baseEnd_554822 := by
    simpa [prefixWord, tailWord_554822, baseEnd_554822] using wordTrace_append hprefix tailTrace_554822
  have hstable : (prefixWord ++ tailWord_554822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554822).length < 2 ^ (prefixWord ++ tailWord_554822).sum := by decide
  have hdescent : baseEnd_554822 < baseStart_554822 := by decide
  rcases family_descends (prefixWord ++ tailWord_554822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554848 : List Nat := [2, 1, 1, 3, 3, 2, 3, 2, 1, 4]
def baseStart_554848 : Nat := 118140960795 + 554848 * 2 ^ 59
def prefixEnd_554848 : Nat := 4983230072969 + 3 ^ 40 * 554848 * 2
def baseEnd_554848 : Nat := 189935809457300258898871

theorem tailTrace_554848 : CollatzResearch.WordTrace tailWord_554848 prefixEnd_554848 189935809457300258898871 := by
  unfold tailWord_554848
  simp only [CollatzResearch.WordTrace]
  refine ⟨10118484546943965669620599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13491312729258620892827465 10118484546943965669620599)
  ·
    refine ⟨15177726820415948504430899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10118484546943965669620599 15177726820415948504430899)
    ·
      refine ⟨22766590230623922756646349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15177726820415948504430899 22766590230623922756646349)
      ·
        refine ⟨8537471336483971033742381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22766590230623922756646349 8537471336483971033742381)
        ·
          refine ⟨3201551751181489137653393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8537471336483971033742381 3201551751181489137653393)
          ·
            refine ⟨2401163813386116853240045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3201551751181489137653393 2401163813386116853240045)
            ·
              refine ⟨900436430019793819965017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2401163813386116853240045 900436430019793819965017)
              ·
                refine ⟨675327322514845364973763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 900436430019793819965017 675327322514845364973763)
                ·
                  refine ⟨1012990983772268047460645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 675327322514845364973763 1012990983772268047460645)
                  ·
                    refine ⟨189935809457300258898871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1012990983772268047460645 189935809457300258898871)
                    ·
                      rfl

theorem cell22_554848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 1, 4].length) (baseStart_554848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554848 prefixEnd_554848 := by exact prefixLift 554848
  have htrace : WordTrace (prefixWord ++ tailWord_554848) baseStart_554848 baseEnd_554848 := by
    simpa [prefixWord, tailWord_554848, baseEnd_554848] using wordTrace_append hprefix tailTrace_554848
  have hstable : (prefixWord ++ tailWord_554848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554848).length < 2 ^ (prefixWord ++ tailWord_554848).sum := by decide
  have hdescent : baseEnd_554848 < baseStart_554848 := by decide
  rcases family_descends (prefixWord ++ tailWord_554848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554861 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 3, 5]
def baseStart_554861 : Nat := 118140960795 + 554861 * 2 ^ 59
def prefixEnd_554861 : Nat := 4983230072969 + 3 ^ 40 * 554861 * 2
def baseEnd_554861 : Nat := 189940259622972558323831

theorem tailTrace_554861 : CollatzResearch.WordTrace tailWord_554861 prefixEnd_554861 189940259622972558323831 := by
  unfold tailWord_554861
  simp only [CollatzResearch.WordTrace]
  refine ⟨20237443242840834559464437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13491628828560556372976291 20237443242840834559464437)
  ·
    refine ⟨1897260304016328239949791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20237443242840834559464437 1897260304016328239949791)
    ·
      refine ⟨2845890456024492359924687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1897260304016328239949791 2845890456024492359924687)
      ·
        refine ⟨4268835684036738539887031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2845890456024492359924687 4268835684036738539887031)
        ·
          refine ⟨6403253526055107809830547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4268835684036738539887031 6403253526055107809830547)
          ·
            refine ⟨9604880289082661714745821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6403253526055107809830547 9604880289082661714745821)
            ·
              refine ⟨3601830108405998143029683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9604880289082661714745821 3601830108405998143029683)
              ·
                refine ⟨5402745162608997214544525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3601830108405998143029683 5402745162608997214544525)
                ·
                  refine ⟨2026029435978373955454197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5402745162608997214544525 2026029435978373955454197)
                  ·
                    refine ⟨189940259622972558323831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2026029435978373955454197 189940259622972558323831)
                    ·
                      rfl

theorem cell22_554861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_554861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554861 prefixEnd_554861 := by exact prefixLift 554861
  have htrace : WordTrace (prefixWord ++ tailWord_554861) baseStart_554861 baseEnd_554861 := by
    simpa [prefixWord, tailWord_554861, baseEnd_554861] using wordTrace_append hprefix tailTrace_554861
  have hstable : (prefixWord ++ tailWord_554861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554861).length < 2 ^ (prefixWord ++ tailWord_554861).sum := by decide
  have hdescent : baseEnd_554861 < baseStart_554861 := by decide
  rcases family_descends (prefixWord ++ tailWord_554861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554936 : List Nat := [2, 1, 2, 1, 2, 3, 3, 1, 7]
def baseStart_554936 : Nat := 118140960795 + 554936 * 2 ^ 59
def prefixEnd_554936 : Nat := 4983230072969 + 3 ^ 40 * 554936 * 2
def baseEnd_554936 : Nat := 63321977885232454232867

theorem tailTrace_554936 : CollatzResearch.WordTrace tailWord_554936 prefixEnd_554936 63321977885232454232867 := by
  unfold tailWord_554936
  simp only [CollatzResearch.WordTrace]
  refine ⟨10120089358784561184222331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13493452478379414912296441 10120089358784561184222331)
  ·
    refine ⟨15180134038176841776333497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10120089358784561184222331 15180134038176841776333497)
    ·
      refine ⟨11385100528632631332250123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15180134038176841776333497 11385100528632631332250123)
      ·
        refine ⟨17077650792948946998375185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11385100528632631332250123 17077650792948946998375185)
        ·
          refine ⟨12808238094711710248781389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17077650792948946998375185 12808238094711710248781389)
          ·
            refine ⟨4803089285516891343293021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12808238094711710248781389 4803089285516891343293021)
            ·
              refine ⟨1801158482068834253734883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4803089285516891343293021 1801158482068834253734883)
              ·
                refine ⟨2701737723103251380602325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1801158482068834253734883 2701737723103251380602325)
                ·
                  refine ⟨63321977885232454232867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2701737723103251380602325 63321977885232454232867)
                  ·
                    rfl

theorem cell22_554936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 7].length) (baseStart_554936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_554936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_554936 prefixEnd_554936 := by exact prefixLift 554936
  have htrace : WordTrace (prefixWord ++ tailWord_554936) baseStart_554936 baseEnd_554936 := by
    simpa [prefixWord, tailWord_554936, baseEnd_554936] using wordTrace_append hprefix tailTrace_554936
  have hstable : (prefixWord ++ tailWord_554936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554936).length < 2 ^ (prefixWord ++ tailWord_554936).sum := by decide
  have hdescent : baseEnd_554936 < baseStart_554936 := by decide
  rcases family_descends (prefixWord ++ tailWord_554936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555011 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 3, 6]
def baseStart_555011 : Nat := 118140960795 + 555011 * 2 ^ 59
def prefixEnd_555011 : Nat := 4983230072969 + 3 ^ 40 * 555011 * 2
def baseEnd_555011 : Nat := 189991607688422167073371

theorem tailTrace_555011 : CollatzResearch.WordTrace tailWord_555011 prefixEnd_555011 189991607688422167073371 := by
  unfold tailWord_555011
  simp only [CollatzResearch.WordTrace]
  refine ⟨20242914192297410177424887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13495276128198273451616591 20242914192297410177424887)
  ·
    refine ⟨30364371288446115266137331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20242914192297410177424887 30364371288446115266137331)
    ·
      refine ⟨45546556932669172899205997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30364371288446115266137331 45546556932669172899205997)
      ·
        refine ⟨17079958849750939837202249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45546556932669172899205997 17079958849750939837202249)
        ·
          refine ⟨12809969137313204877901687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17079958849750939837202249 12809969137313204877901687)
          ·
            refine ⟨19214953705969807316852531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12809969137313204877901687 19214953705969807316852531)
            ·
              refine ⟨28822430558954710975278797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19214953705969807316852531 28822430558954710975278797)
              ·
                refine ⟨10808411459608016615729549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28822430558954710975278797 10808411459608016615729549)
                ·
                  refine ⟨4053154297353006230898581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10808411459608016615729549 4053154297353006230898581)
                  ·
                    refine ⟨189991607688422167073371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4053154297353006230898581 189991607688422167073371)
                    ·
                      rfl

theorem cell22_555011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 6].length) (baseStart_555011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_555011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_555011 prefixEnd_555011 := by exact prefixLift 555011
  have htrace : WordTrace (prefixWord ++ tailWord_555011) baseStart_555011 baseEnd_555011 := by
    simpa [prefixWord, tailWord_555011, baseEnd_555011] using wordTrace_append hprefix tailTrace_555011
  have hstable : (prefixWord ++ tailWord_555011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555011).length < 2 ^ (prefixWord ++ tailWord_555011).sum := by decide
  have hdescent : baseEnd_555011 < baseStart_555011 := by decide
  rcases family_descends (prefixWord ++ tailWord_555011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555122 : List Nat := [3, 2, 1, 2, 2, 3, 3, 1, 5]
def baseStart_555122 : Nat := 118140960795 + 555122 * 2 ^ 59
def prefixEnd_555122 : Nat := 4983230072969 + 3 ^ 40 * 555122 * 2
def baseEnd_555122 : Nat := 63343201752284959182677

theorem tailTrace_555122 : CollatzResearch.WordTrace tailWord_555122 prefixEnd_555122 63343201752284959182677 := by
  unfold tailWord_555122
  simp only [CollatzResearch.WordTrace]
  refine ⟨5061740673723819033678905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13497975129930184089810413 5061740673723819033678905)
  ·
    refine ⟨3796305505292864275259179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5061740673723819033678905 3796305505292864275259179)
    ·
      refine ⟨5694458257939296412888769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3796305505292864275259179 5694458257939296412888769)
      ·
        refine ⟨4270843693454472309666577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5694458257939296412888769 4270843693454472309666577)
        ·
          refine ⟨3203132770090854232249933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4270843693454472309666577 3203132770090854232249933)
          ·
            refine ⟨1201174788784070337093725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3203132770090854232249933 1201174788784070337093725)
            ·
              refine ⟨450440545794026376410147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1201174788784070337093725 450440545794026376410147)
              ·
                refine ⟨675660818691039564615221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 450440545794026376410147 675660818691039564615221)
                ·
                  refine ⟨63343201752284959182677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 675660818691039564615221 63343201752284959182677)
                  ·
                    rfl

theorem cell22_555122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_555122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_555122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_555122 prefixEnd_555122 := by exact prefixLift 555122
  have htrace : WordTrace (prefixWord ++ tailWord_555122) baseStart_555122 baseEnd_555122 := by
    simpa [prefixWord, tailWord_555122, baseEnd_555122] using wordTrace_append hprefix tailTrace_555122
  have hstable : (prefixWord ++ tailWord_555122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555122).length < 2 ^ (prefixWord ++ tailWord_555122).sum := by decide
  have hdescent : baseEnd_555122 < baseStart_555122 := by decide
  rcases family_descends (prefixWord ++ tailWord_555122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555167 : List Nat := [1, 1, 2, 6, 1, 3, 1, 1, 6]
def baseStart_555167 : Nat := 118140960795 + 555167 * 2 ^ 59
def prefixEnd_555167 : Nat := 4983230072969 + 3 ^ 40 * 555167 * 2
def baseEnd_555167 : Nat := 63348336558829920057631

theorem tailTrace_555167 : CollatzResearch.WordTrace tailWord_555167 prefixEnd_555167 63348336558829920057631 := by
  unfold tailWord_555167
  simp only [CollatzResearch.WordTrace]
  refine ⟨20248603979732248820103755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13499069319821499213402503 20248603979732248820103755)
  ·
    refine ⟨30372905969598373230155633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20248603979732248820103755 30372905969598373230155633)
    ·
      refine ⟨22779679477198779922616725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30372905969598373230155633 22779679477198779922616725)
      ·
        refine ⟨1067797475493692808872659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22779679477198779922616725 1067797475493692808872659)
        ·
          refine ⟨1601696213240539213308989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1067797475493692808872659 1601696213240539213308989)
          ·
            refine ⟨600636079965202204990871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1601696213240539213308989 600636079965202204990871)
            ·
              refine ⟨900954119947803307486307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 600636079965202204990871 900954119947803307486307)
              ·
                refine ⟨1351431179921704961229461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 900954119947803307486307 1351431179921704961229461)
                ·
                  refine ⟨63348336558829920057631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1351431179921704961229461 63348336558829920057631)
                  ·
                    rfl

theorem cell22_555167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 6].length) (baseStart_555167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_555167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_555167 prefixEnd_555167 := by exact prefixLift 555167
  have htrace : WordTrace (prefixWord ++ tailWord_555167) baseStart_555167 baseEnd_555167 := by
    simpa [prefixWord, tailWord_555167, baseEnd_555167] using wordTrace_append hprefix tailTrace_555167
  have hstable : (prefixWord ++ tailWord_555167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555167).length < 2 ^ (prefixWord ++ tailWord_555167).sum := by decide
  have hdescent : baseEnd_555167 < baseStart_555167 := by decide
  rcases family_descends (prefixWord ++ tailWord_555167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555212 : List Nat := [2, 2, 1, 6, 2, 9]
def baseStart_555212 : Nat := 118140960795 + 555212 * 2 ^ 59
def prefixEnd_555212 : Nat := 4983230072969 + 3 ^ 40 * 555212 * 2
def baseEnd_555212 : Nat := 2346424865384254849355

theorem tailTrace_555212 : CollatzResearch.WordTrace tailWord_555212 prefixEnd_555212 2346424865384254849355 := by
  unfold tailWord_555212
  simp only [CollatzResearch.WordTrace]
  refine ⟨10125122632284610752745945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13500163509712814336994593 10125122632284610752745945)
  ·
    refine ⟨7593841974213458064559459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10125122632284610752745945 7593841974213458064559459)
    ·
      refine ⟨11390762961320187096839189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7593841974213458064559459 11390762961320187096839189)
      ·
        refine ⟨533942013811883770164337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11390762961320187096839189 533942013811883770164337)
        ·
          refine ⟨400456510358912827623253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 533942013811883770164337 400456510358912827623253)
          ·
            refine ⟨2346424865384254849355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 400456510358912827623253 2346424865384254849355)
            ·
              rfl

theorem cell22_555212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 9].length) (baseStart_555212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_555212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_555212 prefixEnd_555212 := by exact prefixLift 555212
  have htrace : WordTrace (prefixWord ++ tailWord_555212) baseStart_555212 baseEnd_555212 := by
    simpa [prefixWord, tailWord_555212, baseEnd_555212] using wordTrace_append hprefix tailTrace_555212
  have hstable : (prefixWord ++ tailWord_555212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555212).length < 2 ^ (prefixWord ++ tailWord_555212).sum := by decide
  have hdescent : baseEnd_555212 < baseStart_555212 := by decide
  rcases family_descends (prefixWord ++ tailWord_555212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555285 : List Nat := [1, 3, 2, 1, 2, 1, 3, 3, 6]
def baseStart_555285 : Nat := 118140960795 + 555285 * 2 ^ 59
def prefixEnd_555285 : Nat := 4983230072969 + 3 ^ 40 * 555285 * 2
def baseEnd_555285 : Nat := 63361801162658928574177

theorem tailTrace_555285 : CollatzResearch.WordTrace tailWord_555285 prefixEnd_555285 63361801162658928574177 := by
  unfold tailWord_555285
  simp only [CollatzResearch.WordTrace]
  refine ⟨20252907793304754972899309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13501938528869836648599539 20252907793304754972899309)
  ·
    refine ⟨7594840422489283114837241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20252907793304754972899309 7594840422489283114837241)
    ·
      refine ⟨5696130316866962336127931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7594840422489283114837241 5696130316866962336127931)
      ·
        refine ⟨8544195475300443504191897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5696130316866962336127931 8544195475300443504191897)
        ·
          refine ⟨6408146606475332628143923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8544195475300443504191897 6408146606475332628143923)
          ·
            refine ⟨9612219909712998942215885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6408146606475332628143923 9612219909712998942215885)
            ·
              refine ⟨3604582466142374603330957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9612219909712998942215885 3604582466142374603330957)
              ·
                refine ⟨1351718424803390476249109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3604582466142374603330957 1351718424803390476249109)
                ·
                  refine ⟨63361801162658928574177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1351718424803390476249109 63361801162658928574177)
                  ·
                    rfl

theorem cell22_555285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 6].length) (baseStart_555285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_555285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_555285 prefixEnd_555285 := by exact prefixLift 555285
  have htrace : WordTrace (prefixWord ++ tailWord_555285) baseStart_555285 baseEnd_555285 := by
    simpa [prefixWord, tailWord_555285, baseEnd_555285] using wordTrace_append hprefix tailTrace_555285
  have hstable : (prefixWord ++ tailWord_555285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555285).length < 2 ^ (prefixWord ++ tailWord_555285).sum := by decide
  have hdescent : baseEnd_555285 < baseStart_555285 := by decide
  rcases family_descends (prefixWord ++ tailWord_555285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555315 : List Nat := [1, 1, 1, 2, 5, 1, 1, 3, 1, 6]
def baseStart_555315 : Nat := 118140960795 + 555315 * 2 ^ 59
def prefixEnd_555315 : Nat := 4983230072969 + 3 ^ 40 * 555315 * 2
def baseEnd_555315 : Nat := 190095673101066707472439

theorem tailTrace_555315 : CollatzResearch.WordTrace tailWord_555315 prefixEnd_555315 190095673101066707472439 := by
  unfold tailWord_555315
  simp only [CollatzResearch.WordTrace]
  refine ⟨20254001983196070096491399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13502667988797380064327599 20254001983196070096491399)
  ·
    refine ⟨30381002974794105144737099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20254001983196070096491399 30381002974794105144737099)
    ·
      refine ⟨45571504462191157717105649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30381002974794105144737099 45571504462191157717105649)
      ·
        refine ⟨34178628346643368287829237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45571504462191157717105649 34178628346643368287829237)
        ·
          refine ⟨3204246407497815776983991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34178628346643368287829237 3204246407497815776983991)
          ·
            refine ⟨4806369611246723665475987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3204246407497815776983991 4806369611246723665475987)
            ·
              refine ⟨7209554416870085498213981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4806369611246723665475987 7209554416870085498213981)
              ·
                refine ⟨2703582906326282061830243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7209554416870085498213981 2703582906326282061830243)
                ·
                  refine ⟨4055374359489423092745365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2703582906326282061830243 4055374359489423092745365)
                  ·
                    refine ⟨190095673101066707472439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4055374359489423092745365 190095673101066707472439)
                    ·
                      rfl

theorem cell22_555315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 6].length) (baseStart_555315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_555315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_555315 prefixEnd_555315 := by exact prefixLift 555315
  have htrace : WordTrace (prefixWord ++ tailWord_555315) baseStart_555315 baseEnd_555315 := by
    simpa [prefixWord, tailWord_555315, baseEnd_555315] using wordTrace_append hprefix tailTrace_555315
  have hstable : (prefixWord ++ tailWord_555315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555315).length < 2 ^ (prefixWord ++ tailWord_555315).sum := by decide
  have hdescent : baseEnd_555315 < baseStart_555315 := by decide
  rcases family_descends (prefixWord ++ tailWord_555315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555317 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 6, 3]
def baseStart_555317 : Nat := 118140960795 + 555317 * 2 ^ 59
def prefixEnd_555317 : Nat := 4983230072969 + 3 ^ 40 * 555317 * 2
def baseEnd_555317 : Nat := 190096357741939368922433

theorem tailTrace_555317 : CollatzResearch.WordTrace tailWord_555317 prefixEnd_555317 190096357741939368922433 := by
  unfold tailWord_555317
  simp only [CollatzResearch.WordTrace]
  refine ⟨20254074929188824438064205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13502716619459216292042803 20254074929188824438064205)
  ·
    refine ⟨7595278098445809164274077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20254074929188824438064205 7595278098445809164274077)
    ·
      refine ⟨2848229286917178436602779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7595278098445809164274077 2848229286917178436602779)
      ·
        refine ⟨4272343930375767654904169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2848229286917178436602779 4272343930375767654904169)
        ·
          refine ⟨3204257947781825741178127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4272343930375767654904169 3204257947781825741178127)
          ·
            refine ⟨4806386921672738611767191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3204257947781825741178127 4806386921672738611767191)
            ·
              refine ⟨7209580382509107917650787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4806386921672738611767191 7209580382509107917650787)
              ·
                refine ⟨10814370573763661876476181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7209580382509107917650787 10814370573763661876476181)
                ·
                  refine ⟨506923620645171650459821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10814370573763661876476181 506923620645171650459821)
                  ·
                    refine ⟨190096357741939368922433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 506923620645171650459821 190096357741939368922433)
                    ·
                      rfl

theorem cell22_555317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_555317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_555317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_555317 prefixEnd_555317 := by exact prefixLift 555317
  have htrace : WordTrace (prefixWord ++ tailWord_555317) baseStart_555317 baseEnd_555317 := by
    simpa [prefixWord, tailWord_555317, baseEnd_555317] using wordTrace_append hprefix tailTrace_555317
  have hstable : (prefixWord ++ tailWord_555317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555317).length < 2 ^ (prefixWord ++ tailWord_555317).sum := by decide
  have hdescent : baseEnd_555317 < baseStart_555317 := by decide
  rcases family_descends (prefixWord ++ tailWord_555317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555375 : List Nat := [1, 1, 2, 1, 3, 1, 2, 4, 7]
def baseStart_555375 : Nat := 118140960795 + 555375 * 2 ^ 59
def prefixEnd_555375 : Nat := 4983230072969 + 3 ^ 40 * 555375 * 2
def baseEnd_555375 : Nat := 63372070775748850324085

theorem tailTrace_555375 : CollatzResearch.WordTrace tailWord_555375 prefixEnd_555375 63372070775748850324085 := by
  unfold tailWord_555375
  simp only [CollatzResearch.WordTrace]
  refine ⟨20256190362978700343675579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13504126908652466895783719 20256190362978700343675579)
  ·
    refine ⟨30384285544468050515513369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20256190362978700343675579 30384285544468050515513369)
    ·
      refine ⟨22788214158351037886635027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30384285544468050515513369 22788214158351037886635027)
      ·
        refine ⟨34182321237526556829952541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22788214158351037886635027 34182321237526556829952541)
        ·
          refine ⟨12818370464072458811232203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34182321237526556829952541 12818370464072458811232203)
          ·
            refine ⟨19227555696108688216848305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12818370464072458811232203 19227555696108688216848305)
            ·
              refine ⟨14420666772081516162636229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19227555696108688216848305 14420666772081516162636229)
              ·
                refine ⟨2703875019765284280494293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14420666772081516162636229 2703875019765284280494293)
                ·
                  refine ⟨63372070775748850324085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2703875019765284280494293 63372070775748850324085)
                  ·
                    rfl

theorem cell22_555375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 7].length) (baseStart_555375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_555375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_555375 prefixEnd_555375 := by exact prefixLift 555375
  have htrace : WordTrace (prefixWord ++ tailWord_555375) baseStart_555375 baseEnd_555375 := by
    simpa [prefixWord, tailWord_555375, baseEnd_555375] using wordTrace_append hprefix tailTrace_555375
  have hstable : (prefixWord ++ tailWord_555375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555375).length < 2 ^ (prefixWord ++ tailWord_555375).sum := by decide
  have hdescent : baseEnd_555375 < baseStart_555375 := by decide
  rcases family_descends (prefixWord ++ tailWord_555375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555396 : List Nat := [2, 3, 2, 1, 1, 2, 3, 4, 1, 3]
def baseStart_555396 : Nat := 118140960795 + 555396 * 2 ^ 59
def prefixEnd_555396 : Nat := 4983230072969 + 3 ^ 40 * 555396 * 2
def baseEnd_555396 : Nat := 190123401056409496197191

theorem tailTrace_555396 : CollatzResearch.WordTrace tailWord_555396 prefixEnd_555396 190123401056409496197191 := by
  unfold tailWord_555396
  simp only [CollatzResearch.WordTrace]
  refine ⟨10128478147951310465095021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13504637530601747286793361 10128478147951310465095021)
  ·
    refine ⟨3798179305481741424410633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10128478147951310465095021 3798179305481741424410633)
    ·
      refine ⟨2848634479111306068307975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3798179305481741424410633 2848634479111306068307975)
      ·
        refine ⟨4272951718666959102461963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2848634479111306068307975 4272951718666959102461963)
        ·
          refine ⟨6409427578000438653692945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4272951718666959102461963 6409427578000438653692945)
          ·
            refine ⟨4807070683500328990269709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6409427578000438653692945 4807070683500328990269709)
            ·
              refine ⟨1802651506312623371351141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4807070683500328990269709 1802651506312623371351141)
              ·
                refine ⟨337997157433616882128339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1802651506312623371351141 337997157433616882128339)
                ·
                  refine ⟨506995736150425323192509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 337997157433616882128339 506995736150425323192509)
                  ·
                    refine ⟨190123401056409496197191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 506995736150425323192509 190123401056409496197191)
                    ·
                      rfl

theorem cell22_555396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_555396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_555396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_555396 prefixEnd_555396 := by exact prefixLift 555396
  have htrace : WordTrace (prefixWord ++ tailWord_555396) baseStart_555396 baseEnd_555396 := by
    simpa [prefixWord, tailWord_555396, baseEnd_555396] using wordTrace_append hprefix tailTrace_555396
  have hstable : (prefixWord ++ tailWord_555396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555396).length < 2 ^ (prefixWord ++ tailWord_555396).sum := by decide
  have hdescent : baseEnd_555396 < baseStart_555396 := by decide
  rcases family_descends (prefixWord ++ tailWord_555396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555482 : List Nat := [3, 1, 1, 2, 3, 1, 3, 8]
def baseStart_555482 : Nat := 118140960795 + 555482 * 2 ^ 59
def prefixEnd_555482 : Nat := 4983230072969 + 3 ^ 40 * 555482 * 2
def baseEnd_555482 : Nat := 21128093401548215394103

theorem tailTrace_555482 : CollatzResearch.WordTrace tailWord_555482 prefixEnd_555482 21128093401548215394103 := by
  unfold tailWord_555482
  simp only [CollatzResearch.WordTrace]
  refine ⟨5065023243397764404455175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13506728649060705078547133 5065023243397764404455175)
  ·
    refine ⟨7597534865096646606682763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5065023243397764404455175 7597534865096646606682763)
    ·
      refine ⟨11396302297644969910024145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7597534865096646606682763 11396302297644969910024145)
      ·
        refine ⟨8547226723233727432518109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11396302297644969910024145 8547226723233727432518109)
        ·
          refine ⟨3205210021212647787194291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8547226723233727432518109 3205210021212647787194291)
          ·
            refine ⟨4807815031818971680791437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3205210021212647787194291 4807815031818971680791437)
            ·
              refine ⟨1802930636932114380296789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4807815031818971680791437 1802930636932114380296789)
              ·
                refine ⟨21128093401548215394103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1802930636932114380296789 21128093401548215394103)
                ·
                  rfl

theorem cell22_555482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 8].length) (baseStart_555482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_555482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_555482 prefixEnd_555482 := by exact prefixLift 555482
  have htrace : WordTrace (prefixWord ++ tailWord_555482) baseStart_555482 baseEnd_555482 := by
    simpa [prefixWord, tailWord_555482, baseEnd_555482] using wordTrace_append hprefix tailTrace_555482
  have hstable : (prefixWord ++ tailWord_555482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555482).length < 2 ^ (prefixWord ++ tailWord_555482).sum := by decide
  have hdescent : baseEnd_555482 < baseStart_555482 := by decide
  rcases family_descends (prefixWord ++ tailWord_555482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555501 : List Nat := [1, 5, 1, 3, 1, 2, 1, 2, 2, 4]
def baseStart_555501 : Nat := 118140960795 + 555501 * 2 ^ 59
def prefixEnd_555501 : Nat := 4983230072969 + 3 ^ 40 * 555501 * 2
def baseEnd_555501 : Nat := 190159344702224222321869

theorem tailTrace_555501 : CollatzResearch.WordTrace tailWord_555501 prefixEnd_555501 190159344702224222321869 := by
  unfold tailWord_555501
  simp only [CollatzResearch.WordTrace]
  refine ⟨20260785960522223862762357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13507190640348149241841571 20260785960522223862762357)
  ·
    refine ⟨1899448683798958487133971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20260785960522223862762357 1899448683798958487133971)
    ·
      refine ⟨2849173025698437730700957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1899448683798958487133971 2849173025698437730700957)
      ·
        refine ⟨1068439884636914149012859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2849173025698437730700957 1068439884636914149012859)
        ·
          refine ⟨1602659826955371223519289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1068439884636914149012859 1602659826955371223519289)
          ·
            refine ⟨1201994870216528417639467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1602659826955371223519289 1201994870216528417639467)
            ·
              refine ⟨1802992305324792626459201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1201994870216528417639467 1802992305324792626459201)
              ·
                refine ⟨1352244228993594469844401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1802992305324792626459201 1352244228993594469844401)
                ·
                  refine ⟨1014183171745195852383301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1352244228993594469844401 1014183171745195852383301)
                  ·
                    refine ⟨190159344702224222321869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1014183171745195852383301 190159344702224222321869)
                    ·
                      rfl

theorem cell22_555501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_555501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_555501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_555501 prefixEnd_555501 := by exact prefixLift 555501
  have htrace : WordTrace (prefixWord ++ tailWord_555501) baseStart_555501 baseEnd_555501 := by
    simpa [prefixWord, tailWord_555501, baseEnd_555501] using wordTrace_append hprefix tailTrace_555501
  have hstable : (prefixWord ++ tailWord_555501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555501).length < 2 ^ (prefixWord ++ tailWord_555501).sum := by decide
  have hdescent : baseEnd_555501 < baseStart_555501 := by decide
  rcases family_descends (prefixWord ++ tailWord_555501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555512 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 2, 6]
def baseStart_555512 : Nat := 118140960795 + 555512 * 2 ^ 59
def prefixEnd_555512 : Nat := 4983230072969 + 3 ^ 40 * 555512 * 2
def baseEnd_555512 : Nat := 190163110227023860296835

theorem tailTrace_555512 : CollatzResearch.WordTrace tailWord_555512 prefixEnd_555512 190163110227023860296835 := by
  unfold tailWord_555512
  simp only [CollatzResearch.WordTrace]
  refine ⟨10130593581741186370706395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13507458108988248494275193 10130593581741186370706395)
  ·
    refine ⟨15195890372611779556059593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10130593581741186370706395 15195890372611779556059593)
    ·
      refine ⟨11396917779458834667044695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15195890372611779556059593 11396917779458834667044695)
      ·
        refine ⟨17095376669188252000567043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11396917779458834667044695 17095376669188252000567043)
        ·
          refine ⟨25643065003782378000850565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17095376669188252000567043 25643065003782378000850565)
          ·
            refine ⟨4808074688209195875159481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25643065003782378000850565 4808074688209195875159481)
            ·
              refine ⟨3606056016156896906369611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4808074688209195875159481 3606056016156896906369611)
              ·
                refine ⟨5409084024235345359554417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3606056016156896906369611 5409084024235345359554417)
                ·
                  refine ⟨4056813018176509019665813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5409084024235345359554417 4056813018176509019665813)
                  ·
                    refine ⟨190163110227023860296835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4056813018176509019665813 190163110227023860296835)
                    ·
                      rfl

theorem cell22_555512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_555512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_555512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_555512 prefixEnd_555512 := by exact prefixLift 555512
  have htrace : WordTrace (prefixWord ++ tailWord_555512) baseStart_555512 baseEnd_555512 := by
    simpa [prefixWord, tailWord_555512, baseEnd_555512] using wordTrace_append hprefix tailTrace_555512
  have hstable : (prefixWord ++ tailWord_555512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555512).length < 2 ^ (prefixWord ++ tailWord_555512).sum := by decide
  have hdescent : baseEnd_555512 < baseStart_555512 := by decide
  rcases family_descends (prefixWord ++ tailWord_555512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555514 : List Nat := [3, 1, 1, 1, 1, 2, 2, 5, 3, 3]
def baseStart_555514 : Nat := 118140960795 + 555514 * 2 ^ 59
def prefixEnd_555514 : Nat := 4983230072969 + 3 ^ 40 * 555514 * 2
def baseEnd_555514 : Nat := 190163794867896521746829

theorem tailTrace_555514 : CollatzResearch.WordTrace tailWord_555514 prefixEnd_555514 190163794867896521746829 := by
  unfold tailWord_555514
  simp only [CollatzResearch.WordTrace]
  refine ⟨5065315027368781770746399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13507506739650084721990397 5065315027368781770746399)
  ·
    refine ⟨7597972541053172656119599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5065315027368781770746399 7597972541053172656119599)
    ·
      refine ⟨11396958811579758984179399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7597972541053172656119599 11396958811579758984179399)
      ·
        refine ⟨17095438217369638476269099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11396958811579758984179399 17095438217369638476269099)
        ·
          refine ⟨25643157326054457714403649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17095438217369638476269099 25643157326054457714403649)
          ·
            refine ⟨19232367994540843285802737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25643157326054457714403649 19232367994540843285802737)
            ·
              refine ⟨14424275995905632464352053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19232367994540843285802737 14424275995905632464352053)
              ·
                refine ⟨1352275874616153043533005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14424275995905632464352053 1352275874616153043533005)
                ·
                  refine ⟨507103452981057391324877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1352275874616153043533005 507103452981057391324877)
                  ·
                    refine ⟨190163794867896521746829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 507103452981057391324877 190163794867896521746829)
                    ·
                      rfl

theorem cell22_555514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 3, 3].length) (baseStart_555514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_555514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_555514 prefixEnd_555514 := by exact prefixLift 555514
  have htrace : WordTrace (prefixWord ++ tailWord_555514) baseStart_555514 baseEnd_555514 := by
    simpa [prefixWord, tailWord_555514, baseEnd_555514] using wordTrace_append hprefix tailTrace_555514
  have hstable : (prefixWord ++ tailWord_555514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555514).length < 2 ^ (prefixWord ++ tailWord_555514).sum := by decide
  have hdescent : baseEnd_555514 < baseStart_555514 := by decide
  rcases family_descends (prefixWord ++ tailWord_555514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555589 : List Nat := [1, 3, 1, 1, 1, 6, 1, 2, 6]
def baseStart_555589 : Nat := 118140960795 + 555589 * 2 ^ 59
def prefixEnd_555589 : Nat := 4983230072969 + 3 ^ 40 * 555589 * 2
def baseEnd_555589 : Nat := 63396489633540442040533

theorem tailTrace_555589 : CollatzResearch.WordTrace tailWord_555589 prefixEnd_555589 63396489633540442040533 := by
  unfold tailWord_555589
  simp only [CollatzResearch.WordTrace]
  refine ⟨20263995584203414891965821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13509330389468943261310547 20263995584203414891965821)
  ·
    refine ⟨7598998344076280584487183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20263995584203414891965821 7598998344076280584487183)
    ·
      refine ⟨11398497516114420876730775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7598998344076280584487183 11398497516114420876730775)
      ·
        refine ⟨17097746274171631315096163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11398497516114420876730775 17097746274171631315096163)
        ·
          refine ⟨25646619411257446972644245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17097746274171631315096163 25646619411257446972644245)
          ·
            refine ⟨1202185284902692826842699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25646619411257446972644245 1202185284902692826842699)
            ·
              refine ⟨1803277927354039240264049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1202185284902692826842699 1803277927354039240264049)
              ·
                refine ⟨1352458445515529430198037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1803277927354039240264049 1352458445515529430198037)
                ·
                  refine ⟨63396489633540442040533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1352458445515529430198037 63396489633540442040533)
                  ·
                    rfl

theorem cell22_555589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 6].length) (baseStart_555589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_555589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_555589 prefixEnd_555589 := by exact prefixLift 555589
  have htrace : WordTrace (prefixWord ++ tailWord_555589) baseStart_555589 baseEnd_555589 := by
    simpa [prefixWord, tailWord_555589, baseEnd_555589] using wordTrace_append hprefix tailTrace_555589
  have hstable : (prefixWord ++ tailWord_555589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555589).length < 2 ^ (prefixWord ++ tailWord_555589).sum := by decide
  have hdescent : baseEnd_555589 < baseStart_555589 := by decide
  rcases family_descends (prefixWord ++ tailWord_555589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555619 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 4, 4]
def baseStart_555619 : Nat := 118140960795 + 555619 * 2 ^ 59
def prefixEnd_555619 : Nat := 4983230072969 + 3 ^ 40 * 555619 * 2
def baseEnd_555619 : Nat := 190199738513711247871507

theorem tailTrace_555619 : CollatzResearch.WordTrace tailWord_555619 prefixEnd_555619 190199738513711247871507 := by
  unfold tailWord_555619
  simp only [CollatzResearch.WordTrace]
  refine ⟨20265089774094730015557911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13510059849396486677038607 20265089774094730015557911)
  ·
    refine ⟨30397634661142095023336867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20265089774094730015557911 30397634661142095023336867)
    ·
      refine ⟨45596451991713142535005301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30397634661142095023336867 45596451991713142535005301)
      ·
        refine ⟨4274667374223107112656747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45596451991713142535005301 4274667374223107112656747)
        ·
          refine ⟨6412001061334660668985121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4274667374223107112656747 6412001061334660668985121)
          ·
            refine ⟨4809000796000995501738841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6412001061334660668985121 4809000796000995501738841)
            ·
              refine ⟨3606750597000746626304131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4809000796000995501738841 3606750597000746626304131)
              ·
                refine ⟨5410125895501119939456197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3606750597000746626304131 5410125895501119939456197)
                ·
                  refine ⟨1014398605406459988648037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5410125895501119939456197 1014398605406459988648037)
                  ·
                    refine ⟨190199738513711247871507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1014398605406459988648037 190199738513711247871507)
                    ·
                      rfl

theorem cell22_555619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 4].length) (baseStart_555619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_555619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_555619 prefixEnd_555619 := by exact prefixLift 555619
  have htrace : WordTrace (prefixWord ++ tailWord_555619) baseStart_555619 baseEnd_555619 := by
    simpa [prefixWord, tailWord_555619, baseEnd_555619] using wordTrace_append hprefix tailTrace_555619
  have hstable : (prefixWord ++ tailWord_555619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555619).length < 2 ^ (prefixWord ++ tailWord_555619).sum := by decide
  have hdescent : baseEnd_555619 < baseStart_555619 := by decide
  rcases family_descends (prefixWord ++ tailWord_555619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555649 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 2, 7]
def baseStart_555649 : Nat := 118140960795 + 555649 * 2 ^ 59
def prefixEnd_555649 : Nat := 4983230072969 + 3 ^ 40 * 555649 * 2
def baseEnd_555649 : Nat := 190210008126801169621415

theorem tailTrace_555649 : CollatzResearch.WordTrace tailWord_555649 prefixEnd_555649 190210008126801169621415 := by
  unfold tailWord_555649
  simp only [CollatzResearch.WordTrace]
  refine ⟨20266183963986045139150001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13510789309324030092766667 20266183963986045139150001)
  ·
    refine ⟨15199637972989533854362501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20266183963986045139150001 15199637972989533854362501)
    ·
      refine ⟨2849932119935537597692969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15199637972989533854362501 2849932119935537597692969)
      ·
        refine ⟨2137449089951653198269727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2849932119935537597692969 2137449089951653198269727)
        ·
          refine ⟨3206173634927479797404591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2137449089951653198269727 3206173634927479797404591)
          ·
            refine ⟨4809260452391219696106887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3206173634927479797404591 4809260452391219696106887)
            ·
              refine ⟨7213890678586829544160331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4809260452391219696106887 7213890678586829544160331)
              ·
                refine ⟨10820836017880244316240497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7213890678586829544160331 10820836017880244316240497)
                ·
                  refine ⟨8115627013410183237180373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10820836017880244316240497 8115627013410183237180373)
                  ·
                    refine ⟨190210008126801169621415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8115627013410183237180373 190210008126801169621415)
                    ·
                      rfl

theorem cell22_555649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_555649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_555649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_555649 prefixEnd_555649 := by exact prefixLift 555649
  have htrace : WordTrace (prefixWord ++ tailWord_555649) baseStart_555649 baseEnd_555649 := by
    simpa [prefixWord, tailWord_555649, baseEnd_555649] using wordTrace_append hprefix tailTrace_555649
  have hstable : (prefixWord ++ tailWord_555649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555649).length < 2 ^ (prefixWord ++ tailWord_555649).sum := by decide
  have hdescent : baseEnd_555649 < baseStart_555649 := by decide
  rcases family_descends (prefixWord ++ tailWord_555649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555756 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 6, 3]
def baseStart_555756 : Nat := 118140960795 + 555756 * 2 ^ 59
def prefixEnd_555756 : Nat := 4983230072969 + 3 ^ 40 * 555756 * 2
def baseEnd_555756 : Nat := 190246636413488557196087

theorem tailTrace_555756 : CollatzResearch.WordTrace tailWord_555756 prefixEnd_555756 190246636413488557196087 := by
  unfold tailWord_555756
  simp only [CollatzResearch.WordTrace]
  refine ⟨10135043287299201206647561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13513391049732268275530081 10135043287299201206647561)
  ·
    refine ⟨7601282465474400904985671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10135043287299201206647561 7601282465474400904985671)
    ·
      refine ⟨11401923698211601357478507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7601282465474400904985671 11401923698211601357478507)
      ·
        refine ⟨17102885547317402036217761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11401923698211601357478507 17102885547317402036217761)
        ·
          refine ⟨12827164160488051527163321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17102885547317402036217761 12827164160488051527163321)
          ·
            refine ⟨9620373120366038645372491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12827164160488051527163321 9620373120366038645372491)
            ·
              refine ⟨14430559680549057968058737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9620373120366038645372491 14430559680549057968058737)
              ·
                refine ⟨10822919760411793476044053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14430559680549057968058737 10822919760411793476044053)
                ·
                  refine ⟨507324363769302819189565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10822919760411793476044053 507324363769302819189565)
                  ·
                    refine ⟨190246636413488557196087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 507324363769302819189565 190246636413488557196087)
                    ·
                      rfl

theorem cell22_555756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 3].length) (baseStart_555756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_555756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_555756 prefixEnd_555756 := by exact prefixLift 555756
  have htrace : WordTrace (prefixWord ++ tailWord_555756) baseStart_555756 baseEnd_555756 := by
    simpa [prefixWord, tailWord_555756, baseEnd_555756] using wordTrace_append hprefix tailTrace_555756
  have hstable : (prefixWord ++ tailWord_555756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555756).length < 2 ^ (prefixWord ++ tailWord_555756).sum := by decide
  have hdescent : baseEnd_555756 < baseStart_555756 := by decide
  rcases family_descends (prefixWord ++ tailWord_555756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555769 : List Nat := [1, 2, 1, 3, 1, 1, 1, 12]
def baseStart_555769 : Nat := 118140960795 + 555769 * 2 ^ 59
def prefixEnd_555769 : Nat := 4983230072969 + 3 ^ 40 * 555769 * 2
def baseEnd_555769 : Nat := 21139009619906761846783

theorem tailTrace_555769 : CollatzResearch.WordTrace tailWord_555769 prefixEnd_555769 21139009619906761846783 := by
  unfold tailWord_555769
  simp only [CollatzResearch.WordTrace]
  refine ⟨20270560723551305633518361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13513707149034203755678907 20270560723551305633518361)
  ·
    refine ⟨15202920542663479225138771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20270560723551305633518361 15202920542663479225138771)
    ·
      refine ⟨22804380813995218837708157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15202920542663479225138771 22804380813995218837708157)
      ·
        refine ⟨8551642805248207064140559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22804380813995218837708157 8551642805248207064140559)
        ·
          refine ⟨12827464207872310596210839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8551642805248207064140559 12827464207872310596210839)
          ·
            refine ⟨19241196311808465894316259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12827464207872310596210839 19241196311808465894316259)
            ·
              refine ⟨28861794467712698841474389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19241196311808465894316259 28861794467712698841474389)
              ·
                refine ⟨21139009619906761846783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 28861794467712698841474389 21139009619906761846783)
                ·
                  rfl

theorem cell22_555769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 12].length) (baseStart_555769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_555769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_555769 prefixEnd_555769 := by exact prefixLift 555769
  have htrace : WordTrace (prefixWord ++ tailWord_555769) baseStart_555769 baseEnd_555769 := by
    simpa [prefixWord, tailWord_555769, baseEnd_555769] using wordTrace_append hprefix tailTrace_555769
  have hstable : (prefixWord ++ tailWord_555769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555769).length < 2 ^ (prefixWord ++ tailWord_555769).sum := by decide
  have hdescent : baseEnd_555769 < baseStart_555769 := by decide
  rcases family_descends (prefixWord ++ tailWord_555769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555865 : List Nat := [1, 2, 1, 2, 2, 6, 2, 1, 5]
def baseStart_555865 : Nat := 118140960795 + 555865 * 2 ^ 59
def prefixEnd_555865 : Nat := 4983230072969 + 3 ^ 40 * 555865 * 2
def baseEnd_555865 : Nat := 63427983113682868740251

theorem tailTrace_555865 : CollatzResearch.WordTrace tailWord_555865 prefixEnd_555865 63427983113682868740251 := by
  unfold tailWord_555865
  simp only [CollatzResearch.WordTrace]
  refine ⟨20274062131203514029013049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13516041420802342686008699 20274062131203514029013049)
  ·
    refine ⟨15205546598402635521759787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20274062131203514029013049 15205546598402635521759787)
    ·
      refine ⟨22808319897603953282639681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15205546598402635521759787 22808319897603953282639681)
      ·
        refine ⟨17106239923202964961979761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22808319897603953282639681 17106239923202964961979761)
        ·
          refine ⟨12829679942402223721484821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17106239923202964961979761 12829679942402223721484821)
          ·
            refine ⟨601391247300104236944601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12829679942402223721484821 601391247300104236944601)
            ·
              refine ⟨451043435475078177708451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 601391247300104236944601 451043435475078177708451)
              ·
                refine ⟨676565153212617266562677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 451043435475078177708451 676565153212617266562677)
                ·
                  refine ⟨63427983113682868740251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 676565153212617266562677 63427983113682868740251)
                  ·
                    rfl

theorem cell22_555865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 1, 5].length) (baseStart_555865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_555865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_555865 prefixEnd_555865 := by exact prefixLift 555865
  have htrace : WordTrace (prefixWord ++ tailWord_555865) baseStart_555865 baseEnd_555865 := by
    simpa [prefixWord, tailWord_555865, baseEnd_555865] using wordTrace_append hprefix tailTrace_555865
  have hstable : (prefixWord ++ tailWord_555865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555865).length < 2 ^ (prefixWord ++ tailWord_555865).sum := by decide
  have hdescent : baseEnd_555865 < baseStart_555865 := by decide
  rcases family_descends (prefixWord ++ tailWord_555865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555891 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 3, 5]
def baseStart_555891 : Nat := 118140960795 + 555891 * 2 ^ 59
def prefixEnd_555891 : Nat := 4983230072969 + 3 ^ 40 * 555891 * 2
def baseEnd_555891 : Nat := 190292849672393205070673

theorem tailTrace_555891 : CollatzResearch.WordTrace tailWord_555891 prefixEnd_555891 190292849672393205070673 := by
  unfold tailWord_555891
  simp only [CollatzResearch.WordTrace]
  refine ⟨20275010429109320469459527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13516673619406213646306351 20275010429109320469459527)
  ·
    refine ⟨30412515643663980704189291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20275010429109320469459527 30412515643663980704189291)
    ·
      refine ⟨45618773465495971056283937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30412515643663980704189291 45618773465495971056283937)
      ·
        refine ⟨34214080099121978292212953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45618773465495971056283937 34214080099121978292212953)
        ·
          refine ⟨25660560074341483719159715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34214080099121978292212953 25660560074341483719159715)
          ·
            refine ⟨38490840111512225578739573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25660560074341483719159715 38490840111512225578739573)
            ·
              refine ⟨3608516260454271148006835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38490840111512225578739573 3608516260454271148006835)
              ·
                refine ⟨5412774390681406722010253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3608516260454271148006835 5412774390681406722010253)
                ·
                  refine ⟨2029790396505527520753845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5412774390681406722010253 2029790396505527520753845)
                  ·
                    refine ⟨190292849672393205070673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2029790396505527520753845 190292849672393205070673)
                    ·
                      rfl

theorem cell22_555891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 5].length) (baseStart_555891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_555891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_555891 prefixEnd_555891 := by exact prefixLift 555891
  have htrace : WordTrace (prefixWord ++ tailWord_555891) baseStart_555891 baseEnd_555891 := by
    simpa [prefixWord, tailWord_555891, baseEnd_555891] using wordTrace_append hprefix tailTrace_555891
  have hstable : (prefixWord ++ tailWord_555891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555891).length < 2 ^ (prefixWord ++ tailWord_555891).sum := by decide
  have hdescent : baseEnd_555891 < baseStart_555891 := by decide
  rcases family_descends (prefixWord ++ tailWord_555891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555925 : List Nat := [1, 3, 2, 1, 1, 4, 2, 3, 2, 3]
def baseStart_555925 : Nat := 118140960795 + 555925 * 2 ^ 59
def prefixEnd_555925 : Nat := 4983230072969 + 3 ^ 40 * 555925 * 2
def baseEnd_555925 : Nat := 190304488567228449720569

theorem tailTrace_555925 : CollatzResearch.WordTrace tailWord_555925 prefixEnd_555925 190304488567228449720569 := by
  unfold tailWord_555925
  simp only [CollatzResearch.WordTrace]
  refine ⟨20276250510986144276197229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13517500340657429517464819 20276250510986144276197229)
  ·
    refine ⟨7603593941619804103573961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20276250510986144276197229 7603593941619804103573961)
    ·
      refine ⟨5702695456214853077680471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7603593941619804103573961 5702695456214853077680471)
      ·
        refine ⟨8554043184322279616520707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5702695456214853077680471 8554043184322279616520707)
        ·
          refine ⟨12831064776483419424781061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8554043184322279616520707 12831064776483419424781061)
          ·
            refine ⟨2405824645590641142146449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12831064776483419424781061 2405824645590641142146449)
            ·
              refine ⟨1804368484192980856609837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2405824645590641142146449 1804368484192980856609837)
              ·
                refine ⟨676638181572367821228689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1804368484192980856609837 676638181572367821228689)
                ·
                  refine ⟨507478636179275865921517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 676638181572367821228689 507478636179275865921517)
                  ·
                    refine ⟨190304488567228449720569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 507478636179275865921517 190304488567228449720569)
                    ·
                      rfl

theorem cell22_555925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_555925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_555925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_555925 prefixEnd_555925 := by exact prefixLift 555925
  have htrace : WordTrace (prefixWord ++ tailWord_555925) baseStart_555925 baseEnd_555925 := by
    simpa [prefixWord, tailWord_555925, baseEnd_555925] using wordTrace_append hprefix tailTrace_555925
  have hstable : (prefixWord ++ tailWord_555925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555925).length < 2 ^ (prefixWord ++ tailWord_555925).sum := by decide
  have hdescent : baseEnd_555925 < baseStart_555925 := by decide
  rcases family_descends (prefixWord ++ tailWord_555925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555951 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 1, 8]
def baseStart_555951 : Nat := 118140960795 + 555951 * 2 ^ 59
def prefixEnd_555951 : Nat := 4983230072969 + 3 ^ 40 * 555951 * 2
def baseEnd_555951 : Nat := 190313388898573048570489

theorem tailTrace_555951 : CollatzResearch.WordTrace tailWord_555951 prefixEnd_555951 190313388898573048570489 := by
  unfold tailWord_555951
  simp only [CollatzResearch.WordTrace]
  refine ⟨20277198808891950716643707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13518132539261300477762471 20277198808891950716643707)
  ·
    refine ⟨30415798213337926074965561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20277198808891950716643707 30415798213337926074965561)
    ·
      refine ⟨22811848660003444556224171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30415798213337926074965561 22811848660003444556224171)
      ·
        refine ⟨34217772990005166834336257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22811848660003444556224171 34217772990005166834336257)
        ·
          refine ⟨25663329742503875125752193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34217772990005166834336257 25663329742503875125752193)
          ·
            refine ⟨19247497306877906344314145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25663329742503875125752193 19247497306877906344314145)
            ·
              refine ⟨14435622980158429758235609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19247497306877906344314145 14435622980158429758235609)
              ·
                refine ⟨10826717235118822318676707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14435622980158429758235609 10826717235118822318676707)
                ·
                  refine ⟨16240075852678233478015061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10826717235118822318676707 16240075852678233478015061)
                  ·
                    refine ⟨190313388898573048570489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 16240075852678233478015061 190313388898573048570489)
                    ·
                      rfl

theorem cell22_555951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 8].length) (baseStart_555951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_555951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_555951 prefixEnd_555951 := by exact prefixLift 555951
  have htrace : WordTrace (prefixWord ++ tailWord_555951) baseStart_555951 baseEnd_555951 := by
    simpa [prefixWord, tailWord_555951, baseEnd_555951] using wordTrace_append hprefix tailTrace_555951
  have hstable : (prefixWord ++ tailWord_555951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555951).length < 2 ^ (prefixWord ++ tailWord_555951).sum := by decide
  have hdescent : baseEnd_555951 < baseStart_555951 := by decide
  rcases family_descends (prefixWord ++ tailWord_555951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556021 : List Nat := [1, 3, 5, 2, 1, 2, 1, 1, 3, 3]
def baseStart_556021 : Nat := 118140960795 + 556021 * 2 ^ 59
def prefixEnd_556021 : Nat := 4983230072969 + 3 ^ 40 * 556021 * 2
def baseEnd_556021 : Nat := 190337351329116199320275

theorem tailTrace_556021 : CollatzResearch.WordTrace tailWord_556021 prefixEnd_556021 190337351329116199320275 := by
  unfold tailWord_556021
  simp only [CollatzResearch.WordTrace]
  refine ⟨20279751918638352671691917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13519834612425568447794611 20279751918638352671691917)
  ·
    refine ⟨7604906969489382251884469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20279751918638352671691917 7604906969489382251884469)
    ·
      refine ⟨712960028389629586114169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7604906969489382251884469 712960028389629586114169)
      ·
        refine ⟨534720021292222189585627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 712960028389629586114169 534720021292222189585627)
        ·
          refine ⟨802080031938333284378441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534720021292222189585627 802080031938333284378441)
          ·
            refine ⟨601560023953749963283831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 802080031938333284378441 601560023953749963283831)
            ·
              refine ⟨902340035930624944925747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 601560023953749963283831 902340035930624944925747)
              ·
                refine ⟨1353510053895937417388621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 902340035930624944925747 1353510053895937417388621)
                ·
                  refine ⟨507566270210976531520733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1353510053895937417388621 507566270210976531520733)
                  ·
                    refine ⟨190337351329116199320275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 507566270210976531520733 190337351329116199320275)
                    ·
                      rfl

theorem cell22_556021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_556021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556021 prefixEnd_556021 := by exact prefixLift 556021
  have htrace : WordTrace (prefixWord ++ tailWord_556021) baseStart_556021 baseEnd_556021 := by
    simpa [prefixWord, tailWord_556021, baseEnd_556021] using wordTrace_append hprefix tailTrace_556021
  have hstable : (prefixWord ++ tailWord_556021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556021).length < 2 ^ (prefixWord ++ tailWord_556021).sum := by decide
  have hdescent : baseEnd_556021 < baseStart_556021 := by decide
  rcases family_descends (prefixWord ++ tailWord_556021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556034 : List Nat := [3, 4, 1, 3, 1, 1, 1, 3, 5]
def baseStart_556034 : Nat := 118140960795 + 556034 * 2 ^ 59
def prefixEnd_556034 : Nat := 4983230072969 + 3 ^ 40 * 556034 * 2
def baseEnd_556034 : Nat := 63447267164929499581745

theorem tailTrace_556034 : CollatzResearch.WordTrace tailWord_556034 prefixEnd_556034 63447267164929499581745 := by
  unfold tailWord_556034
  simp only [CollatzResearch.WordTrace]
  refine ⟨5070056516897813972978789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13520150711727503927943437 5070056516897813972978789)
  ·
    refine ⟨950635596918340119933523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5070056516897813972978789 950635596918340119933523)
    ·
      refine ⟨1425953395377510179900285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 950635596918340119933523 1425953395377510179900285)
      ·
        refine ⟨534732523266566317462607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1425953395377510179900285 534732523266566317462607)
        ·
          refine ⟨802098784899849476193911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534732523266566317462607 802098784899849476193911)
          ·
            refine ⟨1203148177349774214290867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 802098784899849476193911 1203148177349774214290867)
            ·
              refine ⟨1804722266024661321436301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1203148177349774214290867 1804722266024661321436301)
              ·
                refine ⟨676770849759247995538613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1804722266024661321436301 676770849759247995538613)
                ·
                  refine ⟨63447267164929499581745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 676770849759247995538613 63447267164929499581745)
                  ·
                    rfl

theorem cell22_556034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_556034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556034 prefixEnd_556034 := by exact prefixLift 556034
  have htrace : WordTrace (prefixWord ++ tailWord_556034) baseStart_556034 baseEnd_556034 := by
    simpa [prefixWord, tailWord_556034, baseEnd_556034] using wordTrace_append hprefix tailTrace_556034
  have hstable : (prefixWord ++ tailWord_556034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556034).length < 2 ^ (prefixWord ++ tailWord_556034).sum := by decide
  have hdescent : baseEnd_556034 < baseStart_556034 := by decide
  rcases family_descends (prefixWord ++ tailWord_556034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556094 : List Nat := [4, 2, 1, 3, 1, 1, 2, 3, 2, 3]
def baseStart_556094 : Nat := 118140960795 + 556094 * 2 ^ 59
def prefixEnd_556094 : Nat := 4983230072969 + 3 ^ 40 * 556094 * 2
def baseEnd_556094 : Nat := 190362340720968342245051

theorem tailTrace_556094 : CollatzResearch.WordTrace tailWord_556094 prefixEnd_556094 190362340720968342245051 := by
  unfold tailWord_556094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2535301805921735767387417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13521609631582590759399557 2535301805921735767387417)
  ·
    refine ⟨1901476354441301825540563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2535301805921735767387417 1901476354441301825540563)
    ·
      refine ⟨2852214531661952738310845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1901476354441301825540563 2852214531661952738310845)
      ·
        refine ⟨1069580449373232276866567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2852214531661952738310845 1069580449373232276866567)
        ·
          refine ⟨1604370674059848415299851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1069580449373232276866567 1604370674059848415299851)
          ·
            refine ⟨2406556011089772622949777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1604370674059848415299851 2406556011089772622949777)
            ·
              refine ⟨1804917008317329467212333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2406556011089772622949777 1804917008317329467212333)
              ·
                refine ⟨676843878118998550204625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1804917008317329467212333 676843878118998550204625)
                ·
                  refine ⟨507632908589248912653469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 676843878118998550204625 507632908589248912653469)
                  ·
                    refine ⟨190362340720968342245051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 507632908589248912653469 190362340720968342245051)
                    ·
                      rfl

theorem cell22_556094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_556094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556094 prefixEnd_556094 := by exact prefixLift 556094
  have htrace : WordTrace (prefixWord ++ tailWord_556094) baseStart_556094 baseEnd_556094 := by
    simpa [prefixWord, tailWord_556094, baseEnd_556094] using wordTrace_append hprefix tailTrace_556094
  have hstable : (prefixWord ++ tailWord_556094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556094).length < 2 ^ (prefixWord ++ tailWord_556094).sum := by decide
  have hdescent : baseEnd_556094 < baseStart_556094 := by decide
  rcases family_descends (prefixWord ++ tailWord_556094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556109 : List Nat := [1, 6, 1, 1, 1, 4, 1, 1, 2, 4]
def baseStart_556109 : Nat := 118140960795 + 556109 * 2 ^ 59
def prefixEnd_556109 : Nat := 4983230072969 + 3 ^ 40 * 556109 * 2
def baseEnd_556109 : Nat := 190367475527513303120005

theorem tailTrace_556109 : CollatzResearch.WordTrace tailWord_556109 prefixEnd_556109 190367475527513303120005 := by
  unfold tailWord_556109
  simp only [CollatzResearch.WordTrace]
  refine ⟨20282961542319543700895381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13521974361546362467263587 20282961542319543700895381)
  ·
    refine ⟨950763822296228610979471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20282961542319543700895381 950763822296228610979471)
    ·
      refine ⟨1426145733444342916469207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 950763822296228610979471 1426145733444342916469207)
      ·
        refine ⟨2139218600166514374703811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1426145733444342916469207 2139218600166514374703811)
        ·
          refine ⟨3208827900249771562055717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2139218600166514374703811 3208827900249771562055717)
          ·
            refine ⟨601655231296832167885447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3208827900249771562055717 601655231296832167885447)
            ·
              refine ⟨902482846945248251828171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 601655231296832167885447 902482846945248251828171)
              ·
                refine ⟨1353724270417872377742257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 902482846945248251828171 1353724270417872377742257)
                ·
                  refine ⟨1015293202813404283306693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1353724270417872377742257 1015293202813404283306693)
                  ·
                    refine ⟨190367475527513303120005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1015293202813404283306693 190367475527513303120005)
                    ·
                      rfl

theorem cell22_556109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_556109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556109 prefixEnd_556109 := by exact prefixLift 556109
  have htrace : WordTrace (prefixWord ++ tailWord_556109) baseStart_556109 baseEnd_556109 := by
    simpa [prefixWord, tailWord_556109, baseEnd_556109] using wordTrace_append hprefix tailTrace_556109
  have hstable : (prefixWord ++ tailWord_556109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556109).length < 2 ^ (prefixWord ++ tailWord_556109).sum := by decide
  have hdescent : baseEnd_556109 < baseStart_556109 := by decide
  rcases family_descends (prefixWord ++ tailWord_556109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556135 : List Nat := [1, 1, 5, 1, 1, 4, 1, 1, 7]
def baseStart_556135 : Nat := 118140960795 + 556135 * 2 ^ 59
def prefixEnd_556135 : Nat := 4983230072969 + 3 ^ 40 * 556135 * 2
def baseEnd_556135 : Nat := 63458791952952633989975

theorem tailTrace_556135 : CollatzResearch.WordTrace tailWord_556135 prefixEnd_556135 63458791952952633989975 := by
  unfold tailWord_556135
  simp only [CollatzResearch.WordTrace]
  refine ⟨20283909840225350141341859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13522606560150233427561239 20283909840225350141341859)
  ·
    refine ⟨30425864760338025212012789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20283909840225350141341859 30425864760338025212012789)
    ·
      refine ⟨2852424821281689863626199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30425864760338025212012789 2852424821281689863626199)
      ·
        refine ⟨4278637231922534795439299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2852424821281689863626199 4278637231922534795439299)
        ·
          refine ⟨6417955847883802193158949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4278637231922534795439299 6417955847883802193158949)
          ·
            refine ⟨1203366721478212911217303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6417955847883802193158949 1203366721478212911217303)
            ·
              refine ⟨1805050082217319366825955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1203366721478212911217303 1805050082217319366825955)
              ·
                refine ⟨2707575123325979050238933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1805050082217319366825955 2707575123325979050238933)
                ·
                  refine ⟨63458791952952633989975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2707575123325979050238933 63458791952952633989975)
                  ·
                    rfl

theorem cell22_556135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 7].length) (baseStart_556135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556135 prefixEnd_556135 := by exact prefixLift 556135
  have htrace : WordTrace (prefixWord ++ tailWord_556135) baseStart_556135 baseEnd_556135 := by
    simpa [prefixWord, tailWord_556135, baseEnd_556135] using wordTrace_append hprefix tailTrace_556135
  have hstable : (prefixWord ++ tailWord_556135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556135).length < 2 ^ (prefixWord ++ tailWord_556135).sum := by decide
  have hdescent : baseEnd_556135 < baseStart_556135 := by decide
  rcases family_descends (prefixWord ++ tailWord_556135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556158 : List Nat := [4, 2, 4, 1, 1, 2, 2, 6]
def baseStart_556158 : Nat := 118140960795 + 556158 * 2 ^ 59
def prefixEnd_556158 : Nat := 4983230072969 + 3 ^ 40 * 556158 * 2
def baseEnd_556158 : Nat := 21153805469877056516095

theorem tailTrace_556158 : CollatzResearch.WordTrace tailWord_556158 prefixEnd_556158 21153805469877056516095 := by
  unfold tailWord_556158
  simp only [CollatzResearch.WordTrace]
  refine ⟨2535593589892753133678641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13523165812761350046286085 2535593589892753133678641)
  ·
    refine ⟨1901695192419564850258981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2535593589892753133678641 1901695192419564850258981)
    ·
      refine ⟨356567848578668409423559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1901695192419564850258981 356567848578668409423559)
      ·
        refine ⟨534851772868002614135339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356567848578668409423559 534851772868002614135339)
        ·
          refine ⟨802277659302003921203009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534851772868002614135339 802277659302003921203009)
          ·
            refine ⟨601708244476502940902257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 802277659302003921203009 601708244476502940902257)
            ·
              refine ⟨451281183357377205676693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 601708244476502940902257 451281183357377205676693)
              ·
                refine ⟨21153805469877056516095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 451281183357377205676693 21153805469877056516095)
                ·
                  rfl

theorem cell22_556158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 6].length) (baseStart_556158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556158 prefixEnd_556158 := by exact prefixLift 556158
  have htrace : WordTrace (prefixWord ++ tailWord_556158) baseStart_556158 baseEnd_556158 := by
    simpa [prefixWord, tailWord_556158, baseEnd_556158] using wordTrace_append hprefix tailTrace_556158
  have hstable : (prefixWord ++ tailWord_556158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556158).length < 2 ^ (prefixWord ++ tailWord_556158).sum := by decide
  have hdescent : baseEnd_556158 < baseStart_556158 := by decide
  rcases family_descends (prefixWord ++ tailWord_556158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556197 : List Nat := [1, 3, 1, 2, 1, 6, 1, 1, 6]
def baseStart_556197 : Nat := 118140960795 + 556197 * 2 ^ 59
def prefixEnd_556197 : Nat := 4983230072969 + 3 ^ 40 * 556197 * 2
def baseEnd_556197 : Nat := 63465866575303468973245

theorem tailTrace_556197 : CollatzResearch.WordTrace tailWord_556197 prefixEnd_556197 63465866575303468973245 := by
  unfold tailWord_556197
  simp only [CollatzResearch.WordTrace]
  refine ⟨20286171166000734730098845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13524114110667156486732563 20286171166000734730098845)
  ·
    refine ⟨7607314187250275523787067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20286171166000734730098845 7607314187250275523787067)
    ·
      refine ⟨11410971280875413285680601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7607314187250275523787067 11410971280875413285680601)
      ·
        refine ⟨8558228460656559964260451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11410971280875413285680601 8558228460656559964260451)
        ·
          refine ⟨12837342690984839946390677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8558228460656559964260451 12837342690984839946390677)
          ·
            refine ⟨601750438639914372487063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12837342690984839946390677 601750438639914372487063)
            ·
              refine ⟨902625657959871558730595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 601750438639914372487063 902625657959871558730595)
              ·
                refine ⟨1353938486939807338095893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 902625657959871558730595 1353938486939807338095893)
                ·
                  refine ⟨63465866575303468973245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1353938486939807338095893 63465866575303468973245)
                  ·
                    rfl

theorem cell22_556197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 6].length) (baseStart_556197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556197 prefixEnd_556197 := by exact prefixLift 556197
  have htrace : WordTrace (prefixWord ++ tailWord_556197) baseStart_556197 baseEnd_556197 := by
    simpa [prefixWord, tailWord_556197, baseEnd_556197] using wordTrace_append hprefix tailTrace_556197
  have hstable : (prefixWord ++ tailWord_556197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556197).length < 2 ^ (prefixWord ++ tailWord_556197).sum := by decide
  have hdescent : baseEnd_556197 < baseStart_556197 := by decide
  rcases family_descends (prefixWord ++ tailWord_556197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556248 : List Nat := [2, 1, 2, 2, 6, 1, 2, 2, 4]
def baseStart_556248 : Nat := 118140960795 + 556248 * 2 ^ 59
def prefixEnd_556248 : Nat := 4983230072969 + 3 ^ 40 * 556248 * 2
def baseEnd_556248 : Nat := 63471686022721091298193

theorem tailTrace_556248 : CollatzResearch.WordTrace tailWord_556248 prefixEnd_556248 63471686022721091298193 := by
  unfold tailWord_556248
  simp only [CollatzResearch.WordTrace]
  refine ⟨10144015644407985220102699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13525354192543980293470265 10144015644407985220102699)
  ·
    refine ⟨15216023466611977830154049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10144015644407985220102699 15216023466611977830154049)
    ·
      refine ⟨11412017599958983372615537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15216023466611977830154049 11412017599958983372615537)
      ·
        refine ⟨8559013199969237529461653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11412017599958983372615537 8559013199969237529461653)
        ·
          refine ⟨401203743748558009193515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8559013199969237529461653 401203743748558009193515)
          ·
            refine ⟨601805615622837013790273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401203743748558009193515 601805615622837013790273)
            ·
              refine ⟨451354211717127760342705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 601805615622837013790273 451354211717127760342705)
              ·
                refine ⟨338515658787845820257029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 451354211717127760342705 338515658787845820257029)
                ·
                  refine ⟨63471686022721091298193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 338515658787845820257029 63471686022721091298193)
                  ·
                    rfl

theorem cell22_556248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 2, 4].length) (baseStart_556248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556248 prefixEnd_556248 := by exact prefixLift 556248
  have htrace : WordTrace (prefixWord ++ tailWord_556248) baseStart_556248 baseEnd_556248 := by
    simpa [prefixWord, tailWord_556248, baseEnd_556248] using wordTrace_append hprefix tailTrace_556248
  have hstable : (prefixWord ++ tailWord_556248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556248).length < 2 ^ (prefixWord ++ tailWord_556248).sum := by decide
  have hdescent : baseEnd_556248 < baseStart_556248 := by decide
  rcases family_descends (prefixWord ++ tailWord_556248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556255 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 2, 6]
def baseStart_556255 : Nat := 118140960795 + 556255 * 2 ^ 59
def prefixEnd_556255 : Nat := 4983230072969 + 3 ^ 40 * 556255 * 2
def baseEnd_556255 : Nat := 190417454311217588969557

theorem tailTrace_556255 : CollatzResearch.WordTrace tailWord_556255 prefixEnd_556255 190417454311217588969557 := by
  unfold tailWord_556255
  simp only [CollatzResearch.WordTrace]
  refine ⟨20288286599790610635710219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13525524399860407090473479 20288286599790610635710219)
  ·
    refine ⟨30432429899685915953565329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20288286599790610635710219 30432429899685915953565329)
    ·
      refine ⟨22824322424764436965173997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30432429899685915953565329 22824322424764436965173997)
      ·
        refine ⟨8559120909286663861940249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22824322424764436965173997 8559120909286663861940249)
        ·
          refine ⟨6419340681964997896455187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8559120909286663861940249 6419340681964997896455187)
          ·
            refine ⟨9629011022947496844682781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6419340681964997896455187 9629011022947496844682781)
            ·
              refine ⟨3610879133605311316756043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9629011022947496844682781 3610879133605311316756043)
              ·
                refine ⟨5416318700407966975134065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3610879133605311316756043 5416318700407966975134065)
                ·
                  refine ⟨4062239025305975231350549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5416318700407966975134065 4062239025305975231350549)
                  ·
                    refine ⟨190417454311217588969557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4062239025305975231350549 190417454311217588969557)
                    ·
                      rfl

theorem cell22_556255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 6].length) (baseStart_556255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556255 prefixEnd_556255 := by exact prefixLift 556255
  have htrace : WordTrace (prefixWord ++ tailWord_556255) baseStart_556255 baseEnd_556255 := by
    simpa [prefixWord, tailWord_556255, baseEnd_556255] using wordTrace_append hprefix tailTrace_556255
  have hstable : (prefixWord ++ tailWord_556255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556255).length < 2 ^ (prefixWord ++ tailWord_556255).sum := by decide
  have hdescent : baseEnd_556255 < baseStart_556255 := by decide
  rcases family_descends (prefixWord ++ tailWord_556255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556291 : List Nat := [1, 1, 1, 3, 2, 5, 2, 3, 1, 3]
def baseStart_556291 : Nat := 118140960795 + 556291 * 2 ^ 59
def prefixEnd_556291 : Nat := 4983230072969 + 3 ^ 40 * 556291 * 2
def baseEnd_556291 : Nat := 190429777846925495069447

theorem tailTrace_556291 : CollatzResearch.WordTrace tailWord_556291 prefixEnd_556291 190429777846925495069447 := by
  unfold tailWord_556291
  simp only [CollatzResearch.WordTrace]
  refine ⟨20289599627660188784020727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13526399751773459189347151 20289599627660188784020727)
  ·
    refine ⟨30434399441490283176031091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20289599627660188784020727 30434399441490283176031091)
    ·
      refine ⟨45651599162235424764046637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30434399441490283176031091 45651599162235424764046637)
      ·
        refine ⟨17119349685838284286517489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45651599162235424764046637 17119349685838284286517489)
        ·
          refine ⟨12839512264378713214888117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17119349685838284286517489 12839512264378713214888117)
          ·
            refine ⟨1203704274785504363895761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12839512264378713214888117 1203704274785504363895761)
            ·
              refine ⟨902778206089128272921821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1203704274785504363895761 902778206089128272921821)
              ·
                refine ⟨338541827283423102345683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 902778206089128272921821 338541827283423102345683)
                ·
                  refine ⟨507812740925134653518525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 338541827283423102345683 507812740925134653518525)
                  ·
                    refine ⟨190429777846925495069447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 507812740925134653518525 190429777846925495069447)
                    ·
                      rfl

theorem cell22_556291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 3, 1, 3].length) (baseStart_556291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556291 prefixEnd_556291 := by exact prefixLift 556291
  have htrace : WordTrace (prefixWord ++ tailWord_556291) baseStart_556291 baseEnd_556291 := by
    simpa [prefixWord, tailWord_556291, baseEnd_556291] using wordTrace_append hprefix tailTrace_556291
  have hstable : (prefixWord ++ tailWord_556291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556291).length < 2 ^ (prefixWord ++ tailWord_556291).sum := by decide
  have hdescent : baseEnd_556291 < baseStart_556291 := by decide
  rcases family_descends (prefixWord ++ tailWord_556291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556302 : List Nat := [4, 1, 1, 2, 1, 3, 1, 2, 2, 5]
def baseStart_556302 : Nat := 118140960795 + 556302 * 2 ^ 59
def prefixEnd_556302 : Nat := 4983230072969 + 3 ^ 40 * 556302 * 2
def baseEnd_556302 : Nat := 190433543371725133044413

theorem tailTrace_556302 : CollatzResearch.WordTrace tailWord_556302 prefixEnd_556302 190433543371725133044413 := by
  unfold tailWord_556302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2536250103827542207833895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13526667220413558441780773 2536250103827542207833895)
  ·
    refine ⟨3804375155741313311750843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2536250103827542207833895 3804375155741313311750843)
    ·
      refine ⟨5706562733611969967626265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3804375155741313311750843 5706562733611969967626265)
      ·
        refine ⟨4279922050208977475719699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5706562733611969967626265 4279922050208977475719699)
        ·
          refine ⟨6419883075313466213579549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4279922050208977475719699 6419883075313466213579549)
          ·
            refine ⟨2407456153242549830092331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6419883075313466213579549 2407456153242549830092331)
            ·
              refine ⟨3611184229863824745138497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2407456153242549830092331 3611184229863824745138497)
              ·
                refine ⟨2708388172397868558853873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3611184229863824745138497 2708388172397868558853873)
                ·
                  refine ⟨2031291129298401419140405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2708388172397868558853873 2031291129298401419140405)
                  ·
                    refine ⟨190433543371725133044413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2031291129298401419140405 190433543371725133044413)
                    ·
                      rfl

theorem cell22_556302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_556302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556302 prefixEnd_556302 := by exact prefixLift 556302
  have htrace : WordTrace (prefixWord ++ tailWord_556302) baseStart_556302 baseEnd_556302 := by
    simpa [prefixWord, tailWord_556302, baseEnd_556302] using wordTrace_append hprefix tailTrace_556302
  have hstable : (prefixWord ++ tailWord_556302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556302).length < 2 ^ (prefixWord ++ tailWord_556302).sum := by decide
  have hdescent : baseEnd_556302 < baseStart_556302 := by decide
  rcases family_descends (prefixWord ++ tailWord_556302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556342 : List Nat := [5, 1, 2, 3, 1, 2, 1, 3, 1, 3]
def baseStart_556342 : Nat := 118140960795 + 556342 * 2 ^ 59
def prefixEnd_556342 : Nat := 4983230072969 + 3 ^ 40 * 556342 * 2
def baseEnd_556342 : Nat := 190447236189178362044291

theorem tailTrace_556342 : CollatzResearch.WordTrace tailWord_556342 prefixEnd_556342 190447236189178362044291 := by
  unfold tailWord_556342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1268216234404714030882955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13527639833650282996084853 1268216234404714030882955)
  ·
    refine ⟨1902324351607071046324433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1268216234404714030882955 1902324351607071046324433)
    ·
      refine ⟨1426743263705303284743325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1902324351607071046324433 1426743263705303284743325)
      ·
        refine ⟨535028723889488731778747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1426743263705303284743325 535028723889488731778747)
        ·
          refine ⟨802543085834233097668121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 535028723889488731778747 802543085834233097668121)
          ·
            refine ⟨601907314375674823251091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 802543085834233097668121 601907314375674823251091)
            ·
              refine ⟨902860971563512234876637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 601907314375674823251091 902860971563512234876637)
              ·
                refine ⟨338572864336317088078739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 902860971563512234876637 338572864336317088078739)
                ·
                  refine ⟨507859296504475632118109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 338572864336317088078739 507859296504475632118109)
                  ·
                    refine ⟨190447236189178362044291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 507859296504475632118109 190447236189178362044291)
                    ·
                      rfl

theorem cell22_556342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_556342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556342 prefixEnd_556342 := by exact prefixLift 556342
  have htrace : WordTrace (prefixWord ++ tailWord_556342) baseStart_556342 baseEnd_556342 := by
    simpa [prefixWord, tailWord_556342, baseEnd_556342] using wordTrace_append hprefix tailTrace_556342
  have hstable : (prefixWord ++ tailWord_556342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556342).length < 2 ^ (prefixWord ++ tailWord_556342).sum := by decide
  have hdescent : baseEnd_556342 < baseStart_556342 := by decide
  rcases family_descends (prefixWord ++ tailWord_556342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556364 : List Nat := [2, 2, 1, 3, 2, 2, 2, 1, 4, 3]
def baseStart_556364 : Nat := 118140960795 + 556364 * 2 ^ 59
def prefixEnd_556364 : Nat := 4983230072969 + 3 ^ 40 * 556364 * 2
def baseEnd_556364 : Nat := 190454767238777637994223

theorem tailTrace_556364 : CollatzResearch.WordTrace tailWord_556364 prefixEnd_556364 190454767238777637994223 := by
  unfold tailWord_556364
  simp only [CollatzResearch.WordTrace]
  refine ⟨10146131078197861125714073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13528174770930481500952097 10146131078197861125714073)
  ·
    refine ⟨7609598308648395844285555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10146131078197861125714073 7609598308648395844285555)
    ·
      refine ⟨11414397462972593766428333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7609598308648395844285555 11414397462972593766428333)
      ·
        refine ⟨4280399048614722662410625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11414397462972593766428333 4280399048614722662410625)
        ·
          refine ⟨3210299286461041996807969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4280399048614722662410625 3210299286461041996807969)
          ·
            refine ⟨2407724464845781497605977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3210299286461041996807969 2407724464845781497605977)
            ·
              refine ⟨1805793348634336123204483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2407724464845781497605977 1805793348634336123204483)
              ·
                refine ⟨2708690022951504184806725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1805793348634336123204483 2708690022951504184806725)
                ·
                  refine ⟨507879379303407034651261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2708690022951504184806725 507879379303407034651261)
                  ·
                    refine ⟨190454767238777637994223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 507879379303407034651261 190454767238777637994223)
                    ·
                      rfl

theorem cell22_556364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 4, 3].length) (baseStart_556364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556364 prefixEnd_556364 := by exact prefixLift 556364
  have htrace : WordTrace (prefixWord ++ tailWord_556364) baseStart_556364 baseEnd_556364 := by
    simpa [prefixWord, tailWord_556364, baseEnd_556364] using wordTrace_append hprefix tailTrace_556364
  have hstable : (prefixWord ++ tailWord_556364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556364).length < 2 ^ (prefixWord ++ tailWord_556364).sum := by decide
  have hdescent : baseEnd_556364 < baseStart_556364 := by decide
  rcases family_descends (prefixWord ++ tailWord_556364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556366 : List Nat := [4, 1, 1, 1, 1, 1, 7, 2, 4]
def baseStart_556366 : Nat := 118140960795 + 556366 * 2 ^ 59
def prefixEnd_556366 : Nat := 4983230072969 + 3 ^ 40 * 556366 * 2
def baseEnd_556366 : Nat := 63485150626550099814739

theorem tailTrace_556366 : CollatzResearch.WordTrace tailWord_556366 prefixEnd_556366 63485150626550099814739 := by
  unfold tailWord_556366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2536541887798559574125119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13528223401592317728667301 2536541887798559574125119)
  ·
    refine ⟨3804812831697839361187679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2536541887798559574125119 3804812831697839361187679)
    ·
      refine ⟨5707219247546759041781519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3804812831697839361187679 5707219247546759041781519)
      ·
        refine ⟨8560828871320138562672279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5707219247546759041781519 8560828871320138562672279)
        ·
          refine ⟨12841243306980207844008419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8560828871320138562672279 12841243306980207844008419)
          ·
            refine ⟨19261864960470311766012629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12841243306980207844008419 19261864960470311766012629)
            ·
              refine ⟨451449960011022932015921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 19261864960470311766012629 451449960011022932015921)
              ·
                refine ⟨338587470008267199011941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 451449960011022932015921 338587470008267199011941)
                ·
                  refine ⟨63485150626550099814739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 338587470008267199011941 63485150626550099814739)
                  ·
                    rfl

theorem cell22_556366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_556366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556366 prefixEnd_556366 := by exact prefixLift 556366
  have htrace : WordTrace (prefixWord ++ tailWord_556366) baseStart_556366 baseEnd_556366 := by
    simpa [prefixWord, tailWord_556366, baseEnd_556366] using wordTrace_append hprefix tailTrace_556366
  have hstable : (prefixWord ++ tailWord_556366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556366).length < 2 ^ (prefixWord ++ tailWord_556366).sum := by decide
  have hdescent : baseEnd_556366 < baseStart_556366 := by decide
  rcases family_descends (prefixWord ++ tailWord_556366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556437 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 1, 7]
def baseStart_556437 : Nat := 118140960795 + 556437 * 2 ^ 59
def prefixEnd_556437 : Nat := 4983230072969 + 3 ^ 40 * 556437 * 2
def baseEnd_556437 : Nat := 190479756630629780918999

theorem tailTrace_556437 : CollatzResearch.WordTrace tailWord_556437 prefixEnd_556437 190479756630629780918999 := by
  unfold tailWord_556437
  simp only [CollatzResearch.WordTrace]
  refine ⟨20294924685131255718835565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13529949790087503812557043 20294924685131255718835565)
  ·
    refine ⟨7610596756924220894563337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20294924685131255718835565 7610596756924220894563337)
    ·
      refine ⟨5707947567693165670922503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7610596756924220894563337 5707947567693165670922503)
      ·
        refine ⟨8561921351539748506383755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5707947567693165670922503 8561921351539748506383755)
        ·
          refine ⟨12842882027309622759575633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8561921351539748506383755 12842882027309622759575633)
          ·
            refine ⟨9632161520482217069681725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12842882027309622759575633 9632161520482217069681725)
            ·
              refine ⟨3612060570180831401130647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9632161520482217069681725 3612060570180831401130647)
              ·
                refine ⟨5418090855271247101695971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3612060570180831401130647 5418090855271247101695971)
                ·
                  refine ⟨8127136282906870652543957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5418090855271247101695971 8127136282906870652543957)
                  ·
                    refine ⟨190479756630629780918999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8127136282906870652543957 190479756630629780918999)
                    ·
                      rfl

theorem cell22_556437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_556437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556437 prefixEnd_556437 := by exact prefixLift 556437
  have htrace : WordTrace (prefixWord ++ tailWord_556437) baseStart_556437 baseEnd_556437 := by
    simpa [prefixWord, tailWord_556437, baseEnd_556437] using wordTrace_append hprefix tailTrace_556437
  have hstable : (prefixWord ++ tailWord_556437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556437).length < 2 ^ (prefixWord ++ tailWord_556437).sum := by decide
  have hdescent : baseEnd_556437 < baseStart_556437 := by decide
  rcases family_descends (prefixWord ++ tailWord_556437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556473 : List Nat := [1, 2, 1, 4, 5, 1, 1, 2, 5]
def baseStart_556473 : Nat := 118140960795 + 556473 * 2 ^ 59
def prefixEnd_556473 : Nat := 4983230072969 + 3 ^ 40 * 556473 * 2
def baseEnd_556473 : Nat := 63497360055445895672963

theorem tailTrace_556473 : CollatzResearch.WordTrace tailWord_556473 prefixEnd_556473 63497360055445895672963 := by
  unfold tailWord_556473
  simp only [CollatzResearch.WordTrace]
  refine ⟨20296237713000833867146073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13530825142000555911430715 20296237713000833867146073)
  ·
    refine ⟨15222178284750625400359555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20296237713000833867146073 15222178284750625400359555)
    ·
      refine ⟨22833267427125938100539333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15222178284750625400359555 22833267427125938100539333)
      ·
        refine ⟨4281237642586113393851125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22833267427125938100539333 4281237642586113393851125)
        ·
          refine ⟨401366028992448130673543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4281237642586113393851125 401366028992448130673543)
          ·
            refine ⟨602049043488672196010315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401366028992448130673543 602049043488672196010315)
            ·
              refine ⟨903073565233008294015473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 602049043488672196010315 903073565233008294015473)
              ·
                refine ⟨677305173924756220511605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 903073565233008294015473 677305173924756220511605)
                ·
                  refine ⟨63497360055445895672963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 677305173924756220511605 63497360055445895672963)
                  ·
                    rfl

theorem cell22_556473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 5].length) (baseStart_556473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556473 prefixEnd_556473 := by exact prefixLift 556473
  have htrace : WordTrace (prefixWord ++ tailWord_556473) baseStart_556473 baseEnd_556473 := by
    simpa [prefixWord, tailWord_556473, baseEnd_556473] using wordTrace_append hprefix tailTrace_556473
  have hstable : (prefixWord ++ tailWord_556473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556473).length < 2 ^ (prefixWord ++ tailWord_556473).sum := by decide
  have hdescent : baseEnd_556473 < baseStart_556473 := by decide
  rcases family_descends (prefixWord ++ tailWord_556473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556529 : List Nat := [1, 2, 2, 2, 3, 4, 8]
def baseStart_556529 : Nat := 118140960795 + 556529 * 2 ^ 59
def prefixEnd_556529 : Nat := 4983230072969 + 3 ^ 40 * 556529 * 2
def baseEnd_556529 : Nat := 7055972226324896578471

theorem tailTrace_556529 : CollatzResearch.WordTrace tailWord_556529 prefixEnd_556529 7055972226324896578471 := by
  unfold tailWord_556529
  simp only [CollatzResearch.WordTrace]
  refine ⟨20298280200797955431184641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13532186800531970287456427 20298280200797955431184641)
  ·
    refine ⟨15223710150598466573388481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20298280200797955431184641 15223710150598466573388481)
    ·
      refine ⟨11417782612948849930041361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15223710150598466573388481 11417782612948849930041361)
      ·
        refine ⟨8563336959711637447531021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11417782612948849930041361 8563336959711637447531021)
        ·
          refine ⟨3211251359891864042824133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8563336959711637447531021 3211251359891864042824133)
          ·
            refine ⟨602109629979724508029525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3211251359891864042824133 602109629979724508029525)
            ·
              refine ⟨7055972226324896578471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 602109629979724508029525 7055972226324896578471)
              ·
                rfl

theorem cell22_556529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 8].length) (baseStart_556529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556529 prefixEnd_556529 := by exact prefixLift 556529
  have htrace : WordTrace (prefixWord ++ tailWord_556529) baseStart_556529 baseEnd_556529 := by
    simpa [prefixWord, tailWord_556529, baseEnd_556529] using wordTrace_append hprefix tailTrace_556529
  have hstable : (prefixWord ++ tailWord_556529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556529).length < 2 ^ (prefixWord ++ tailWord_556529).sum := by decide
  have hdescent : baseEnd_556529 < baseStart_556529 := by decide
  rcases family_descends (prefixWord ++ tailWord_556529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556533 : List Nat := [1, 3, 5, 1, 1, 1, 2, 1, 4, 3]
def baseStart_556533 : Nat := 118140960795 + 556533 * 2 ^ 59
def prefixEnd_556533 : Nat := 4983230072969 + 3 ^ 40 * 556533 * 2
def baseEnd_556533 : Nat := 190512619392517530518705

theorem tailTrace_556533 : CollatzResearch.WordTrace tailWord_556533 prefixEnd_556533 190512619392517530518705 := by
  unfold tailWord_556533
  simp only [CollatzResearch.WordTrace]
  refine ⟨20298426092783464114330253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13532284061855642742886835 20298426092783464114330253)
  ·
    refine ⟨7611909784793799042873845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20298426092783464114330253 7611909784793799042873845)
    ·
      refine ⟨713616542324418660269423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7611909784793799042873845 713616542324418660269423)
      ·
        refine ⟨1070424813486627990404135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 713616542324418660269423 1070424813486627990404135)
        ·
          refine ⟨1605637220229941985606203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1070424813486627990404135 1605637220229941985606203)
          ·
            refine ⟨2408455830344912978409305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1605637220229941985606203 2408455830344912978409305)
            ·
              refine ⟨1806341872758684733806979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2408455830344912978409305 1806341872758684733806979)
              ·
                refine ⟨2709512809138027100710469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1806341872758684733806979 2709512809138027100710469)
                ·
                  refine ⟨508033651713380081383213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2709512809138027100710469 508033651713380081383213)
                  ·
                    refine ⟨190512619392517530518705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 508033651713380081383213 190512619392517530518705)
                    ·
                      rfl

theorem cell22_556533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_556533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556533 prefixEnd_556533 := by exact prefixLift 556533
  have htrace : WordTrace (prefixWord ++ tailWord_556533) baseStart_556533 baseEnd_556533 := by
    simpa [prefixWord, tailWord_556533, baseEnd_556533] using wordTrace_append hprefix tailTrace_556533
  have hstable : (prefixWord ++ tailWord_556533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556533).length < 2 ^ (prefixWord ++ tailWord_556533).sum := by decide
  have hdescent : baseEnd_556533 < baseStart_556533 := by decide
  rcases family_descends (prefixWord ++ tailWord_556533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556546 : List Nat := [3, 4, 1, 2, 1, 1, 1, 9]
def baseStart_556546 : Nat := 118140960795 + 556546 * 2 ^ 59
def prefixEnd_556546 : Nat := 4983230072969 + 3 ^ 40 * 556546 * 2
def baseEnd_556546 : Nat := 21168563284243314438185

theorem tailTrace_556546 : CollatzResearch.WordTrace tailWord_556546 prefixEnd_556546 21168563284243314438185 := by
  unfold tailWord_556546
  simp only [CollatzResearch.WordTrace]
  refine ⟨5074725060434091833638373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13532600161157578223035661 5074725060434091833638373)
  ·
    refine ⟨951510948831392218807195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5074725060434091833638373 951510948831392218807195)
    ·
      refine ⟨1427266423247088328210793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 951510948831392218807195 1427266423247088328210793)
      ·
        refine ⟨1070449817435316246158095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1427266423247088328210793 1070449817435316246158095)
        ·
          refine ⟨1605674726152974369237143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1070449817435316246158095 1605674726152974369237143)
          ·
            refine ⟨2408512089229461553855715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1605674726152974369237143 2408512089229461553855715)
            ·
              refine ⟨3612768133844192330783573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2408512089229461553855715 3612768133844192330783573)
              ·
                refine ⟨21168563284243314438185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3612768133844192330783573 21168563284243314438185)
                ·
                  rfl

theorem cell22_556546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 9].length) (baseStart_556546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556546 prefixEnd_556546 := by exact prefixLift 556546
  have htrace : WordTrace (prefixWord ++ tailWord_556546) baseStart_556546 baseEnd_556546 := by
    simpa [prefixWord, tailWord_556546, baseEnd_556546] using wordTrace_append hprefix tailTrace_556546
  have hstable : (prefixWord ++ tailWord_556546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556546).length < 2 ^ (prefixWord ++ tailWord_556546).sum := by decide
  have hdescent : baseEnd_556546 < baseStart_556546 := by decide
  rcases family_descends (prefixWord ++ tailWord_556546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556595 : List Nat := [1, 1, 1, 2, 4, 3, 4, 2, 1, 3]
def baseStart_556595 : Nat := 118140960795 + 556595 * 2 ^ 59
def prefixEnd_556595 : Nat := 4983230072969 + 3 ^ 40 * 556595 * 2
def baseEnd_556595 : Nat := 190533843259570035468515

theorem tailTrace_556595 : CollatzResearch.WordTrace tailWord_556595 prefixEnd_556595 190533843259570035468515 := by
  unfold tailWord_556595
  simp only [CollatzResearch.WordTrace]
  refine ⟨20300687418558848703087239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13533791612372565802058159 20300687418558848703087239)
  ·
    refine ⟨30451031127838273054630859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20300687418558848703087239 30451031127838273054630859)
    ·
      refine ⟨45676546691757409581946289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30451031127838273054630859 45676546691757409581946289)
      ·
        refine ⟨34257410018818057186459717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45676546691757409581946289 34257410018818057186459717)
        ·
          refine ⟨6423264378528385722461197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34257410018818057186459717 6423264378528385722461197)
          ·
            refine ⟨2408724141948144645922949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6423264378528385722461197 2408724141948144645922949)
            ·
              refine ⟨451635776615277121110553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2408724141948144645922949 451635776615277121110553)
              ·
                refine ⟨338726832461457840832915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 451635776615277121110553 338726832461457840832915)
                ·
                  refine ⟨508090248692186761249373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 338726832461457840832915 508090248692186761249373)
                  ·
                    refine ⟨190533843259570035468515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 508090248692186761249373 190533843259570035468515)
                    ·
                      rfl

theorem cell22_556595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 2, 1, 3].length) (baseStart_556595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556595 prefixEnd_556595 := by exact prefixLift 556595
  have htrace : WordTrace (prefixWord ++ tailWord_556595) baseStart_556595 baseEnd_556595 := by
    simpa [prefixWord, tailWord_556595, baseEnd_556595] using wordTrace_append hprefix tailTrace_556595
  have hstable : (prefixWord ++ tailWord_556595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556595).length < 2 ^ (prefixWord ++ tailWord_556595).sum := by decide
  have hdescent : baseEnd_556595 < baseStart_556595 := by decide
  rcases family_descends (prefixWord ++ tailWord_556595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556653 : List Nat := [1, 5, 1, 1, 4, 1, 2, 1, 6]
def baseStart_556653 : Nat := 118140960795 + 556653 * 2 ^ 59
def prefixEnd_556653 : Nat := 4983230072969 + 3 ^ 40 * 556653 * 2
def baseEnd_556653 : Nat := 63517899281625739172779

theorem tailTrace_556653 : CollatzResearch.WordTrace tailWord_556653 prefixEnd_556653 63517899281625739172779 := by
  unfold tailWord_556653
  simp only [CollatzResearch.WordTrace]
  refine ⟨20302802852348724608698613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13535201901565816405799075 20302802852348724608698613)
  ·
    refine ⟨1903387767407692932065495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20302802852348724608698613 1903387767407692932065495)
    ·
      refine ⟨2855081651111539398098243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1903387767407692932065495 2855081651111539398098243)
      ·
        refine ⟨4282622476667309097147365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2855081651111539398098243 4282622476667309097147365)
        ·
          refine ⟨802991714375120455715131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4282622476667309097147365 802991714375120455715131)
          ·
            refine ⟨1204487571562680683572697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 802991714375120455715131 1204487571562680683572697)
            ·
              refine ⟨903365678672010512679523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1204487571562680683572697 903365678672010512679523)
              ·
                refine ⟨1355048518008015769019285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 903365678672010512679523 1355048518008015769019285)
                ·
                  refine ⟨63517899281625739172779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1355048518008015769019285 63517899281625739172779)
                  ·
                    rfl

theorem cell22_556653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_556653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556653 prefixEnd_556653 := by exact prefixLift 556653
  have htrace : WordTrace (prefixWord ++ tailWord_556653) baseStart_556653 baseEnd_556653 := by
    simpa [prefixWord, tailWord_556653, baseEnd_556653] using wordTrace_append hprefix tailTrace_556653
  have hstable : (prefixWord ++ tailWord_556653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556653).length < 2 ^ (prefixWord ++ tailWord_556653).sum := by decide
  have hdescent : baseEnd_556653 < baseStart_556653 := by decide
  rcases family_descends (prefixWord ++ tailWord_556653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556681 : List Nat := [1, 2, 1, 1, 4, 1, 6, 6]
def baseStart_556681 : Nat := 118140960795 + 556681 * 2 ^ 59
def prefixEnd_556681 : Nat := 4983230072969 + 3 ^ 40 * 556681 * 2
def baseEnd_556681 : Nat := 21173698090788275313139

theorem tailTrace_556681 : CollatzResearch.WordTrace tailWord_556681 prefixEnd_556681 21173698090788275313139 := by
  unfold tailWord_556681
  simp only [CollatzResearch.WordTrace]
  refine ⟨20303824096247285390717897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13535882730831523593811931 20303824096247285390717897)
  ·
    refine ⟨15227868072185464043038423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20303824096247285390717897 15227868072185464043038423)
    ·
      refine ⟨22841802108278196064557635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15227868072185464043038423 22841802108278196064557635)
      ·
        refine ⟨34262703162417294096836453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22841802108278196064557635 34262703162417294096836453)
        ·
          refine ⟨6424256842953242643156835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34262703162417294096836453 6424256842953242643156835)
          ·
            refine ⟨9636385264429863964735253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6424256842953242643156835 9636385264429863964735253)
            ·
              refine ⟨451705559270149873346965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9636385264429863964735253 451705559270149873346965)
              ·
                refine ⟨21173698090788275313139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 451705559270149873346965 21173698090788275313139)
                ·
                  rfl

theorem cell22_556681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 6].length) (baseStart_556681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556681 prefixEnd_556681 := by exact prefixLift 556681
  have htrace : WordTrace (prefixWord ++ tailWord_556681) baseStart_556681 baseEnd_556681 := by
    simpa [prefixWord, tailWord_556681, baseEnd_556681] using wordTrace_append hprefix tailTrace_556681
  have hstable : (prefixWord ++ tailWord_556681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556681).length < 2 ^ (prefixWord ++ tailWord_556681).sum := by decide
  have hdescent : baseEnd_556681 < baseStart_556681 := by decide
  rcases family_descends (prefixWord ++ tailWord_556681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556764 : List Nat := [2, 2, 5, 1, 2, 1, 1, 4, 1, 3]
def baseStart_556764 : Nat := 118140960795 + 556764 * 2 ^ 59
def prefixEnd_556764 : Nat := 4983230072969 + 3 ^ 40 * 556764 * 2
def baseEnd_556764 : Nat := 190591695413309927992997

theorem tailTrace_556764 : CollatzResearch.WordTrace tailWord_556764 prefixEnd_556764 190591695413309927992997 := by
  unfold tailWord_556764
  simp only [CollatzResearch.WordTrace]
  refine ⟨10153425677473295282994673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13537900903297727043992897 10153425677473295282994673)
  ·
    refine ⟨7615069258104971462246005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10153425677473295282994673 7615069258104971462246005)
    ·
      refine ⟨713912742947341074585563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7615069258104971462246005 713912742947341074585563)
      ·
        refine ⟨1070869114421011611878345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 713912742947341074585563 1070869114421011611878345)
        ·
          refine ⟨803151835815758708908759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1070869114421011611878345 803151835815758708908759)
          ·
            refine ⟨1204727753723638063363139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 803151835815758708908759 1204727753723638063363139)
            ·
              refine ⟨1807091630585457095044709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1204727753723638063363139 1807091630585457095044709)
              ·
                refine ⟨338829680734773205320883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1807091630585457095044709 338829680734773205320883)
                ·
                  refine ⟨508244521102159807981325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 338829680734773205320883 508244521102159807981325)
                  ·
                    refine ⟨190591695413309927992997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 508244521102159807981325 190591695413309927992997)
                    ·
                      rfl

theorem cell22_556764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_556764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556764 prefixEnd_556764 := by exact prefixLift 556764
  have htrace : WordTrace (prefixWord ++ tailWord_556764) baseStart_556764 baseEnd_556764 := by
    simpa [prefixWord, tailWord_556764, baseEnd_556764] using wordTrace_append hprefix tailTrace_556764
  have hstable : (prefixWord ++ tailWord_556764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556764).length < 2 ^ (prefixWord ++ tailWord_556764).sum := by decide
  have hdescent : baseEnd_556764 < baseStart_556764 := by decide
  rcases family_descends (prefixWord ++ tailWord_556764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556775 : List Nat := [1, 1, 5, 4, 1, 1, 1, 1, 2, 5]
def baseStart_556775 : Nat := 118140960795 + 556775 * 2 ^ 59
def prefixEnd_556775 : Nat := 4983230072969 + 3 ^ 40 * 556775 * 2
def baseEnd_556775 : Nat := 190595460938109565967963

theorem tailTrace_556775 : CollatzResearch.WordTrace tailWord_556775 prefixEnd_556775 190595460938109565967963 := by
  unfold tailWord_556775
  simp only [CollatzResearch.WordTrace]
  refine ⟨20307252557906739444639779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13538168371937826296426519 20307252557906739444639779)
  ·
    refine ⟨30460878836860109166959669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20307252557906739444639779 30460878836860109166959669)
    ·
      refine ⟨2855707390955635234402469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30460878836860109166959669 2855707390955635234402469)
      ·
        refine ⟨535445135804181606450463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2855707390955635234402469 535445135804181606450463)
        ·
          refine ⟨803167703706272409675695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 535445135804181606450463 803167703706272409675695)
          ·
            refine ⟨1204751555559408614513543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 803167703706272409675695 1204751555559408614513543)
            ·
              refine ⟨1807127333339112921770315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1204751555559408614513543 1807127333339112921770315)
              ·
                refine ⟨2710691000008669382655473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1807127333339112921770315 2710691000008669382655473)
                ·
                  refine ⟨2033018250006502036991605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2710691000008669382655473 2033018250006502036991605)
                  ·
                    refine ⟨190595460938109565967963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2033018250006502036991605 190595460938109565967963)
                    ·
                      rfl

theorem cell22_556775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_556775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556775 prefixEnd_556775 := by exact prefixLift 556775
  have htrace : WordTrace (prefixWord ++ tailWord_556775) baseStart_556775 baseEnd_556775 := by
    simpa [prefixWord, tailWord_556775, baseEnd_556775] using wordTrace_append hprefix tailTrace_556775
  have hstable : (prefixWord ++ tailWord_556775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556775).length < 2 ^ (prefixWord ++ tailWord_556775).sum := by decide
  have hdescent : baseEnd_556775 < baseStart_556775 := by decide
  rcases family_descends (prefixWord ++ tailWord_556775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556837 : List Nat := [1, 3, 1, 2, 3, 3, 3, 1, 2, 3]
def baseStart_556837 : Nat := 118140960795 + 556837 * 2 ^ 59
def prefixEnd_556837 : Nat := 4983230072969 + 3 ^ 40 * 556837 * 2
def baseEnd_556837 : Nat := 190616684805162070917773

theorem tailTrace_556837 : CollatzResearch.WordTrace tailWord_556837 prefixEnd_556837 190616684805162070917773 := by
  unfold tailWord_556837
  simp only [CollatzResearch.WordTrace]
  refine ⟨20309513883682124033396765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13539675922454749355597843 20309513883682124033396765)
  ·
    refine ⟨7616067706380796512523787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20309513883682124033396765 7616067706380796512523787)
    ·
      refine ⟨11424101559571194768785681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7616067706380796512523787 11424101559571194768785681)
      ·
        refine ⟨8568076169678396076589261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11424101559571194768785681 8568076169678396076589261)
        ·
          refine ⟨3213028563629398528720973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8568076169678396076589261 3213028563629398528720973)
          ·
            refine ⟨1204885711361024448270365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3213028563629398528720973 1204885711361024448270365)
            ·
              refine ⟨451832141760384168101387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1204885711361024448270365 451832141760384168101387)
              ·
                refine ⟨677748212640576252152081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 451832141760384168101387 677748212640576252152081)
                ·
                  refine ⟨508311159480432189114061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 677748212640576252152081 508311159480432189114061)
                  ·
                    refine ⟨190616684805162070917773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 508311159480432189114061 190616684805162070917773)
                    ·
                      rfl

theorem cell22_556837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 2, 3].length) (baseStart_556837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556837 prefixEnd_556837 := by exact prefixLift 556837
  have htrace : WordTrace (prefixWord ++ tailWord_556837) baseStart_556837 baseEnd_556837 := by
    simpa [prefixWord, tailWord_556837, baseEnd_556837] using wordTrace_append hprefix tailTrace_556837
  have hstable : (prefixWord ++ tailWord_556837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556837).length < 2 ^ (prefixWord ++ tailWord_556837).sum := by decide
  have hdescent : baseEnd_556837 < baseStart_556837 := by decide
  rcases family_descends (prefixWord ++ tailWord_556837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556850 : List Nat := [3, 2, 1, 1, 3, 4, 2, 6]
def baseStart_556850 : Nat := 118140960795 + 556850 * 2 ^ 59
def prefixEnd_556850 : Nat := 4983230072969 + 3 ^ 40 * 556850 * 2
def baseEnd_556850 : Nat := 21180126107870485593637

theorem tailTrace_556850 : CollatzResearch.WordTrace tailWord_556850 prefixEnd_556850 21180126107870485593637 := by
  unfold tailWord_556850
  simp only [CollatzResearch.WordTrace]
  refine ⟨5077497008158756813405001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13539992021756684835746669 5077497008158756813405001)
  ·
    refine ⟨3808122756119067610053751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5077497008158756813405001 3808122756119067610053751)
    ·
      refine ⟨5712184134178601415080627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3808122756119067610053751 5712184134178601415080627)
      ·
        refine ⟨8568276201267902122620941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5712184134178601415080627 8568276201267902122620941)
        ·
          refine ⟨3213103575475463295982853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8568276201267902122620941 3213103575475463295982853)
          ·
            refine ⟨602456920401649367996785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3213103575475463295982853 602456920401649367996785)
            ·
              refine ⟨451842690301237025997589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 602456920401649367996785 451842690301237025997589)
              ·
                refine ⟨21180126107870485593637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 451842690301237025997589 21180126107870485593637)
                ·
                  rfl

theorem cell22_556850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 6].length) (baseStart_556850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556850 prefixEnd_556850 := by exact prefixLift 556850
  have htrace : WordTrace (prefixWord ++ tailWord_556850) baseStart_556850 baseEnd_556850 := by
    simpa [prefixWord, tailWord_556850, baseEnd_556850] using wordTrace_append hprefix tailTrace_556850
  have hstable : (prefixWord ++ tailWord_556850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556850).length < 2 ^ (prefixWord ++ tailWord_556850).sum := by decide
  have hdescent : baseEnd_556850 < baseStart_556850 := by decide
  rcases family_descends (prefixWord ++ tailWord_556850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556882 : List Nat := [3, 2, 2, 1, 1, 5, 1, 1, 3, 3]
def baseStart_556882 : Nat := 118140960795 + 556882 * 2 ^ 59
def prefixEnd_556882 : Nat := 4983230072969 + 3 ^ 40 * 556882 * 2
def baseEnd_556882 : Nat := 190632089224796953542635

theorem tailTrace_556882 : CollatzResearch.WordTrace tailWord_556882 prefixEnd_556882 190632089224796953542635 := by
  unfold tailWord_556882
  simp only [CollatzResearch.WordTrace]
  refine ⟨5077788792129774179696225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13540770112346064479189933 5077788792129774179696225)
  ·
    refine ⟨3808341594097330634772169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5077788792129774179696225 3808341594097330634772169)
    ·
      refine ⟨2856256195572997976079127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3808341594097330634772169 2856256195572997976079127)
      ·
        refine ⟨4284384293359496964118691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2856256195572997976079127 4284384293359496964118691)
        ·
          refine ⟨6426576440039245446178037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4284384293359496964118691 6426576440039245446178037)
          ·
            refine ⟨602491541253679260579191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6426576440039245446178037 602491541253679260579191)
            ·
              refine ⟨903737311880518890868787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 602491541253679260579191 903737311880518890868787)
              ·
                refine ⟨1355605967820778336303181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 903737311880518890868787 1355605967820778336303181)
                ·
                  refine ⟨508352237932791876113693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1355605967820778336303181 508352237932791876113693)
                  ·
                    refine ⟨190632089224796953542635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 508352237932791876113693 190632089224796953542635)
                    ·
                      rfl

theorem cell22_556882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_556882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556882 prefixEnd_556882 := by exact prefixLift 556882
  have htrace : WordTrace (prefixWord ++ tailWord_556882) baseStart_556882 baseEnd_556882 := by
    simpa [prefixWord, tailWord_556882, baseEnd_556882] using wordTrace_append hprefix tailTrace_556882
  have hstable : (prefixWord ++ tailWord_556882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556882).length < 2 ^ (prefixWord ++ tailWord_556882).sum := by decide
  have hdescent : baseEnd_556882 < baseStart_556882 := by decide
  rcases family_descends (prefixWord ++ tailWord_556882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556895 : List Nat := [1, 1, 2, 3, 1, 4, 4, 1, 5]
def baseStart_556895 : Nat := 118140960795 + 556895 * 2 ^ 59
def prefixEnd_556895 : Nat := 4983230072969 + 3 ^ 40 * 556895 * 2
def baseEnd_556895 : Nat := 63545513130156417655865

theorem tailTrace_556895 : CollatzResearch.WordTrace tailWord_556895 prefixEnd_556895 63545513130156417655865 := by
  unfold tailWord_556895
  simp only [CollatzResearch.WordTrace]
  refine ⟨20311629317471999939008139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13541086211647999959338759 20311629317471999939008139)
  ·
    refine ⟨30467443976207999908512209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20311629317471999939008139 30467443976207999908512209)
    ·
      refine ⟨22850582982155999931384157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30467443976207999908512209 22850582982155999931384157)
      ·
        refine ⟨8568968618308499974269059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22850582982155999931384157 8568968618308499974269059)
        ·
          refine ⟨12853452927462749961403589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8568968618308499974269059 12853452927462749961403589)
          ·
            refine ⟨2410022423899265617763173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12853452927462749961403589 2410022423899265617763173)
            ·
              refine ⟨451879204481112303330595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2410022423899265617763173 451879204481112303330595)
              ·
                refine ⟨677818806721668454995893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 451879204481112303330595 677818806721668454995893)
                ·
                  refine ⟨63545513130156417655865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 677818806721668454995893 63545513130156417655865)
                  ·
                    rfl

theorem cell22_556895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 5].length) (baseStart_556895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556895 prefixEnd_556895 := by exact prefixLift 556895
  have htrace : WordTrace (prefixWord ++ tailWord_556895) baseStart_556895 baseEnd_556895 := by
    simpa [prefixWord, tailWord_556895, baseEnd_556895] using wordTrace_append hprefix tailTrace_556895
  have hstable : (prefixWord ++ tailWord_556895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556895).length < 2 ^ (prefixWord ++ tailWord_556895).sum := by decide
  have hdescent : baseEnd_556895 < baseStart_556895 := by decide
  rcases family_descends (prefixWord ++ tailWord_556895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556953 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 4, 4]
def baseStart_556953 : Nat := 118140960795 + 556953 * 2 ^ 59
def prefixEnd_556953 : Nat := 4983230072969 + 3 ^ 40 * 556953 * 2
def baseEnd_556953 : Nat := 190656393975776435017417

theorem tailTrace_556953 : CollatzResearch.WordTrace tailWord_556953 prefixEnd_556953 190656393975776435017417 := by
  unfold tailWord_556953
  simp only [CollatzResearch.WordTrace]
  refine ⟨20313744751261875844619513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13542496500841250563079675 20313744751261875844619513)
  ·
    refine ⟨15235308563446406883464635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20313744751261875844619513 15235308563446406883464635)
    ·
      refine ⟨22852962845169610325196953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15235308563446406883464635 22852962845169610325196953)
      ·
        refine ⟨17139722133877207743897715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22852962845169610325196953 17139722133877207743897715)
        ·
          refine ⟨25709583200815811615846573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17139722133877207743897715 25709583200815811615846573)
          ·
            refine ⟨9641093700305929355942465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25709583200815811615846573 9641093700305929355942465)
            ·
              refine ⟨7230820275229447016956849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9641093700305929355942465 7230820275229447016956849)
              ·
                refine ⟨5423115206422085262717637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7230820275229447016956849 5423115206422085262717637)
                ·
                  refine ⟨1016834101204140986759557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5423115206422085262717637 1016834101204140986759557)
                  ·
                    refine ⟨190656393975776435017417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1016834101204140986759557 190656393975776435017417)
                    ·
                      rfl

theorem cell22_556953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 4].length) (baseStart_556953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556953 prefixEnd_556953 := by exact prefixLift 556953
  have htrace : WordTrace (prefixWord ++ tailWord_556953) baseStart_556953 baseEnd_556953 := by
    simpa [prefixWord, tailWord_556953, baseEnd_556953] using wordTrace_append hprefix tailTrace_556953
  have hstable : (prefixWord ++ tailWord_556953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556953).length < 2 ^ (prefixWord ++ tailWord_556953).sum := by decide
  have hdescent : baseEnd_556953 < baseStart_556953 := by decide
  rcases family_descends (prefixWord ++ tailWord_556953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556989 : List Nat := [1, 4, 1, 2, 3, 3, 1, 2, 2, 3]
def baseStart_556989 : Nat := 118140960795 + 556989 * 2 ^ 59
def prefixEnd_556989 : Nat := 4983230072969 + 3 ^ 40 * 556989 * 2
def baseEnd_556989 : Nat := 190668717511484341117307

theorem tailTrace_556989 : CollatzResearch.WordTrace tailWord_556989 prefixEnd_556989 190668717511484341117307 := by
  unfold tailWord_556989
  simp only [CollatzResearch.WordTrace]
  refine ⟨20315057779131453992930021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13543371852754302661953347 20315057779131453992930021)
  ·
    refine ⟨3809073333587147623674379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20315057779131453992930021 3809073333587147623674379)
    ·
      refine ⟨5713610000380721435511569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3809073333587147623674379 5713610000380721435511569)
      ·
        refine ⟨4285207500285541076633677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5713610000380721435511569 4285207500285541076633677)
        ·
          refine ⟨1606952812607077903737629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4285207500285541076633677 1606952812607077903737629)
          ·
            refine ⟨602607304727654213901611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1606952812607077903737629 602607304727654213901611)
            ·
              refine ⟨903910957091481320852417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 602607304727654213901611 903910957091481320852417)
              ·
                refine ⟨677933217818610990639313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 903910957091481320852417 677933217818610990639313)
                ·
                  refine ⟨508449913363958242979485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 677933217818610990639313 508449913363958242979485)
                  ·
                    refine ⟨190668717511484341117307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 508449913363958242979485 190668717511484341117307)
                    ·
                      rfl

theorem cell22_556989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_556989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_556989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_556989 prefixEnd_556989 := by exact prefixLift 556989
  have htrace : WordTrace (prefixWord ++ tailWord_556989) baseStart_556989 baseEnd_556989 := by
    simpa [prefixWord, tailWord_556989, baseEnd_556989] using wordTrace_append hprefix tailTrace_556989
  have hstable : (prefixWord ++ tailWord_556989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556989).length < 2 ^ (prefixWord ++ tailWord_556989).sum := by decide
  have hdescent : baseEnd_556989 < baseStart_556989 := by decide
  rcases family_descends (prefixWord ++ tailWord_556989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557077 : List Nat := [1, 3, 2, 1, 5, 1, 1, 1, 3, 4]
def baseStart_557077 : Nat := 118140960795 + 557077 * 2 ^ 59
def prefixEnd_557077 : Nat := 4983230072969 + 3 ^ 40 * 557077 * 2
def baseEnd_557077 : Nat := 190698841709881444917037

theorem tailTrace_557077 : CollatzResearch.WordTrace tailWord_557077 prefixEnd_557077 190698841709881444917037 := by
  unfold tailWord_557077
  simp only [CollatzResearch.WordTrace]
  refine ⟨20318267402812645022133485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13545511601875096681422323 20318267402812645022133485)
  ·
    refine ⟨7619350276054741883300057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20318267402812645022133485 7619350276054741883300057)
    ·
      refine ⟨5714512707041056412475043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7619350276054741883300057 5714512707041056412475043)
      ·
        refine ⟨8571769060561584618712565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5714512707041056412475043 8571769060561584618712565)
        ·
          refine ⟨803603349427648558004303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8571769060561584618712565 803603349427648558004303)
          ·
            refine ⟨1205405024141472837006455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 803603349427648558004303 1205405024141472837006455)
            ·
              refine ⟨1808107536212209255509683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1205405024141472837006455 1808107536212209255509683)
              ·
                refine ⟨2712161304318313883264525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1808107536212209255509683 2712161304318313883264525)
                ·
                  refine ⟨1017060489119367706224197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2712161304318313883264525 1017060489119367706224197)
                  ·
                    refine ⟨190698841709881444917037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1017060489119367706224197 190698841709881444917037)
                    ·
                      rfl

theorem cell22_557077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_557077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_557077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_557077 prefixEnd_557077 := by exact prefixLift 557077
  have htrace : WordTrace (prefixWord ++ tailWord_557077) baseStart_557077 baseEnd_557077 := by
    simpa [prefixWord, tailWord_557077, baseEnd_557077] using wordTrace_append hprefix tailTrace_557077
  have hstable : (prefixWord ++ tailWord_557077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557077).length < 2 ^ (prefixWord ++ tailWord_557077).sum := by decide
  have hdescent : baseEnd_557077 < baseStart_557077 := by decide
  rcases family_descends (prefixWord ++ tailWord_557077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557107 : List Nat := [1, 1, 1, 2, 4, 1, 3, 4, 2, 3]
def baseStart_557107 : Nat := 118140960795 + 557107 * 2 ^ 59
def prefixEnd_557107 : Nat := 4983230072969 + 3 ^ 40 * 557107 * 2
def baseEnd_557107 : Nat := 190709111322971366666945

theorem tailTrace_557107 : CollatzResearch.WordTrace tailWord_557107 prefixEnd_557107 190709111322971366666945 := by
  unfold tailWord_557107
  simp only [CollatzResearch.WordTrace]
  refine ⟨20319361592703960145725575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13546241061802640097150383 20319361592703960145725575)
  ·
    refine ⟨30479042389055940218588363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20319361592703960145725575 30479042389055940218588363)
    ·
      refine ⟨45718563583583910327882545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30479042389055940218588363 45718563583583910327882545)
      ·
        refine ⟨34288922687687932745911909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45718563583583910327882545 34288922687687932745911909)
        ·
          refine ⟨6429173003941487389858483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34288922687687932745911909 6429173003941487389858483)
          ·
            refine ⟨9643759505912231084787725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6429173003941487389858483 9643759505912231084787725)
            ·
              refine ⟨3616409814717086656795397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9643759505912231084787725 3616409814717086656795397)
              ·
                refine ⟨678076840259453748149137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3616409814717086656795397 678076840259453748149137)
                ·
                  refine ⟨508557630194590311111853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 678076840259453748149137 508557630194590311111853)
                  ·
                    refine ⟨190709111322971366666945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 508557630194590311111853 190709111322971366666945)
                    ·
                      rfl

theorem cell22_557107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 2, 3].length) (baseStart_557107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_557107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_557107 prefixEnd_557107 := by exact prefixLift 557107
  have htrace : WordTrace (prefixWord ++ tailWord_557107) baseStart_557107 baseEnd_557107 := by
    simpa [prefixWord, tailWord_557107, baseEnd_557107] using wordTrace_append hprefix tailTrace_557107
  have hstable : (prefixWord ++ tailWord_557107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557107).length < 2 ^ (prefixWord ++ tailWord_557107).sum := by decide
  have hdescent : baseEnd_557107 < baseStart_557107 := by decide
  rcases family_descends (prefixWord ++ tailWord_557107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557109 : List Nat := [1, 3, 3, 1, 1, 1, 6, 2, 4]
def baseStart_557109 : Nat := 118140960795 + 557109 * 2 ^ 59
def prefixEnd_557109 : Nat := 4983230072969 + 3 ^ 40 * 557109 * 2
def baseEnd_557109 : Nat := 63569931987948009372313

theorem tailTrace_557109 : CollatzResearch.WordTrace tailWord_557109 prefixEnd_557109 63569931987948009372313 := by
  unfold tailWord_557109
  simp only [CollatzResearch.WordTrace]
  refine ⟨20319434538696714487298381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13546289692464476324865587 20319434538696714487298381)
  ·
    refine ⟨7619787952011267932736893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20319434538696714487298381 7619787952011267932736893)
    ·
      refine ⟨2857420482004225474776335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7619787952011267932736893 2857420482004225474776335)
      ·
        refine ⟨4286130723006338212164503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2857420482004225474776335 4286130723006338212164503)
        ·
          refine ⟨6429196084509507318246755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4286130723006338212164503 6429196084509507318246755)
          ·
            refine ⟨9643794126764260977370133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6429196084509507318246755 9643794126764260977370133)
            ·
              refine ⟨452052849692074733314225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9643794126764260977370133 452052849692074733314225)
              ·
                refine ⟨339039637269056049985669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 452052849692074733314225 339039637269056049985669)
                ·
                  refine ⟨63569931987948009372313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 339039637269056049985669 63569931987948009372313)
                  ·
                    rfl

theorem cell22_557109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 2, 4].length) (baseStart_557109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_557109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_557109 prefixEnd_557109 := by exact prefixLift 557109
  have htrace : WordTrace (prefixWord ++ tailWord_557109) baseStart_557109 baseEnd_557109 := by
    simpa [prefixWord, tailWord_557109, baseEnd_557109] using wordTrace_append hprefix tailTrace_557109
  have hstable : (prefixWord ++ tailWord_557109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557109).length < 2 ^ (prefixWord ++ tailWord_557109).sum := by decide
  have hdescent : baseEnd_557109 < baseStart_557109 := by decide
  rcases family_descends (prefixWord ++ tailWord_557109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557120 : List Nat := [2, 1, 1, 2, 2, 4, 3, 7]
def baseStart_557120 : Nat := 118140960795 + 557120 * 2 ^ 59
def prefixEnd_557120 : Nat := 4983230072969 + 3 ^ 40 * 557120 * 2
def baseEnd_557120 : Nat := 21190395720960407343545

theorem tailTrace_557120 : CollatzResearch.WordTrace tailWord_557120 prefixEnd_557120 21190395720960407343545 := by
  unfold tailWord_557120
  simp only [CollatzResearch.WordTrace]
  refine ⟨10159917870828431682974407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13546557161104575577299209 10159917870828431682974407)
  ·
    refine ⟨15239876806242647524461611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10159917870828431682974407 15239876806242647524461611)
    ·
      refine ⟨22859815209363971286692417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15239876806242647524461611 22859815209363971286692417)
      ·
        refine ⟨17144861407022978465019313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22859815209363971286692417 17144861407022978465019313)
        ·
          refine ⟨12858646055267233848764485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17144861407022978465019313 12858646055267233848764485)
          ·
            refine ⟨2410996135362606346643341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12858646055267233848764485 2410996135362606346643341)
            ·
              refine ⟨904123550760977379991253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2410996135362606346643341 904123550760977379991253)
              ·
                refine ⟨21190395720960407343545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 904123550760977379991253 21190395720960407343545)
                ·
                  rfl

theorem cell22_557120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 7].length) (baseStart_557120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_557120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_557120 prefixEnd_557120 := by exact prefixLift 557120
  have htrace : WordTrace (prefixWord ++ tailWord_557120) baseStart_557120 baseEnd_557120 := by
    simpa [prefixWord, tailWord_557120, baseEnd_557120] using wordTrace_append hprefix tailTrace_557120
  have hstable : (prefixWord ++ tailWord_557120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557120).length < 2 ^ (prefixWord ++ tailWord_557120).sum := by decide
  have hdescent : baseEnd_557120 < baseStart_557120 := by decide
  rcases family_descends (prefixWord ++ tailWord_557120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557169 : List Nat := [1, 2, 2, 2, 1, 1, 3, 6, 1, 3]
def baseStart_557169 : Nat := 118140960795 + 557169 * 2 ^ 59
def prefixEnd_557169 : Nat := 4983230072969 + 3 ^ 40 * 557169 * 2
def baseEnd_557169 : Nat := 190730335190023871616755

theorem tailTrace_557169 : CollatzResearch.WordTrace tailWord_557169 prefixEnd_557169 190730335190023871616755 := by
  unfold tailWord_557169
  simp only [CollatzResearch.WordTrace]
  refine ⟨20321622918479344734482561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13547748612319563156321707 20321622918479344734482561)
  ·
    refine ⟨15241217188859508550861921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20321622918479344734482561 15241217188859508550861921)
    ·
      refine ⟨11430912891644631413146441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15241217188859508550861921 11430912891644631413146441)
      ·
        refine ⟨8573184668733473559859831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11430912891644631413146441 8573184668733473559859831)
        ·
          refine ⟨12859777003100210339789747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8573184668733473559859831 12859777003100210339789747)
          ·
            refine ⟨19289665504650315509684621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12859777003100210339789747 19289665504650315509684621)
            ·
              refine ⟨7233624564243868316131733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19289665504650315509684621 7233624564243868316131733)
              ·
                refine ⟨339076151448931327318675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7233624564243868316131733 339076151448931327318675)
                ·
                  refine ⟨508614227173396990978013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 339076151448931327318675 508614227173396990978013)
                  ·
                    refine ⟨190730335190023871616755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 508614227173396990978013 190730335190023871616755)
                    ·
                      rfl

theorem cell22_557169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 6, 1, 3].length) (baseStart_557169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_557169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_557169 prefixEnd_557169 := by exact prefixLift 557169
  have htrace : WordTrace (prefixWord ++ tailWord_557169) baseStart_557169 baseEnd_557169 := by
    simpa [prefixWord, tailWord_557169, baseEnd_557169] using wordTrace_append hprefix tailTrace_557169
  have hstable : (prefixWord ++ tailWord_557169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557169).length < 2 ^ (prefixWord ++ tailWord_557169).sum := by decide
  have hdescent : baseEnd_557169 < baseStart_557169 := by decide
  rcases family_descends (prefixWord ++ tailWord_557169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557233 : List Nat := [1, 2, 2, 5, 3, 1, 2, 1, 5]
def baseStart_557233 : Nat := 118140960795 + 557233 * 2 ^ 59
def prefixEnd_557233 : Nat := 4983230072969 + 3 ^ 40 * 557233 * 2
def baseEnd_557233 : Nat := 63584081232649679338853

theorem tailTrace_557233 : CollatzResearch.WordTrace tailWord_557233 prefixEnd_557233 63584081232649679338853 := by
  unfold tailWord_557233
  simp only [CollatzResearch.WordTrace]
  refine ⟨20323957190247483664812353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13549304793498322443208235 20323957190247483664812353)
  ·
    refine ⟨15242967892685612748609265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20323957190247483664812353 15242967892685612748609265)
    ·
      refine ⟨11432225919514209561456949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15242967892685612748609265 11432225919514209561456949)
      ·
        refine ⟨1071771179954457146386589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11432225919514209561456949 1071771179954457146386589)
        ·
          refine ⟨401914192482921429894971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1071771179954457146386589 401914192482921429894971)
          ·
            refine ⟨602871288724382144842457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401914192482921429894971 602871288724382144842457)
            ·
              refine ⟨452153466543286608631843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 602871288724382144842457 452153466543286608631843)
              ·
                refine ⟨678230199814929912947765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 452153466543286608631843 678230199814929912947765)
                ·
                  refine ⟨63584081232649679338853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 678230199814929912947765 63584081232649679338853)
                  ·
                    rfl

theorem cell22_557233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 1, 5].length) (baseStart_557233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_557233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_557233 prefixEnd_557233 := by exact prefixLift 557233
  have htrace : WordTrace (prefixWord ++ tailWord_557233) baseStart_557233 baseEnd_557233 := by
    simpa [prefixWord, tailWord_557233, baseEnd_557233] using wordTrace_append hprefix tailTrace_557233
  have hstable : (prefixWord ++ tailWord_557233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557233).length < 2 ^ (prefixWord ++ tailWord_557233).sum := by decide
  have hdescent : baseEnd_557233 < baseStart_557233 := by decide
  rcases family_descends (prefixWord ++ tailWord_557233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557321 : List Nat := [1, 2, 1, 1, 3, 4, 1, 5, 1, 3]
def baseStart_557321 : Nat := 118140960795 + 557321 * 2 ^ 59
def prefixEnd_557321 : Nat := 4983230072969 + 3 ^ 40 * 557321 * 2
def baseEnd_557321 : Nat := 190782367896346141816289

theorem tailTrace_557321 : CollatzResearch.WordTrace tailWord_557321 prefixEnd_557321 190782367896346141816289 := by
  unfold tailWord_557321
  simp only [CollatzResearch.WordTrace]
  refine ⟨20327166813928674694015817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13551444542619116462677211 20327166813928674694015817)
  ·
    refine ⟨15245375110446506020511863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20327166813928674694015817 15245375110446506020511863)
    ·
      refine ⟨22868062665669759030767795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15245375110446506020511863 22868062665669759030767795)
      ·
        refine ⟨34302093998504638546151693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22868062665669759030767795 34302093998504638546151693)
        ·
          refine ⟨12863285249439239454806885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34302093998504638546151693 12863285249439239454806885)
          ·
            refine ⟨2411865984269857397776291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12863285249439239454806885 2411865984269857397776291)
            ·
              refine ⟨3617798976404786096664437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2411865984269857397776291 3617798976404786096664437)
              ·
                refine ⟨339168654037948696562291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3617798976404786096664437 339168654037948696562291)
                ·
                  refine ⟨508752981056923044843437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 339168654037948696562291 508752981056923044843437)
                  ·
                    refine ⟨190782367896346141816289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 508752981056923044843437 190782367896346141816289)
                    ·
                      rfl

theorem cell22_557321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 5, 1, 3].length) (baseStart_557321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_557321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_557321 prefixEnd_557321 := by exact prefixLift 557321
  have htrace : WordTrace (prefixWord ++ tailWord_557321) baseStart_557321 baseEnd_557321 := by
    simpa [prefixWord, tailWord_557321, baseEnd_557321] using wordTrace_append hprefix tailTrace_557321
  have hstable : (prefixWord ++ tailWord_557321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557321).length < 2 ^ (prefixWord ++ tailWord_557321).sum := by decide
  have hdescent : baseEnd_557321 < baseStart_557321 := by decide
  rcases family_descends (prefixWord ++ tailWord_557321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557396 : List Nat := [2, 4, 1, 1, 2, 4, 1, 1, 6]
def baseStart_557396 : Nat := 118140960795 + 557396 * 2 ^ 59
def prefixEnd_557396 : Nat := 4983230072969 + 3 ^ 40 * 557396 * 2
def baseEnd_557396 : Nat := 63602680643023648730353

theorem tailTrace_557396 : CollatzResearch.WordTrace tailWord_557396 prefixEnd_557396 63602680643023648730353 := by
  unfold tailWord_557396
  simp only [CollatzResearch.WordTrace]
  refine ⟨10164951144328481251498021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13553268192437975001997361 10164951144328481251498021)
  ·
    refine ⟨1905928339561590234655879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10164951144328481251498021 1905928339561590234655879)
    ·
      refine ⟨2858892509342385351983819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1905928339561590234655879 2858892509342385351983819)
      ·
        refine ⟨4288338764013578027975729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2858892509342385351983819 4288338764013578027975729)
        ·
          refine ⟨3216254073010183520981797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4288338764013578027975729 3216254073010183520981797)
          ·
            refine ⟨603047638689409410184087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3216254073010183520981797 603047638689409410184087)
            ·
              refine ⟨904571458034114115276131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 603047638689409410184087 904571458034114115276131)
              ·
                refine ⟨1356857187051171172914197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 904571458034114115276131 1356857187051171172914197)
                ·
                  refine ⟨63602680643023648730353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1356857187051171172914197 63602680643023648730353)
                  ·
                    rfl

theorem cell22_557396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_557396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_557396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_557396 prefixEnd_557396 := by exact prefixLift 557396
  have htrace : WordTrace (prefixWord ++ tailWord_557396) baseStart_557396 baseEnd_557396 := by
    simpa [prefixWord, tailWord_557396, baseEnd_557396] using wordTrace_append hprefix tailTrace_557396
  have hstable : (prefixWord ++ tailWord_557396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557396).length < 2 ^ (prefixWord ++ tailWord_557396).sum := by decide
  have hdescent : baseEnd_557396 < baseStart_557396 := by decide
  rcases family_descends (prefixWord ++ tailWord_557396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557407 : List Nat := [1, 1, 2, 3, 1, 2, 3, 9]
def baseStart_557407 : Nat := 118140960795 + 557407 * 2 ^ 59
def prefixEnd_557407 : Nat := 4983230072969 + 3 ^ 40 * 557407 * 2
def baseEnd_557407 : Nat := 21201311939318953796225

theorem tailTrace_557407 : CollatzResearch.WordTrace tailWord_557407 prefixEnd_557407 21201311939318953796225 := by
  unfold tailWord_557407
  simp only [CollatzResearch.WordTrace]
  refine ⟨20330303491617111381646475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13553535661078074254430983 20330303491617111381646475)
  ·
    refine ⟨30495455237425667072469713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20330303491617111381646475 30495455237425667072469713)
    ·
      refine ⟨22871591428069250304352285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30495455237425667072469713 22871591428069250304352285)
      ·
        refine ⟨8576846785525968864132107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22871591428069250304352285 8576846785525968864132107)
        ·
          refine ⟨12865270178288953296198161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8576846785525968864132107 12865270178288953296198161)
          ·
            refine ⟨9648952633716714972148621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12865270178288953296198161 9648952633716714972148621)
            ·
              refine ⟨3618357237643768114555733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9648952633716714972148621 3618357237643768114555733)
              ·
                refine ⟨21201311939318953796225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3618357237643768114555733 21201311939318953796225)
                ·
                  rfl

theorem cell22_557407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 9].length) (baseStart_557407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_557407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_557407 prefixEnd_557407 := by exact prefixLift 557407
  have htrace : WordTrace (prefixWord ++ tailWord_557407) baseStart_557407 baseEnd_557407 := by
    simpa [prefixWord, tailWord_557407, baseEnd_557407] using wordTrace_append hprefix tailTrace_557407
  have hstable : (prefixWord ++ tailWord_557407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557407).length < 2 ^ (prefixWord ++ tailWord_557407).sum := by decide
  have hdescent : baseEnd_557407 < baseStart_557407 := by decide
  rcases family_descends (prefixWord ++ tailWord_557407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557411 : List Nat := [1, 1, 1, 5, 2, 1, 3, 3, 2, 3]
def baseStart_557411 : Nat := 118140960795 + 557411 * 2 ^ 59
def prefixEnd_557411 : Nat := 4983230072969 + 3 ^ 40 * 557411 * 2
def baseEnd_557411 : Nat := 190813176735615907066013

theorem tailTrace_557411 : CollatzResearch.WordTrace tailWord_557411 prefixEnd_557411 190813176735615907066013 := by
  unfold tailWord_557411
  simp only [CollatzResearch.WordTrace]
  refine ⟨20330449383602620064792087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13553632922401746709861391 20330449383602620064792087)
  ·
    refine ⟨30495674075403930097188131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20330449383602620064792087 30495674075403930097188131)
    ·
      refine ⟨45743511113105895145782197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30495674075403930097188131 45743511113105895145782197)
      ·
        refine ⟨4288454166853677669917081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45743511113105895145782197 4288454166853677669917081)
        ·
          refine ⟨3216340625140258252437811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4288454166853677669917081 3216340625140258252437811)
          ·
            refine ⟨4824510937710387378656717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3216340625140258252437811 4824510937710387378656717)
            ·
              refine ⟨1809191601641395266996269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4824510937710387378656717 1809191601641395266996269)
              ·
                refine ⟨678446850615523225123601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1809191601641395266996269 678446850615523225123601)
                ·
                  refine ⟨508835137961642418842701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 678446850615523225123601 508835137961642418842701)
                  ·
                    refine ⟨190813176735615907066013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 508835137961642418842701 190813176735615907066013)
                    ·
                      rfl

theorem cell22_557411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 2, 3].length) (baseStart_557411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_557411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_557411 prefixEnd_557411 := by exact prefixLift 557411
  have htrace : WordTrace (prefixWord ++ tailWord_557411) baseStart_557411 baseEnd_557411 := by
    simpa [prefixWord, tailWord_557411, baseEnd_557411] using wordTrace_append hprefix tailTrace_557411
  have hstable : (prefixWord ++ tailWord_557411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557411).length < 2 ^ (prefixWord ++ tailWord_557411).sum := by decide
  have hdescent : baseEnd_557411 < baseStart_557411 := by decide
  rcases family_descends (prefixWord ++ tailWord_557411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_557426 : List Nat := [3, 2, 1, 2, 1, 4, 2, 1, 2, 4]
def baseStart_557426 : Nat := 118140960795 + 557426 * 2 ^ 59
def prefixEnd_557426 : Nat := 4983230072969 + 3 ^ 40 * 557426 * 2
def baseEnd_557426 : Nat := 190818311542160867940967

theorem tailTrace_557426 : CollatzResearch.WordTrace tailWord_557426 prefixEnd_557426 190818311542160867940967 := by
  unfold tailWord_557426
  simp only [CollatzResearch.WordTrace]
  refine ⟨5082749119637069406647033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13553997652365518417725421 5082749119637069406647033)
  ·
    refine ⟨3812061839727802054985275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5082749119637069406647033 3812061839727802054985275)
    ·
      refine ⟨5718092759591703082477913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3812061839727802054985275 5718092759591703082477913)
      ·
        refine ⟨4288569569693777311858435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5718092759591703082477913 4288569569693777311858435)
        ·
          refine ⟨6432854354540665967787653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4288569569693777311858435 6432854354540665967787653)
          ·
            refine ⟨1206160191476374868960185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6432854354540665967787653 1206160191476374868960185)
            ·
              refine ⟨904620143607281151720139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1206160191476374868960185 904620143607281151720139)
              ·
                refine ⟨1356930215410921727580209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 904620143607281151720139 1356930215410921727580209)
                ·
                  refine ⟨1017697661558191295685157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1356930215410921727580209 1017697661558191295685157)
                  ·
                    refine ⟨190818311542160867940967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1017697661558191295685157 190818311542160867940967)
                    ·
                      rfl

theorem cell22_557426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_557426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_557426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_557426 prefixEnd_557426 := by exact prefixLift 557426
  have htrace : WordTrace (prefixWord ++ tailWord_557426) baseStart_557426 baseEnd_557426 := by
    simpa [prefixWord, tailWord_557426, baseEnd_557426] using wordTrace_append hprefix tailTrace_557426
  have hstable : (prefixWord ++ tailWord_557426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_557426).length < 2 ^ (prefixWord ++ tailWord_557426).sum := by decide
  have hdescent : baseEnd_557426 < baseStart_557426 := by decide
  rcases family_descends (prefixWord ++ tailWord_557426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
